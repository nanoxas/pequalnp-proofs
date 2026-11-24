#!/usr/bin/env python3
"""Independent executable audit of the accepted L-meta-1445 search.

The accepted Lean source is authoritative. This Python port creates inputs and
estimates evaluation work; its results alone are not Lean proof certificates.
The optimized evaluator follows the Lean list order and saturating subtraction.
A separate reference evaluator omits the coverage-count and tight-frontier
shortcuts and recomputes coverage from each candidate frontier.
"""
from __future__ import annotations

import functools
import itertools
import time

TOP = (1 << 256) - 1
ZERO = (0, 0)
ONE = (TOP, TOP)
TARGET = (TOP, 0)


def sep(d, a):
    return a[0] ^ a[1] if d else a[0] & (TOP ^ a[1])


def union_sep(d, v):
    ans = 0
    for a in v:
        ans |= sep(d, a)
    return ans


def coverage(d, v):
    c0 = c1 = c2 = 0
    for a in reversed(v):
        z = sep(d, a)
        c0, c1, c2 = z | c0, (z & (TOP ^ c0)) | (c1 & (TOP ^ z)), (z & c1) | (c2 & (TOP ^ z))
    return c0, c1, c2


def take_one(c, a):
    return c[0] & (TOP ^ (c[1] & a))


def take_two(c, a, b):
    return c[0] & (TOP ^ ((c[1] & (a | b)) | (c[2] & (a & b))))


def neg(a):
    return TOP ^ a[0], TOP ^ a[1]


def binary(is_or, a, b):
    return (a[0] | b[0], a[1] | b[1]) if is_or else (a[0] & b[0], a[1] & b[1])


class SearchLimit(RuntimeError):
    pass


class Evaluator:
    """Return (search result, exact unrolled search-call count).

    Cached results include subtree call counts, so a cache hit still contributes
    its entire recursive expansion to the returned logical cost. The cost counts
    calls to `search`, not arithmetic/list reductions in the Lean kernel.
    """
    def __init__(self, reference=False, cache_size=100_000, seconds=120, max_states=2_000_000):
        self.reference = reference
        self.deadline = time.monotonic() + seconds
        self.max_states = max_states
        self.visits = 0
        self.started = time.monotonic()
        self.search = functools.lru_cache(maxsize=cache_size)(self._search)

    def _search(self, budget, t, v):
        self.visits += 1
        if self.visits > self.max_states:
            raise SearchLimit("computed-state budget reached")
        if (self.visits == 1 or self.visits % 1024 == 0) and time.monotonic() > self.deadline:
            raise SearchLimit("time budget reached")
        work = 1
        if budget == 0:
            return v == (TARGET,), work
        k = budget - 1
        if t > k + 1 or len(v) > max(0, k + 1 - t) + 1:
            return False, work
        if v == (TARGET,):
            return True, work

        def recurse(next_t, state):
            nonlocal work
            answer, calls = self.search(k, next_t, state)
            work += calls
            return answer

        def available(g):
            return g not in v and g != ZERO and g != ONE

        def try_gate(next_t, rest, n, cov, g, keeps):
            d = next_t > 0
            base = sep(d, g) | cov
            if n == max(0, k - next_t):
                return base == TOP and available(g) and recurse(next_t, (g,) + rest)
            for h in keeps:
                if n + len(h) + 1 <= max(0, k - next_t) + 1 and base | union_sep(d, h) == TOP and available(g):
                    if recurse(next_t, (g,) + h + rest):
                        return True
            return False

        if t > 0:
            next_t = t - 1
            c = coverage(next_t > 0, v)
            for a in v:
                rest = tuple(x for x in v if x != a)
                mask = union_sep(next_t > 0, rest) if self.reference else take_one(c, sep(next_t > 0, a))
                if try_gate(next_t, rest, len(v) - 1, mask, neg(a), ((), (a,))):
                    return True, work

        d = t > 0
        c = coverage(d, v)
        fast = not self.reference and t == 0 and len(v) == k + 2
        for i, a in enumerate(v):
            for b in v[i+1:]:
                rest = tuple(x for x in v if x != a and x != b)
                if fast:
                    ua = c[1] & sep(False, a)
                    ub = c[1] & sep(False, b)
                    g = binary(False, a, b)
                    if ua & (TOP ^ b[0]) == 0 and ub & (TOP ^ a[0]) == 0 and available(g):
                        if recurse(t, (g,) + rest):
                            return True, work
                    g = binary(True, a, b)
                    if ua & b[1] == 0 and ub & a[1] == 0 and available(g):
                        if recurse(t, (g,) + rest):
                            return True, work
                else:
                    mask = union_sep(d, rest) if self.reference else take_two(c, sep(d, a), sep(d, b))
                    for is_or in (False, True):
                        if try_gate(t, rest, len(v) - 2, mask, binary(is_or, a, b), ((), (a,), (b,), (a,b))):
                            return True, work
        return False, work

    def run(self, budget, t, v):
        try:
            result, calls = self.search(budget, t, tuple(v))
            record = {"status": "COMPLETE", "result": result, "unrolled_search_calls": calls}
        except (SearchLimit, RecursionError, MemoryError) as exc:
            record = {"status": "UNKNOWN", "reason": str(exc) or type(exc).__name__}
        record.update({"seconds": time.monotonic() - self.started, "computed_states": self.visits,
                       "cache": self.search.cache_info()._asdict(), "reference": self.reference})
        return record


def make_raw(table, n=5):
    positive = [x for x in range(1 << n) if table >> x & 1]
    negative = [x for x in range(1 << n) if not table >> x & 1]
    pairs = list(itertools.product(positive, negative))
    assert pairs and len(pairs) <= 256
    pairs = [pairs[j % len(pairs)] for j in range(256)]
    raw = tuple((sum(((a >> i) & 1) << j for j, (a,b) in enumerate(pairs)),
                 sum(((b >> i) & 1) << j for j, (a,b) in enumerate(pairs))) for i in range(n))
    return raw


def sample(raw, side, index):
    return sum(((a[0 if side else 1] >> index) & 1) << j for j, a in enumerate(raw))


def audit_raw(table, raw, n=5):
    samples = all(((table >> sample(raw, b, i)) & 1) == b for b in (0,1) for i in range(256))
    essential = [union_sep(True, raw[:j] + raw[j+1:]) != TOP for j in range(len(raw))]
    return {"length": len(raw), "nodup": len(set(raw)) == len(raw), "samples_correct": samples,
            "essential_inputs": essential, "separates_all": union_sep(False, raw) == TOP,
            "distinct_positive_rows": len({sample(raw, True, i) for i in range(256)}),
            "distinct_negative_rows": len({sample(raw, False, i) for i in range(256)})}

