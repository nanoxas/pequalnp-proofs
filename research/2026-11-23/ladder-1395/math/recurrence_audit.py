"""Audit the public few-NOT recurrence using two independent exact algorithms.

The slow algorithm evaluates its posted max/min recursion directly. The fast
algorithm uses consecutive leaf intervals and greedily chooses the smallest
width that attains a proposed payoff. It is an executable research aid, not a
Lean certificate or a claim that the public desk assigned a search shard.

Source: https://github.com/brilliant-hq/pequalnp-proofs/pull/2852
The accepted lower-bound proof belongs to that PR's contributor, stierms.
"""

from functools import cache
from pathlib import Path
import argparse
import json


def base(q: int, b: int, k: int) -> int:
    n = q * q + q + 1
    deleted = 0 if b == 0 else min(n, b * q + 1)
    return (n - deleted) * min(k, q)


def direct_recurrence(q: int):
    @cache
    def value(s: int, b: int, k: int) -> int:
        if s == 0:
            return base(q, b, k)
        return max(
            min(value(s - 1, b + j, k - j), value(s - 1, b, j))
            for j in range(k + 1)
        )

    return value


def feasible(q: int, s: int, b: int, k: int, payoff: int) -> bool:
    if payoff == 0:
        return True
    leaves = 1 << s
    if leaves > k or b + leaves > q + 1:
        return False
    n = q * q + q + 1
    for _ in range(leaves - 1):
        coefficient = n if b == 0 else max(0, n - (b * q + 1))
        if coefficient == 0:
            return False
        width = (payoff + coefficient - 1) // coefficient
        if width > q or width > k:
            return False
        b += width
        k -= width
    return payoff <= base(q, b, k)


def greedy_value(q: int, s: int, b: int, k: int) -> int:
    lo, hi = 0, base(q, b, k) + 1
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if feasible(q, s, b, k, mid):
            lo = mid
        else:
            hi = mid
    return lo


def public_lower_bound(q: int, s: int) -> int:
    return q * (q * max(0, q + 1 - (1 << s)) // (1 << (s + 1)))


def audit(q_max: int) -> dict:
    comparisons = 0
    mismatches = []
    threshold_mismatches = []
    for q in range(2, q_max + 1):
        direct = direct_recurrence(q)
        for s in range((q + 1).bit_length() + 1):
            for b in range(q + 3):
                for k in range(q + 4):
                    actual = direct(s, b, k)
                    fast = greedy_value(q, s, b, k)
                    expected_positive = (1 << s) <= k and b + (1 << s) <= q + 1
                    comparisons += 1
                    if actual != fast:
                        mismatches.append([q, s, b, k, actual, fast])
                    if (actual > 0) != expected_positive:
                        threshold_mismatches.append([q, s, b, k, actual])
    examples = []
    for q in [2, 3, 4, 7, 8, 16, 31, 64, 127]:
        n = q * q + q + 1
        for s in range((q + 1).bit_length() + 1):
            exact = greedy_value(q, s, 0, n)
            bound = public_lower_bound(q, s)
            examples.append({"q": q, "s": s, "exact_g": exact, "checked_bound": bound})
            assert bound <= exact
    return {
        "scope": "Independent finite audit; no assigned shard exhaustion or new accepted proof.",
        "source": "https://github.com/brilliant-hq/pequalnp-proofs/pull/2852",
        "q_max_for_direct_comparison": q_max,
        "states_compared": comparisons,
        "algorithm_mismatches": mismatches,
        "positivity_threshold_mismatches": threshold_mismatches,
        "positivity_conjecture": "G(s,b,K)>0 iff 2**s<=K and b+2**s<=q+1, for q>=2",
        "examples": examples,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-max", type=int, default=12)
    parser.add_argument("--output", type=Path, default=Path("recurrence-audit.json"))
    args = parser.parse_args()
    result = audit(args.q_max)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "examples"}, indent=2))
