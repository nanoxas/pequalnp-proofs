"""Exact semantic OR-budget search for globally clean monotone circuits.

An AND is clean when it is false on every independent input.  Every wire is
represented by (raw singleton support, accepted edge inputs).  OR is union;
clean AND is intersection and has empty singleton support.  AND gates are free
in this search.  A clean operand dominates the output of any AND using it, so
only pairs of dirty wires need be considered for free AND closure.

This is a mathematical diagnostic, not a Lean certificate or project submission.
"""
from __future__ import annotations

import argparse
import itertools
import json
import time


def solve(n, edges, budget, state_cap=300000):
    m = len(edges)
    target = (1 << m) - 1
    neighbors = [0] * n
    incident = [0] * n
    for i, (a, b) in enumerate(edges):
        neighbors[a] |= 1 << b
        neighbors[b] |= 1 << a
        incident[a] |= 1 << i
        incident[b] |= 1 << i

    def compatible(a, b):
        if not a or not b or a & b:
            return False
        return all(b & ~neighbors[v] == 0 for v in range(n) if a >> v & 1)

    def usable(a):
        return any(a & ~nb == 0 for nb in neighbors)

    def maximal_clean(clean):
        vals = sorted(set(clean), key=lambda v: (-v.bit_count(), v))
        result = []
        for x in vals:
            if x and not any(x & ~y == 0 for y in result):
                result.append(x)
        return tuple(sorted(result))

    def close(dirty, clean):
        vals = sorted(set(dirty), key=lambda p: (p[0], -p[1].bit_count(), p[1]))
        kept = []
        for s, e in vals:
            if not any(s == t and e & ~f == 0 for t, f in kept):
                kept.append((s, e))
        for i, (s, e) in enumerate(kept):
            for t, f in kept[:i]:
                if compatible(s, t):
                    clean.append(e & f)
        return (tuple(sorted(kept)), maximal_clean(clean))

    start = close([(1 << v, incident[v]) for v in range(n)], [])
    frontier = {start: []}
    seen = {start}
    statistics = []
    started = time.monotonic()
    if target in start[1]:
        return {"result": "SAT", "or_count": 0, "path": []}
    for level in range(1, budget + 1):
        next_frontier = {}
        for (dirty, clean), path in frontier.items():
            wires = list(dirty) + [(0, e) for e in clean]
            for i, (s, e) in enumerate(wires):
                for t, f in wires[:i]:
                    u, g = s | t, e | f
                    if u:
                        if not usable(u):
                            continue
                        if any(u == v and g & ~h == 0 for v, h in dirty):
                            continue
                        candidate = close(list(dirty) + [(u, g)], list(clean))
                    else:
                        if any(g & ~h == 0 for h in clean):
                            continue
                        candidate = (dirty, maximal_clean(list(clean) + [g]))
                    if target in candidate[1]:
                        return {"result": "SAT", "or_count": level,
                                "path": path + [((s, e), (t, f))],
                                "statistics": statistics,
                                "seconds": time.monotonic() - started}
                    if candidate in seen:
                        continue
                    seen.add(candidate)
                    next_frontier[candidate] = path + [((s, e), (t, f))]
                    if len(seen) > state_cap:
                        return {"result": "UNKNOWN_state_cap", "level": level,
                                "statistics": statistics, "states": len(seen),
                                "seconds": time.monotonic() - started}
        statistics.append({"level": level, "new_states": len(next_frontier),
                           "total_states": len(seen)})
        frontier = next_frontier
        if not frontier:
            break
    return {"result": "UNSAT_semantic_search", "budget": budget,
            "statistics": statistics, "seconds": time.monotonic() - started}


def canonical(n, edges):
    return min(tuple(sorted(tuple(sorted((p[a], p[b]))) for a, b in edges))
               for p in itertools.permutations(range(n)))


def has_c4(n, edges):
    E = {frozenset(e) for e in edges}
    return any(all(frozenset((p[i], p[(i + 1) % 4])) in E for i in range(4))
               for p in itertools.permutations(range(n), 4))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--cap", type=int, default=300000)
    parser.add_argument("--case", choices=["n4", "c5", "c6", "path4"], default="n4")
    args = parser.parse_args()
    if args.case == "n4":
        n = 4
        universe = list(itertools.combinations(range(n), 2))
        cases = sorted({canonical(n, [e for i, e in enumerate(universe) if mask >> i & 1])
                        for mask in range(1 << len(universe))
                        if not has_c4(n, [e for i, e in enumerate(universe) if mask >> i & 1])})
    elif args.case == "path4":
        n, cases = 4, [((0, 1), (1, 2), (2, 3))]
    else:
        n = int(args.case[1:])
        cases = [tuple((i, (i + 1) % n) for i in range(n))]
    for edges in cases:
        if len(edges) < 2:
            continue
        result = solve(n, edges, len(edges) - 2, args.cap)
        print(json.dumps({"n": n, "edges": edges, **result}), flush=True)
