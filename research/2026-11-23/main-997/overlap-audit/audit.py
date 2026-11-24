#!/usr/bin/env python3
"""Exhaustive seven-input audit of partial-support overlap versus whole refunds.

No SAT, Lean, network, or private task-state access is used. All gate indices
in reports are zero-based; wire n+g is the output of gate g.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
N = 7
Y = (1 << 0) | (1 << 1) | (1 << 2)
TARGETS = [(1 << 0) | (1 << 3) | (1 << 4),
           (1 << 3) | (1 << 5) | (1 << 6)]


def vertices(mask):
    return [p for p in range(N) if mask >> p & 1]


def build(duplicates):
    gates = []

    def gate(op, *inputs):
        gates.append({"op": op, "inputs": list(inputs)})
        return N + len(gates) - 1

    y01 = gate("and", 0, 1)
    h = gate("and", y01, 2)
    z = gate("not", h)
    bz = gate("and", 4, z)
    cy0 = gate("and", 5, 0)
    ab = gate("or", 3, bz)
    g = gate("or", ab, cy0)
    last = g
    for _ in range(duplicates):
        last = gate("or", last, last)
    light = gate("or", last, 0)
    ac = gate("or", 3, 5)
    heavy = gate("or", ac, 6)
    return {"n": N, "sets": TARGETS, "y": Y, "not_gate": z - N,
            "gates": gates, "outputs": [light, heavy],
            "named_gates": {"h": h - N, "z": z - N, "bz": bz - N,
                            "cy0": cy0 - N, "ab": ab - N, "g": g - N,
                            "light_output": light - N, "ac": ac - N,
                            "heavy_output": heavy - N},
            "duplicate_count": duplicates}


def evaluate(case, row):
    wires = [bool(row >> p & 1) for p in range(N)]
    for gate in case["gates"]:
        args = [wires[w] if 0 <= w < len(wires) else False for w in gate["inputs"]]
        if gate["op"] == "and":
            value = all(args)
        elif gate["op"] == "or":
            value = any(args)
        elif gate["op"] == "not":
            value = not (args[0] if args else False)
        else:
            raise AssertionError("unexpected operation")
        wires.append(value)
    return wires


def live_gates(case):
    pending = list(case["outputs"])
    live = set()
    while pending:
        wire = pending.pop()
        if wire < N:
            continue
        j = wire - N
        if j in live:
            continue
        live.add(j)
        pending += [w for w in case["gates"][j]["inputs"] if w < wire]
    return live


def audit(case):
    gates = case["gates"]
    size = len(gates)
    k = Y.bit_count()
    dup = case["duplicate_count"]
    assert (TARGETS[0] & TARGETS[1]).bit_count() == 1
    assert TARGETS[0] & Y and not (TARGETS[1] & Y)
    assert all(g["op"] in {"and", "or", "not"} and len(g["inputs"]) <= 2 for g in gates)
    assert [i for i, g in enumerate(gates) if g["op"] == "not"] == [case["not_gate"]]
    vectors = [0] * size
    low_rows = 0
    for row in range(1 << N):
        wires = evaluate(case, row)
        for i, out in enumerate(case["outputs"]):
            assert wires[out] == bool(row & TARGETS[i])
        if row.bit_count() < k:
            low_rows += 1
            assert wires[N + case["not_gate"]]
        assert wires[N + case["named_gates"]["h"]] == (row & Y == Y)
        for j in range(size):
            if wires[N + j]:
                vectors[j] |= 1 << row
    assert not evaluate(case, Y)[N + case["not_gate"]]
    assert low_rows == 29
    assert live_gates(case) == set(range(size))

    unit = [evaluate(case, 1 << p)[N:] for p in range(N)]
    shifted = [evaluate(case, Y | (1 << p))[N:] for p in range(N)]
    single = [sum(1 << p for p in range(N) if unit[p][j]) for j in range(size)]
    outside = [sum(1 << p for p in range(N) if not (Y >> p & 1) and shifted[p][j])
               for j in range(size)]
    heavy_indices = [i for i, S in enumerate(TARGETS) if not (S & Y)]
    light_indices = [i for i, S in enumerate(TARGETS) if S & Y]
    light = {i: [j for j in range(size)
                 if single[j].bit_count() >= 2 and single[j] & ~TARGETS[i] == 0]
             for i in light_indices}
    heavy = {i: [j for j in range(size)
                 if outside[j].bit_count() >= 2 and outside[j] & ~TARGETS[i] == 0]
             for i in heavy_indices}

    # This is exactly the posted two-existential refund predicate. The second
    # equivalence is guarded by p notin Y; points in Y impose no condition.
    refund = [j for j in range(size)
              if any(all(unit[p][j] == bool(S >> p & 1) for p in range(N))
                     for S in TARGETS)
              and any(all(shifted[p][j] == bool(TARGETS[i] >> p & 1)
                          for p in range(N) if not (Y >> p & 1))
                      for i in heavy_indices)]
    assert refund == [9 + dup]
    assert single[case["named_gates"]["g"]] == (1 << 3) | (1 << 4)
    assert outside[case["named_gates"]["g"]] == (1 << 3) | (1 << 5)

    per_set = []
    for i in range(len(TARGETS)):
        kind = "light" if i in light else "heavy"
        assigned = light[i] if kind == "light" else heavy[i]
        demand = min(k, TARGETS[i].bit_count()) if kind == "light" else TARGETS[i].bit_count()
        assert demand <= len(assigned) + 1
        per_set.append({"target": i, "kind": kind, "vertices": vertices(TARGETS[i]),
                        "weighted_demand": demand, "minimum_gate_quota": max(demand - 1, 0),
                        "all_eligible_gates": assigned, "eligible_count": len(assigned),
                        "posted_per_set_count_holds": True})
    L = set(light[0])
    H = set(heavy[1])
    intersection = L & H
    union = L | H
    assert intersection == set(range(6, 7 + dup))
    assert not intersection.intersection(refund)
    selected_light = {5, 7 + dup}
    selected_heavy = {8 + dup, 9 + dup}
    assert selected_light <= L and selected_heavy <= H
    assert len(selected_light) == len(selected_heavy) == 2
    assert selected_light.isdisjoint(selected_heavy)
    lhs = sum(x["weighted_demand"] for x in per_set)
    rhs = size + len(refund) + len(TARGETS)
    assert lhs == 6 and rhs == 13 + dup and lhs <= rhs
    return {"duplicates": dup, "n": N, "m": len(TARGETS), "k": k,
            "gate_count": size, "all_gates_live": True,
            "truth_rows_checked": 1 << N, "output_values_checked": (1 << N) * len(TARGETS),
            "low_weight_rows_checked": low_rows, "all_posted_hypotheses_checked": True,
            "per_set_counts": per_set, "refund_gates": refund, "refund_count": len(refund),
            "partial_overlap_gates": sorted(intersection), "partial_overlap_count": len(intersection),
            "every_overlap_is_nonrefunded": True,
            "overlap_count_le_refund_count": len(intersection) <= len(refund),
            "eligible_union_count": len(union), "total_eligible_memberships": len(L) + len(H),
            "total_eligible_memberships_le_gates_plus_refunds": len(L) + len(H) <= size + len(refund),
            "selected_light_gates": sorted(selected_light), "selected_heavy_gates": sorted(selected_heavy),
            "selected_quotas_have_zero_overlap": True,
            "weighted_lhs": lhs, "exact_refund_rhs": rhs, "exact_997_holds": True,
            "gate_supports": [{"gate": j, "singleton": vertices(single[j]),
                               "shifted_outside": vertices(outside[j]),
                               "whole_refund": j in refund,
                               "truth_vector_sha256": hashlib.sha256(vectors[j].to_bytes(16, "little")).hexdigest()}
                              for j in range(size)]}


def main():
    cases = [build(d) for d in [0, 1, 6, 10]]
    results = [audit(c) for c in cases]
    case_bytes = (json.dumps(cases, indent=2) + "\n").encode()
    (HERE / "circuits.json").write_bytes(case_bytes)
    record = {"status": "EXHAUSTIVE_DATA_AUDIT_PASS", "solver_used": False,
              "lean_checked": False,
              "scope": "All original circuit/window/output and proposed per-set hypotheses are exhaustively checked. The examples refute overlap-implies-refund and raw-class cardinality shortcuts, while satisfying the exact 997 conclusion.",
              "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "circuits_sha256": hashlib.sha256(case_bytes).hexdigest(), "variants": results}
    (HERE / "results.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"status": record["status"], "variants": [
        {k: r[k] for k in ["duplicates", "gate_count", "partial_overlap_count", "refund_count",
                           "total_eligible_memberships", "weighted_lhs", "exact_refund_rhs"]}
        for r in results]}, indent=2))


if __name__ == "__main__":
    main()
