#!/usr/bin/env python3
"""Construct the requested13-input family and audit its complete OR baseline.

No solver or network operation is used. Exact data are compatible with
main-997/search.py --case-file. This is data verification, not a997 proof.
"""
from __future__ import annotations
import hashlib
import itertools
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
N = 13
Y = [0, 1, 2]
SETS = [list(range(3,11)), [0,3,11], [1,4,11], [2,5,11],
        [0,6,12], [1,7,12], [2,8,12], [0,1,9], [0,2,10], [1,2,3]]


def mask(vertices):
    return sum(1 << v for v in vertices)


def main():
    y, sets = mask(Y), [mask(s) for s in SETS]
    assert all(0 <= v < N for s in SETS for v in s)
    intersections = []
    for i, j in itertools.combinations(range(len(SETS)), 2):
        inter = sorted(set(SETS[i]) & set(SETS[j]))
        assert len(inter) <= 1
        intersections.append({"i": i, "j": j, "intersection": inter})
    case = {"name": "linear13_one_heavy8_nine_triples", "n": N,
            "sets": sets, "y": y, "gate_bounds": [23]}
    (HERE / "case.json").write_text(json.dumps(case, indent=2)+"\n")
    gates = [{"op":"and", "inputs":[0,1]},
             {"op":"and", "inputs":[2,N]},
             {"op":"not", "inputs":[N+1]}]
    outputs = []
    for S in SETS:
        wire = S[0]
        for v in S[1:]:
            gates.append({"op":"or", "inputs":[wire,v]})
            wire = N+len(gates)-1
        outputs.append(wire)
    baseline = {"gates": gates, "outputs": outputs}
    (HERE / "baseline.json").write_text(json.dumps(baseline, indent=2)+"\n")

    # Independent scalar evaluator using actual-index list semantics.
    vectors = [bytearray((1 << N)//8) for _ in SETS]
    true_counts = [0]*len(SETS)
    singleton_signatures = [0]*len(gates)
    shifted_signatures = [0]*len(gates)
    low_rows = 0
    for row in range(1 << N):
        x = [bool(row & (1 << v)) for v in range(N)]
        wires = list(x)
        for gate in gates:
            args = [wires[w] if w < len(wires) else False for w in gate["inputs"]]
            if gate["op"] == "and": value = all(args)
            elif gate["op"] == "or": value = any(args)
            else: value = not (args[0] if args else False)
            wires.append(value)
        for i, S in enumerate(SETS):
            expected = any(x[v] for v in S)
            assert wires[outputs[i]] == expected
            if expected:
                vectors[i][row//8] |= 1 << (row%8)
                true_counts[i] += 1
        if row.bit_count() < len(Y):
            assert wires[N+2]
            low_rows += 1
        if row == y:
            assert not wires[N+2]
        for p in range(N):
            if row == 1 << p:
                for j in range(len(gates)):
                    singleton_signatures[j] |= int(wires[N+j]) << p
            if p not in Y and row == y | (1 << p):
                for j in range(len(gates)):
                    shifted_signatures[j] |= int(wires[N+j]) << p
    heavy = [i for i,S in enumerate(sets) if not S & y]
    heavy_masks = {sets[i] for i in heavy}
    refunds = [j for j in range(len(gates))
               if singleton_signatures[j] in sets and shifted_signatures[j] in heavy_masks]
    F = sum(len(S) if i in heavy else min(len(Y),len(S)) for i,S in enumerate(SETS))
    B = sum(min(len(Y),len(S))-1 for S in SETS)
    heavy_excess = sum(max(len(SETS[i])-len(Y)-1,0) for i in heavy)
    heavy_base = sum(len(SETS[i])-1 for i in heavy)+sum(i not in heavy for i in range(len(SETS)))+len(Y)
    assert F == 35 and B == 20 and heavy == [0] and refunds == [9]
    assert len(gates) == 28 and low_rows == 92 and heavy_excess == 4 and heavy_base == 19

    # Check compatibility and compare against the existing two independent
    # scalar/bitvector evaluation implementations, without constructing a SAT
    # encoder or calling a solver.
    sys.path.insert(0,str(HERE.parent))
    import search
    loaded = search.load_cases(HERE / "case.json")
    assert loaded == [case] and search.bounds(case) == [23]
    a = search.evaluate(N,baseline,sets,y)
    b = search.evaluate_vectors(N,baseline,sets,y)
    assert a == b
    assert a["outputs_correct"] and a["not_window_correct"] and a["refunded_gates"] == refunds
    report = {"status":"PASS", "n":N,"m":len(SETS),"k":len(Y),
              "target_vertices":SETS,"Y":Y,"all_pair_intersections":intersections,
              "all_input_rows":1 << N,"output_values_checked":len(SETS)*(1 << N),
              "target_true_row_counts":true_counts,
              "target_vector_sha256":[hashlib.sha256(v).hexdigest() for v in vectors],
              "low_weight_rows_checked":low_rows,"F":F,"B":B,"H":len(heavy),
              "light_minterm_lower_bound":B+len(Y),
              "forced_refund_lower_bound":len(heavy),
              "necessary_violation_gate_count":23,"necessary_violation_refund_count":1,
              "heavy_excess_after_forced_refund":heavy_excess,
              "heavy_minterm_baseline":heavy_base,"surplus_if_23_gates":23-heavy_base,
              "baseline_size":len(gates),"baseline_refunded_gates":refunds,
              "baseline_rhs":a["right_hand_side"],
              "existing_search_scalar_and_vectors_agree":True,
              "solver_started":False,
              "scope":"Full family/baseline data audit; the equality-partition exclusion is a separate paper proof."}
    (HERE / "audit.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({k:v for k,v in report.items() if k not in ["all_pair_intersections","target_vector_sha256"]},indent=2))


if __name__ == "__main__":
    main()
