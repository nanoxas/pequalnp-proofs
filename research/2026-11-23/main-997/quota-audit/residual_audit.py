"""Exhaustive obstruction to matching only C1-private/C0-heavy resources.

This checks all 2^19 rows of a concrete one-NOT circuit.  Its actual 997
conclusion holds.  The failed auxiliary statement gives each light target
only its C1 private gates, each heavy target the union of its C1 private
and C0 sound OR gates, and one extra capacity at every exact refund.
"""
from itertools import combinations
from pathlib import Path
import hashlib
import json

from audit import evaluate

HERE = Path(__file__).resolve().parent


def build():
    # Points 0..6 correspond to the nonzero vectors 1..7 in F_2^3.
    # The line {0,1,2} is Y.  Every other Fano line meets it once.
    lines = sorted({tuple(sorted((a-1, b-1, (a ^ b)-1)))
                    for a, b in combinations(range(1, 8), 2)})
    Y = {0, 1, 2}
    lights = [list(line) for line in lines if set(line) != Y]
    assert len(lights) == 6
    assert all(len(set(S) & Y) == 1 for S in lights)
    n, k = 19, 3
    gates = []

    def gate(op, *args):
        gates.append({'op': op, 'inputs': list(args)})
        return n + len(gates)-1

    h = gate('and', gate('and', 0, 1), 2)
    z = gate('not', h)
    narrow = {p: gate('and', p, z) for p in range(3, 7)}
    groups, mixtures = [], []
    for i, S in enumerate(lights):
        y = next(iter(set(S) & Y))
        points = sorted(set(S)-Y)
        ts = [7+2*i, 8+2*i]
        switched = [gate('or', narrow[p], gate('and', t, h))
                    for p, t in zip(points, ts)]
        mix = gate('or', *switched)
        output = gate('or', y, mix)
        mixtures.append(mix)
        groups.append({'target': S, 'output': output,
                       'chunk': ts, 'mixture': mix})
    allmix = mixtures[0]
    for mix in mixtures[1:]:
        allmix = gate('or', allmix, mix)
    T = list(range(7, 19))
    clauses = []
    for y in range(k):
        clause = y
        for p in T:
            clause = gate('or', clause, p)
        clauses.append(clause)
    q = gate('and', gate('and', clauses[0], clauses[1]), clauses[2])
    out = gate('or', gate('and', q, z), gate('and', allmix, h))
    return {'name': 'six_fano_light_one_heavy', 'n': n, 'k': k,
            'y': sorted(Y), 'h_wire': h, 'not_gate': z-n,
            'gates': gates, 'light_groups': groups,
            'heavy_target': T, 'heavy_output': out}


def audit(case):
    n, k, gates = case['n'], case['k'], case['gates']
    Y = set(case['y'])
    ymask = sum(1 << p for p in Y)
    sets = [set(g['target']) for g in case['light_groups']]
    sets.append(set(case['heavy_target']))
    outputs = [g['output'] for g in case['light_groups']]
    outputs.append(case['heavy_output'])
    assert all(len(a & b) <= 1 for a, b in combinations(sets, 2))
    assert all(len(g['inputs']) <= 2 and all(w < n+j for w in g['inputs'])
               for j, g in enumerate(gates))
    assert [j for j, g in enumerate(gates) if g['op'] == 'not'] == [case['not_gate']]

    # Full truth vectors: bit x records the circuit value at input mask x.
    row_count = 1 << n
    mask = (1 << row_count)-1
    inputs = [(mask // ((1 << (1 << p))+1)) << (1 << p) for p in range(n)]
    original = evaluate(case, inputs, mask)
    c1 = evaluate(case, inputs, mask, True)
    c0 = evaluate(case, inputs, mask, False)
    for S, output in zip(sets, outputs):
        want = 0
        for p in S:
            want |= inputs[p]
        assert original[output] == want
    expected_h = mask
    for p in Y:
        expected_h &= inputs[p]
    assert original[case['h_wire']] == expected_h
    assert original[n+case['not_gate']] == mask ^ expected_h
    assert not(original[n+case['not_gate']] >> ymask & 1)
    for size in range(k):
        for A in combinations(range(n), size):
            x = sum(1 << p for p in A)
            assert original[n+case['not_gate']] >> x & 1

    U = [{p for p in range(n) if original[n+j] >> (1 << p) & 1}
         for j in range(len(gates))]
    V = [{p for p in range(n) if p not in Y and
          original[n+j] >> (ymask | (1 << p)) & 1}
         for j in range(len(gates))]
    assert all(U[j] == {p for p in range(n) if c1[n+j] >> (1 << p) & 1}
               for j in range(len(gates)))
    assert all(V[j] == {p for p in range(n) if p not in Y and
                       c0[n+j] >> (ymask | (1 << p)) & 1}
               for j in range(len(gates)))
    G = [{j for j in range(len(gates)) if j != case['not_gate']
          and len(U[j]) >= 2 and U[j] <= S} for S in sets]
    T = sets[-1]
    negative_T = ((1 << n)-1) ^ sum(1 << p for p in T)
    H = {j for j, g in enumerate(gates) if g['op'] == 'or'
         and not(c0[n+j] >> negative_T & 1) and len(V[j]) >= 2}
    assert all(V[j] <= T for j in H)
    R = {j for j in range(len(gates)) if U[j] in sets and V[j] == T}
    assert R == {case['heavy_output']-n}
    assert all(len(A) == 2 for A in G[:-1])
    assert len(G[-1]) == 4
    assert len(H) == 12
    assert all(not(A & B) for A, B in combinations(G, 2))
    union_G = set().union(*G)
    resources = union_G | H
    quotas = [min(k, len(S))-1 for S in sets[:-1]] + [len(T)-1]
    demand = sum(quotas)
    assert len(union_G) == 16
    assert len(resources) == 21
    assert demand == 23
    # This is the all-target Hall cut, so even arbitrary matching/exchanges
    # inside these eligible pools cannot meet demand with refund capacity.
    assert demand > len(resources) + len(R)

    pending, live = list(outputs), set()
    while pending:
        w = pending.pop()
        if w < n or w-n in live:
            continue
        live.add(w-n)
        pending.extend(gates[w-n]['inputs'])
    assert len(live) == len(gates)
    readers = {j for j, g in enumerate(gates) if j > case['not_gate']
               and n+case['not_gate'] in g['inputs']}
    lhs = sum(min(k, len(S)) for S in sets[:-1]) + len(T)
    rhs = len(gates) + len(R) + len(sets)
    assert lhs <= rhs
    return {'status': 'EXHAUSTIVE_TRUTH_AND_SUPPORT_AUDIT_PASS',
            'n': n, 'k': k, 'gate_count': len(gates), 'target_count': len(sets),
            'full_truth_rows_checked': row_count, 'all_gates_live': True,
            'private_counts': [len(A) for A in G], 'heavy_or_count': len(H),
            'private_union_count': len(union_G), 'eligible_union_count': len(resources),
            'target_quotas': quotas, 'total_quota': demand,
            'refund_count': len(R), 'direct_reader_count': len(readers),
            'residual_heavy_deficit': quotas[-1]-len(G[-1]),
            'heavy_resources_outside_private_union': len(H-union_G),
            'unpaid_by_eligible_union': demand-len(resources),
            'unpaid_after_refund_capacity': demand-len(resources)-len(R),
            'unused_gates': len(gates)-len(resources),
            'weighted_lhs': lhs, 'exact_997_rhs': rhs,
            'G': [sorted(A) for A in G], 'H': sorted(H), 'refund_gates': sorted(R),
            'direct_readers': sorted(readers),
            'truth_vector_sha256': [hashlib.sha256(original[o].to_bytes(
                (row_count+7)//8, 'little')).hexdigest() for o in outputs]}


def main():
    case = build()
    report = audit(case)
    source = HERE/'residual-circuit.json'
    source.write_text(json.dumps(case, indent=2)+'\n')
    record = {'scope': 'Refutes residual pool-only quota matching, even with one extra credit per exact refund. Unused gates remain essential; L-meta-997 holds in this example.',
              'lean_checked': False, 'solver_used': False,
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'evaluator_sha256': hashlib.sha256((HERE/'audit.py').read_bytes()).hexdigest(),
              'circuit_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
              'result': report}
    (HERE/'residual-results.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in ['status', 'n', 'gate_count',
        'full_truth_rows_checked', 'total_quota', 'eligible_union_count',
        'refund_count', 'unpaid_after_refund_capacity', 'unused_gates']}, indent=2))


if __name__ == '__main__':
    main()
