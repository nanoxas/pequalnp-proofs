"""Residual-pool obstruction even when every sound heavy gate is eligible.

Exact original singleton/shifted/complement rows and an exhaustive abstract
generator identity are checked.  The 23-input truth table is not enumerated.
"""
from pathlib import Path
import hashlib
import json

from audit import evaluate
from residual_audit import build as six_group_build

HERE = Path(__file__).resolve().parent


def build():
    lights = [g['target'] for g in six_group_build()['light_groups']] + [[0, 7, 8]]
    n, gates = 23, []
    def gate(op, *args):
        gates.append({'op': op, 'inputs': list(args)})
        return n+len(gates)-1
    h = gate('and', gate('and', 0, 1), 2)
    z = gate('not', h)
    narrow = {p: gate('and', p, z) for p in range(3, 9)}
    groups, mixes = [], []
    for i, S in enumerate(lights):
        y = next(p for p in S if p < 3)
        ps = [p for p in S if p >= 3]
        ts = [9+2*i, 10+2*i]
        switches = [gate('or', narrow[p], gate('and', t, h)) for p, t in zip(ps, ts)]
        mix = gate('or', *switches)
        groups.append({'target': S, 'chunk': ts, 'y_point': y,
                       'output': gate('or', y, mix)})
        mixes.append(mix)
    mix = mixes[0]
    for w in mixes[1:]:
        mix = gate('or', mix, w)
    T = list(range(9, 23))
    clauses = []
    for y in range(3):
        clause = y
        for t in T:
            clause = gate('or', clause, t)
        clauses.append(clause)
    q = gate('and', gate('and', clauses[0], clauses[1]), clauses[2])
    output = gate('or', gate('and', q, z), gate('and', mix, h))
    return {'name': 'seven_light_one_heavy_all_ops', 'n': n, 'k': 3,
            'y': [0, 1, 2], 'h_wire': h, 'not_gate': z-n, 'gates': gates,
            'light_groups': groups, 'heavy_target': T, 'heavy_output': output}


def abstract_identity(case):
    # Three Y bits, seven independent s_i=OR(P_i), and seven independent
    # t_i=OR(T_i). Every actual assignment maps into this larger abstract
    # cube, so these identities cover all original assignments.
    variables = 3+2*len(case['light_groups'])
    rows = 1 << variables
    mask = (1 << rows)-1
    bits = [(mask // ((1 << (1 << p))+1)) << (1 << p) for p in range(variables)]
    h = bits[0] & bits[1] & bits[2]
    z = mask ^ h
    mix, all_t = 0, 0
    for i, group in enumerate(case['light_groups']):
        s, t = bits[3+i], bits[3+len(case['light_groups'])+i]
        m = (s & z) | (t & h)
        y = bits[group['y_point']]
        assert y | m == y | s
        mix |= m
        all_t |= t
    q = (bits[0] | all_t) & (bits[1] | all_t) & (bits[2] | all_t)
    assert q == h | all_t
    assert (q & z) | (mix & h) == all_t
    return rows


def audit(case):
    n, gates, Y = case['n'], case['gates'], set(case['y'])
    sets = [set(g['target']) for g in case['light_groups']] + [set(case['heavy_target'])]
    outputs = [g['output'] for g in case['light_groups']] + [case['heavy_output']]
    assert all(len(A & B) <= 1 for i, A in enumerate(sets) for B in sets[i+1:])
    assert all(len(g['inputs']) <= 2 and all(w < n+j for w in g['inputs'])
               for j, g in enumerate(gates))
    assert [j for j, g in enumerate(gates) if g['op'] == 'not'] == [case['not_gate']]
    ymask = sum(1 << p for p in Y)
    rows = [1 << p for p in range(n)] + [ymask | (1 << p) for p in range(n)]
    rows += [((1 << n)-1) ^ sum(1 << p for p in S) for S in sets] + [0, ymask]
    mask = (1 << len(rows))-1
    inputs = [sum(1 << j for j, x in enumerate(rows) if x >> p & 1) for p in range(n)]
    original = evaluate(case, inputs, mask)
    c1, c0 = evaluate(case, inputs, mask, True), evaluate(case, inputs, mask, False)
    for S, out in zip(sets, outputs):
        assert original[out] == sum(1 << j for j, x in enumerate(rows)
                                    if any(x >> p & 1 for p in S))
    U = [{p for p in range(n) if original[n+j] >> p & 1} for j in range(len(gates))]
    V = [{p for p in range(n) if p not in Y and original[n+j] >> (n+p) & 1}
         for j in range(len(gates))]
    assert all(U[j] == {p for p in range(n) if c1[n+j] >> p & 1} for j in range(len(gates)))
    assert all(V[j] == {p for p in range(n) if p not in Y and c0[n+j] >> (n+p) & 1}
               for j in range(len(gates)))
    G = [{j for j in range(len(gates)) if j != case['not_gate'] and len(U[j]) >= 2
          and U[j] <= S} for S in sets]
    heavy_negative_row = 2*n+len(sets)-1
    Hall = {j for j in range(len(gates)) if not(c0[n+j] >> heavy_negative_row & 1)
            and len(V[j]) >= 2}
    Hor = {j for j in Hall if gates[j]['op'] == 'or'}
    R = {j for j in range(len(gates)) if U[j] in sets and V[j] == sets[-1]}
    assert R == {case['heavy_output']-n}
    assert [len(A) for A in G] == [2]*7+[4]
    assert len(Hor) == 14 and len(Hall) == 15
    unionG = set().union(*G)
    resources = unionG | Hall
    quota = 7*2 + len(sets[-1])-1
    assert len(unionG) == 18 and len(resources) == 25 and quota == 27
    assert quota > len(resources)+len(R)
    pending, live = list(outputs), set()
    while pending:
        w = pending.pop()
        if w < n or w-n in live:
            continue
        live.add(w-n)
        pending.extend(gates[w-n]['inputs'])
    assert len(live) == len(gates)
    lhs = sum(min(3, len(S)) for S in sets[:-1])+len(sets[-1])
    rhs = len(gates)+len(R)+len(sets)
    assert lhs <= rhs
    return {'status': 'EXACT_REQUIRED_ROWS_AND_GENERIC_IDENTITY_AUDIT_PASS',
            'n': n, 'gate_count': len(gates), 'target_count': len(sets),
            'original_sample_rows_checked': len(rows), 'full_original_truth_rows_checked': 0,
            'abstract_identity_rows_checked': abstract_identity(case),
            'all_gates_live': True, 'G': [sorted(A) for A in G],
            'H_or': sorted(Hor), 'H_all': sorted(Hall), 'refund_gates': sorted(R),
            'eligible_union_count': len(resources), 'total_quota': quota, 'refund_count': len(R),
            'unpaid_after_refunds': quota-len(resources)-len(R),
            'unused_gates': len(gates)-len(resources), 'weighted_lhs': lhs, 'exact_997_rhs': rhs}


def main():
    case = build()
    result = audit(case)
    circuit = HERE/'all-ops-circuit.json'
    circuit.write_text(json.dumps(case, indent=2)+'\n')
    digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    record = {'scope': 'Refutes residual matching in C1-private union all C0-sound wide gates plus refunds. The exact997 inequality holds; general unused credits remain available.',
              'lean_checked': False, 'solver_used': False, 'script_sha256': digest(Path(__file__)),
              'evaluator_sha256': digest(HERE/'audit.py'), 'source_builder_sha256': digest(HERE/'residual_audit.py'),
              'circuit_sha256': digest(circuit), 'result': result}
    (HERE/'all-ops-results.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ['status', 'n', 'gate_count',
        'original_sample_rows_checked', 'abstract_identity_rows_checked',
        'eligible_union_count', 'total_quota', 'refund_count', 'unused_gates']}, indent=2))


if __name__ == '__main__':
    main()
