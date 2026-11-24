"""Minimum full-OR quota obstructions; no SAT, Lean, network, or lease data.

Small cases receive a complete truth-vector audit. The affine-plane case
uses exact singleton/shifted/negative rows and a separately exhaustive
Boolean-identity check of the generator's output construction.
"""
from __future__ import annotations

from itertools import combinations, product
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent


def build(k, lines, outside_count, d, name):
    n = k + outside_count + len(lines) * d
    gates = []
    def gate(op, *args):
        gates.append({'op': op, 'inputs': list(args)})
        return n + len(gates) - 1
    h = 0
    for y in range(1, k):
        h = gate('and', h, y)
    z = gate('not', h)
    sz = [gate('and', k + p, z) for p in range(outside_count)]
    groups = []
    for i, (direction, points) in enumerate(lines):
        ts = list(range(k + outside_count + i*d, k + outside_count + (i+1)*d))
        switches = [gate('or', sz[points[j % len(points)]], gate('and', t, h))
                    for j, t in enumerate(ts)]
        mix = switches[0]
        chain = []
        for w in switches[1:]:
            mix = gate('or', mix, w)
            chain.append(mix-n)
        light = gate('or', direction, mix)
        clauses = []
        for y in range(k):
            clause = y
            for t in ts:
                clause = gate('or', clause, t)
            clauses.append(clause)
        p = clauses[0]
        for clause in clauses[1:]:
            p = gate('and', p, clause)
        heavy = gate('or', gate('and', p, z), gate('and', mix, h))
        groups.append({'light': [direction] + [k+p for p in points], 'heavy': ts,
                       'light_out': light, 'heavy_out': heavy, 'chain': chain})
    return {'name': name, 'k': k, 'n': n, 'y': list(range(k)),
            'not_gate': z-n, 'h_wire': h, 'gates': gates, 'groups': groups}


def affine_lines(q):
    assert q == 5
    result = []
    for slope in range(q):
        for b in range(q):
            result.append((slope, [x*q + ((slope*x+b) % q) for x in range(q)]))
    for x in range(q):
        result.append((q, [x*q+y for y in range(q)]))
    return result


def evaluate(case, inputs, mask, replacement=None):
    values = list(inputs)
    for j, g in enumerate(case['gates']):
        a = [values[w] if w < len(values) else 0 for w in g['inputs']]
        if j == case['not_gate'] and replacement is not None:
            v = mask if replacement else 0
        elif g['op'] == 'and':
            v = mask
            for x in a: v &= x
        elif g['op'] == 'or':
            v = 0
            for x in a: v |= x
        else:
            v = mask ^ (a[0] if a else 0)
        values.append(v)
    return values


def boolean_identity_audit(k):
    checked = 0
    for ys in product([False, True], repeat=k):
        h = all(ys)
        for s, t in product([False, True], repeat=2):
            z = not h
            mix = (s and z) or (t and h)
            p = all(y or t for y in ys)
            assert p == (h or t)
            for yi in ys:
                assert (yi or mix) == (yi or s)
            assert ((p and z) or (mix and h)) == t
            checked += 1
    return checked


def audit(case):
    k, n, gates = case['k'], case['n'], case['gates']
    Y = (1 << k)-1
    groups = case['groups']
    sets = [set(g[key]) for g in groups for key in ['light', 'heavy']]
    assert all(len(a & b) <= 1 for a,b in combinations(sets, 2))
    assert all(len(g['inputs']) <= 2 and all(w < n+j for w in g['inputs']) for j,g in enumerate(gates))
    assert [j for j,g in enumerate(gates) if g['op']=='not'] == [case['not_gate']]
    rows = [1 << p for p in range(n)] + [Y | (1 << p) for p in range(n)]
    rows += [((1 << n)-1) ^ sum(1 << p for p in g['heavy']) for g in groups]
    rows += [((1 << n)-1) ^ sum(1 << p for p in g['light']) for g in groups]
    mask = (1 << len(rows))-1
    inputs = [sum(1 << j for j,row in enumerate(rows) if row >> p & 1) for p in range(n)]
    original = evaluate(case, inputs, mask)
    c0 = evaluate(case, inputs, mask, False)
    c1 = evaluate(case, inputs, mask, True)
    U = [{p for p in range(n) if original[n+j] >> p & 1} for j in range(len(gates))]
    V = [{p for p in range(k,n) if original[n+j] >> (n+p) & 1} for j in range(len(gates))]
    assert all(U[j] == {p for p in range(n) if c1[n+j] >> p & 1} for j in range(len(gates)))
    assert all(V[j] == {p for p in range(k,n) if c0[n+j] >> (n+p) & 1} for j in range(len(gates)))
    refunds = {j for j in range(len(gates)) if U[j] in sets and V[j] in [set(g['heavy']) for g in groups]}
    readers = {j for j,g in enumerate(gates) if j > case['not_gate'] and n+case['not_gate'] in g['inputs']}
    pools = []
    for i, group in enumerate(groups):
        S,T = set(group['light']),set(group['heavy'])
        L = {j for j,g in enumerate(gates) if g['op']=='or' and len(U[j])>=2 and U[j]<=S} - readers
        H = {j for j,g in enumerate(gates) if g['op']=='or' and len(V[j])>=2 and not(c0[n+j] >> (2*n+i)&1)} - readers
        assert L == set(group['chain']) | {group['light_out']-n}
        assert H == set(group['chain']) | {group['heavy_out']-n}
        assert all(not(c1[n+j] >> (2*n+len(groups)+i)&1) for j in L)
        private_h = {j for j in range(len(gates)) if len(U[j])>=2 and U[j]<=T}
        private_l_and = {j for j,g in enumerate(gates) if g['op']=='and' and len(U[j])>=2 and U[j]<=S}
        assert not private_l_and
        assert len(private_h) == k+1 < len(T)-1
        qL,qH = min(k,len(S))-1,len(T)-1
        choices = [(len(set(a)&set(b)),a,b) for a in combinations(sorted(L),qL) for b in combinations(sorted(H),qH)]
        overlap,a,b = min(choices)
        assert overlap == k-3 and not((L&H)&refunds)
        pools.append({'light_pool': sorted(L),'heavy_pool': sorted(H),'light_quota':qL,'heavy_quota':qH,
                      'minimum_overlap':overlap,'selected_light':list(a),'selected_heavy':list(b),
                      'heavy_private_count':len(private_h),'heavy_deficit':len(T)-1-len(private_h)})
    for i,j in combinations(range(len(groups)),2):
        for x,y in [('light_pool','light_pool'),('heavy_pool','heavy_pool'),('light_pool','heavy_pool'),('heavy_pool','light_pool')]:
            assert not(set(pools[i][x]) & set(pools[j][y]))
    assert refunds == {g['heavy_out']-n for g in groups}
    live = set(); pending = [g[key] for g in groups for key in ['light_out','heavy_out']]
    while pending:
        w = pending.pop()
        if w<n or w-n in live: continue
        live.add(w-n); pending.extend(gates[w-n]['inputs'])
    assert len(live)==len(gates)
    exhaustive_rows = 0
    if n <= 18:
        exhaustive_rows = 1 << n
        fullmask = (1 << exhaustive_rows)-1
        iv = [(fullmask // ((1 << (1 << p))+1)) << (1 << p) for p in range(n)]
        full = evaluate(case,iv,fullmask)
        for group in groups:
            for kind in ['light','heavy']:
                want = 0
                for p in group[kind]: want |= iv[p]
                assert full[group[kind+'_out']] == want
        for size in range(k):
            for subset in combinations(range(n),size):
                row = sum(1 << p for p in subset)
                assert full[n+case['not_gate']] >> row & 1
        assert not(full[n+case['not_gate']] >> Y & 1)
    overlap = sum(p['minimum_overlap'] for p in pools)
    quota = sum(p['light_quota']+p['heavy_quota'] for p in pools)
    union = quota-overlap
    lhs = sum(min(k,len(g['light']))+len(g['heavy']) for g in groups)
    assert lhs <= len(gates)+len(refunds)+2*len(groups)
    return {'name':case['name'],'n':n,'k':k,'gate_count':len(gates),'target_count':2*len(groups),
            'all_gates_live':True,'full_truth_rows_checked':exhaustive_rows,
            'generator_boolean_identity_cases':boolean_identity_audit(k),'sample_rows_checked':len(rows),
            'original_output_correctness':'complete_truth_vectors' if exhaustive_rows else 'explicit_generator_boolean_identity',
            'minimum_full_quota_overlap':overlap,'refund_count':len(refunds),'direct_reader_count':len(readers),
            'minimum_overlap_le_refunds':overlap<=len(refunds),
            'minimum_overlap_le_refunds_plus_readers':overlap<=len(refunds)+len(readers),
            'optimal_selected_union_count':union,'unused_gates':len(gates)-union,
            'minimum_overlap_le_refunds_plus_unused':overlap<=len(refunds)+len(gates)-union,
            'weighted_lhs':lhs,'exact_997_rhs':len(gates)+len(refunds)+2*len(groups),
            'refund_gates':sorted(refunds),'direct_readers':sorted(readers),'pools':pools}


def main():
    cases = [build(5,[(0,list(range(4)))],4,8,'one_pair_k5'),
             build(6,affine_lines(5),25,9,'affine_q5_k6')]
    reports = [audit(case) for case in cases]
    cp=HERE/'circuits.json';cp.write_text(json.dumps(cases,indent=2)+'\n')
    rec={'status':'FINITE_SUPPORT_AND_BOOLEAN_IDENTITY_AUDIT_PASS','lean_checked':False,'solver_used':False,
         'scope':'Refutes full-heavy-OR minimum-quota overlap bounds by refunds alone and by refunds plus direct NOT readers. Does not refute L-meta-997 or residual-deficit/unused-gate accounting.',
         'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'circuits_sha256':hashlib.sha256(cp.read_bytes()).hexdigest(),'cases':reports}
    (HERE/'results.json').write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps([{k:r[k] for k in ['name','n','gate_count','minimum_full_quota_overlap','refund_count','direct_reader_count','unused_gates','full_truth_rows_checked','original_output_correctness']} for r in reports],indent=2))


if __name__=='__main__':
    main()
