"""Affine-line obstruction to the nonempty shifted heavy resource pool.

No truth table of the large original circuit is claimed.  The original
outputs follow from the recorded generator identities, checked for every
control assignment.  Singleton signatures and the entire C0-on-Y-subcube
function of EVERY gate are propagated exactly.  The latter functions are
all constants or disjunctions; the evaluator rejects an AND that does not
preserve that representation.  No SAT solver, Lean, network or lease data.
"""
from itertools import combinations, product
from pathlib import Path
import hashlib
import json
import struct

HERE = Path(__file__).resolve().parent


def control_identity(k):
    cases = 0
    for ys in product([False, True], repeat=k):
        h, z = all(ys), not all(ys)
        for s, t in product([False, True], repeat=2):
            m = (s and z) or (t and h)
            q = all(y or t for y in ys)
            assert q == (h or t)
            assert ((q and z) or (m and h)) == t
            for y in ys:
                assert (y or m) == (y or s)
            cases += 1
    return cases


def audit(q, k):
    assert q % 2 == 1 and all(q % d for d in range(2, int(q**0.5)+1))
    assert 2 <= k <= q and q >= k+3
    points = q*q
    n = k+2*points
    p_offset, t_offset = k, k+points
    point = lambda x, y: x*q+y
    lines = [(slope, [point(x, (slope*x+b) % q) for x in range(q)])
             for slope in range(k) for b in range(q)]
    heavy_count = len(lines)
    light_specs = [(line_id, slope, line[j], line[j+1])
                   for line_id, (slope, line) in enumerate(lines)
                   for j in range(0, q-1, 2)]
    light_sets = [[slope, p_offset+a, p_offset+b]
                  for _, slope, a, b in light_specs]
    heavy_sets = [[t_offset+p for p in line] for _, line in lines]
    sets = light_sets+heavy_sets
    masks = [sum(1 << p for p in S) for S in sets]
    heavy_masks = masks[len(light_sets):]
    owners = [set() for _ in range(n)]
    target_digest = hashlib.sha256()
    used_pairs = set()
    for i, S in enumerate(sets):
        target_digest.update(struct.pack('<I', len(S)))
        target_digest.update(struct.pack('<'+'I'*len(S), *sorted(S)))
        for p in S:
            owners[p].add(i)
        for p, r in combinations(sorted(S), 2):
            pair = p*n+r
            assert pair not in used_pairs
            used_pairs.add(pair)
    del used_pairs
    heavy_owners = [{i-len(light_sets) for i in A if i >= len(light_sets)} for A in owners]
    target_mask_set, heavy_mask_set = set(masks), set(heavy_masks)
    all_inputs = (1 << n)-1
    outside = all_inputs ^ ((1 << k)-1)
    # U is exact singleton truth. V=-1 means constant true on the Y-subcube;
    # otherwise V is the exact OR-of-inputs mask on that entire subcube.
    U = [1 << p for p in range(n)]
    V = [-1 if p < k else 1 << p for p in range(n)]
    gates, outputs = [], []
    G_card, H_card = [0]*len(sets), [0]*heavy_count
    counts = {'G_union': 0, 'H_nonempty_union': 0, 'eligible_union': 0,
              'refunds': 0, 'AND': 0, 'OR': 0, 'NOT': 0}
    gate_digest, signature_digest = hashlib.sha256(), hashlib.sha256()
    ubytes = (n+7)//8

    def owner_candidates(mask, target_owners):
        if not mask:
            return set()
        first = (mask & -mask).bit_length()-1
        rest = mask & (mask-1)
        if not rest:
            return set(target_owners[first])
        second = (rest & -rest).bit_length()-1
        return target_owners[first] & target_owners[second]

    def gate(op, a, b=None):
        w = len(U)
        assert 0 <= a < w and (b is None or 0 <= b < w)
        if op == 'and':
            u = U[a] & U[b]
            va, vb = V[a], V[b]
            if va == -1:
                v = vb
            elif vb == -1:
                v = va
            elif va & ~vb == 0:
                v = va
            elif vb & ~va == 0:
                v = vb
            else:
                raise AssertionError('C0 AND is not an exact disjunction')
            opcode = 0
        elif op == 'or':
            u = U[a] | U[b]
            v = -1 if V[a] == -1 or V[b] == -1 else V[a] | V[b]
            opcode = 1
        else:
            assert op == 'not' and b is None and V[a] in [0, -1]
            u = all_inputs ^ U[a]
            v = 0 if V[a] == -1 else -1
            opcode = 2
        U.append(u); V.append(v); gates.append((opcode, a, b))
        counts[op.upper()] += 1
        gate_digest.update(struct.pack('<BII', opcode, a, 0xffffffff if b is None else b))
        signature_digest.update(u.to_bytes(ubytes, 'little'))
        signature_digest.update((outside if v == -1 else v).to_bytes(ubytes, 'little'))
        gs = []
        if u.bit_count() >= 2:
            gs = [i for i in owner_candidates(u, owners) if u & ~masks[i] == 0]
        assert len(gs) <= 1
        for i in gs:
            G_card[i] += 1
        hs = []
        if v not in [0, -1]:
            hs = [i for i in owner_candidates(v, heavy_owners) if v & ~heavy_masks[i] == 0]
        for i in hs:
            H_card[i] += 1
        counts['G_union'] += bool(gs)
        counts['H_nonempty_union'] += bool(hs)
        counts['eligible_union'] += bool(gs or hs)
        vmask = outside if v == -1 else v
        counts['refunds'] += u in target_mask_set and vmask in heavy_mask_set
        return w

    h = 0
    for y in range(1, k):
        h = gate('and', h, y)
    assert U[h] == 0 and V[h] == -1
    z = gate('not', h)
    narrow_u = [gate('and', p_offset+p, z) for p in range(points)]
    narrow_v = [gate('and', t_offset+p, h) for p in range(points)]
    switches = [gate('or', narrow_u[p], narrow_v[p]) for p in range(points)]
    light_index = 0
    for line_id, (slope, line) in enumerate(lines):
        chunks = []
        for j in range(0, q-1, 2):
            c = gate('or', switches[line[j]], switches[line[j+1]])
            o = gate('or', slope, c)
            assert U[o] == masks[light_index] and V[o] == -1
            outputs.append(o)
            light_index += 1
            chunks.append(c)
        chunks.append(switches[line[-1]])
        mix = chunks[0]
        for c in chunks[1:]:
            mix = gate('or', mix, c)
        assert U[mix] == sum(1 << (p_offset+p) for p in line)
        assert V[mix] == heavy_masks[line_id]
        clauses = []
        for y in range(k):
            c = y
            for p in line:
                c = gate('or', c, t_offset+p)
            clauses.append(c)
        Q = clauses[0]
        for c in clauses[1:]:
            Q = gate('and', Q, c)
        assert U[Q] == heavy_masks[line_id] and V[Q] == -1
        o = gate('or', gate('and', Q, z), gate('and', mix, h))
        assert U[o] == heavy_masks[line_id] and V[o] == heavy_masks[line_id]
        outputs.append(o)

    assert counts['NOT'] == 1
    assert G_card == [2]*len(light_sets)+[k+1]*heavy_count
    assert counts['G_union'] == heavy_count*(q+k)
    assert counts['H_nonempty_union'] == 2*points+heavy_count*(q+1)
    expected_union = 2*points+heavy_count*(3*(q-1)//2+k+2)
    assert counts['eligible_union'] == expected_union
    assert counts['refunds'] == heavy_count
    expected_size = k+3*points+heavy_count*((q-1)+(q-1)//2+k*q+(k-1)+3)
    assert len(gates) == expected_size
    seen, pending = set(), list(outputs)
    while pending:
        w = pending.pop()
        if w < n or w-n in seen:
            continue
        seen.add(w-n)
        _, a, b = gates[w-n]
        pending.append(a)
        if b is not None:
            pending.append(b)
    assert len(seen) == len(gates)
    demand = 2*heavy_count*(q-1)
    lhs = 3*len(light_sets)+q*heavy_count
    rhs = len(gates)+heavy_count+len(sets)
    assert lhs <= rhs
    return {'q': q, 'k': k, 'input_count': n, 'heavy_targets': heavy_count,
            'light_targets': len(light_sets), 'target_count': len(sets),
            'gate_count': len(gates), 'all_gates_live': True,
            'exact_C0_symbolic_function_class': 'constant or disjunction on the entire Y-subcube',
            'singleton_and_shifted_signatures': 'all gates, exact symbolic propagation',
            'full_original_truth_rows_checked': 0, 'control_identity_cases': control_identity(k),
            'all_heavy_classes_deficient': q-1 > k+1,
            'heavy_private_count_each': k+1, 'heavy_deficit_each': q-k-2,
            'G_union_count': counts['G_union'], 'H_nonempty_union_count': counts['H_nonempty_union'],
            'eligible_union_count': counts['eligible_union'], 'total_quota': demand,
            'refund_count': counts['refunds'],
            'unpaid_after_refunds': demand-counts['eligible_union']-counts['refunds'],
            'unused_gates': len(gates)-counts['eligible_union'],
            'weighted_lhs': lhs, 'exact_997_rhs': rhs,
            'target_family_sha256': target_digest.hexdigest(),
            'gate_list_sha256': gate_digest.hexdigest(),
            'all_signature_pairs_sha256': signature_digest.hexdigest()}


def main():
    cases = [audit(11, 5), audit(47, 9)]
    assert cases[-1]['unpaid_after_refunds'] == 235
    result = {'status': 'SYMBOLIC_GATE_SEMANTICS_AND_GENERATOR_IDENTITY_AUDIT_PASS',
              'scope': 'Auxiliary counterexample: C1-private plus all nonempty C0-sound heavy gates and exact refunds do not suffice as exclusive quota resources. The actual L-meta-997 inequality holds.',
              'lean_checked': False, 'solver_used': False,
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'cases': cases}
    (HERE/'results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps([{k: c[k] for k in ['q', 'k', 'input_count', 'gate_count',
        'total_quota', 'eligible_union_count', 'refund_count', 'unpaid_after_refunds',
        'unused_gates']} for c in cases], indent=2))


if __name__ == '__main__':
    main()
