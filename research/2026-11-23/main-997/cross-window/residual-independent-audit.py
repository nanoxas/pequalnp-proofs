"""Independent complete vector check of the published-local residual example.

No SAT, Lean, network, or mutation of the source audit. Input vectors use
byte patterns, independently of the source audit's integer-division formula.
"""
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'quota-audit/residual-circuit.json'
case = json.loads(SOURCE.read_text())
expected = json.loads((HERE.parent / 'quota-audit/residual-results.json').read_text())['result']
n = case['n']
rows = 1 << n
byte_count = rows // 8
mask = (1 << rows) - 1
inputs = []
for p in range(n):
    if p < 3:
        raw = bytes([0xAA, 0xCC, 0xF0][p:p+1]) * byte_count
    else:
        block = 1 << (p-3)
        raw = (bytes(block) + bytes([255]) * block) * (byte_count // (2*block))
    inputs.append(int.from_bytes(raw, 'little'))

def values(replace=None):
    result = list(inputs)
    for j, gate in enumerate(case['gates']):
        assert gate['op'] in {'and', 'or', 'not'} and len(gate['inputs']) <= 2
        assert all(0 <= r < n+j for r in gate['inputs'])
        args = [result[r] for r in gate['inputs']]
        if j == case['not_gate'] and replace is not None:
            v = mask if replace else 0
        elif gate['op'] == 'or':
            v = 0
            for a in args: v |= a
        elif gate['op'] == 'and':
            v = mask
            for a in args: v &= a
        else:
            v = mask ^ (args[0] if args else 0)
        result.append(v)
    return result

original, c0, c1 = values(), values(False), values(True)
Y = set(case['y'])
ymask = sum(1 << p for p in Y)
targets = [set(group['target']) for group in case['light_groups']] + [set(case['heavy_target'])]
outputs = [group['output'] for group in case['light_groups']] + [case['heavy_output']]
assert all(len(a & b) <= 1 for a, b in combinations(targets, 2))
assert [j for j, g in enumerate(case['gates']) if g['op'] == 'not'] == [case['not_gate']]
output_hashes = []
for target, output in zip(targets, outputs):
    wanted = 0
    for p in target: wanted |= inputs[p]
    assert original[output] == wanted
    output_hashes.append(sha256(original[output].to_bytes(byte_count, 'little')).hexdigest())
assert output_hashes == expected['truth_vector_sha256']
h = mask
for p in Y: h &= inputs[p]
assert original[case['h_wire']] == h
assert original[n+case['not_gate']] == mask ^ h

size = len(case['gates'])
U = [{p for p in range(n) if (original[n+j] >> (1 << p)) & 1} for j in range(size)]
V = [{p for p in range(n) if p not in Y and (original[n+j] >> (ymask | (1 << p))) & 1}
     for j in range(size)]
G = [{j for j in range(size) if j != case['not_gate'] and len(U[j]) >= 2 and U[j] <= S}
     for S in targets]
T = targets[-1]
negative = ((1 << n)-1) ^ sum(1 << p for p in T)
H = {j for j, g in enumerate(case['gates']) if g['op'] == 'or' and
     not ((c0[n+j] >> negative) & 1) and len(V[j]) >= 2}
R = {j for j in range(size) if any(U[j] == S for S in targets) and V[j] == T}
union = set().union(*G) | H
demand = sum(min(len(Y), len(S))-1 for S in targets[:-1]) + len(T)-1
assert [sorted(g) for g in G] == expected['G']
assert sorted(H) == expected['H'] and sorted(R) == expected['refund_gates']
assert demand == 23 and len(union) == 21 and len(R) == 1
assert demand > len(union) + len(R)
weighted = sum(min(len(Y), len(S)) for S in targets[:-1]) + len(T)
assert weighted == 30 and size+len(R)+len(targets) == 97
result = {
    'status': 'PASS_INDEPENDENT_FULL_VECTOR_AUDIT',
    'script_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
    'source_circuit_sha256': sha256(SOURCE.read_bytes()).hexdigest(),
    'inputs': n, 'complete_truth_rows': rows, 'gate_count': size,
    'target_count': len(targets), 'target_quotas_sum': demand,
    'eligible_union_count': len(union), 'exact_refunds': len(R),
    'unused_gate_count': size-len(union), 'weighted_lhs': weighted,
    'exact_997_rhs': size+len(R)+len(targets),
    'output_hashes_match_source_audit': True,
    'scope': 'Refutes the specified private/heavy pool-only matching with refund capacity; the full L-meta-997 inequality holds.',
    'solver_used': False, 'lean_checked': False,
}
(HERE / 'residual-independent-audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
