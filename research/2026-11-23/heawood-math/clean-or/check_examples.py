"""Exhaustive 16-row checks for the normalization examples in the proof note."""
import json

n = 4
all_rows = (1 << (1 << n)) - 1
x = [sum(1 << row for row in range(1 << n) if row >> v & 1) for v in range(n)]
a, b, c, d = x
f = (a & b) | (b & c) | (c & d)
negative_rows = all_rows ^ f

def support(table):
    return [v for v in range(n) if table >> (1 << v) & 1]

def clean(table):
    return table & negative_rows == 0

# The final gate is AND, and neither AND has a clean operand.
g0 = c & d
g1 = a | c
g2 = b | g0
g3 = g1 & g2
assert g3 == f
assert clean(g0) and clean(g3)
assert all(support(t) for t in [c, d, g1, g2])

# A valid clean-operand bypass can increase the internal wire while preserving f.
g4 = g3 & a
original_output = g3 | g4
replacement_output = g3 | g3
assert clean(g4) and clean(g3)
assert g4 != g3 and g4 & ~g3 == 0
assert original_output == replacement_output == f
assert (g4 ^ g3) & negative_rows == 0

# Without global cleanliness, empty singleton support does not justify bypass.
h = a & d
g = h & b
assert support(h) == [] and not clean(h) and clean(g)
assert f | g == f
assert f | h != f
bad_row = (1 << 0) | (1 << 3)
assert not (f >> bad_row & 1)
assert (f | h) >> bad_row & 1

print(json.dumps({
    "rows_checked_per_example": 16,
    "clean_final_AND_path": "PASS",
    "safe_clean_operand_bypass": "PASS",
    "empty_singleton_without_global_cleanliness": {
        "result": "COUNTEREXAMPLE", "independent_input": [0, 3]
    }
}, indent=2))
