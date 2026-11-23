"""Check the exact semantics of the six-AND witness in checked L-meta-1006.

The checked theorem concerns a maximal-independent-set boundary condition.
This audit compares the same circuit with the full edge function as well.
Source: pequalnp-proofs/lean/PEqualNP/Outside/L_meta_1006.lean
"""

import json
from pathlib import Path

EDGES = [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
         (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9),
         (6, 7), (6, 10), (7, 9), (8, 9)]


def edge_function(mask):
    return any(mask >> a & 1 and mask >> b & 1 for a, b in EDGES)


def circuit(mask):
    x = [bool(mask >> i & 1) for i in range(11)]
    g0 = (x[7] or x[10]) and (x[6] or x[9])
    g1 = x[2] and (x[5] or x[10] or g0)
    g2 = x[0] and (x[9] or x[10])
    g3 = (x[8] or g0) and (x[4] or x[5])
    g4 = (x[4] or x[8]) and (x[1] or g0)
    g5 = x[3] and (x[6] or x[7])
    return g1 or g2 or g3 or g4 or g5


if __name__ == "__main__":
    independent = [m for m in range(1 << 11) if not edge_function(m)]
    maximal = [m for m in independent if all(
        m >> v & 1 or edge_function(m | (1 << v)) for v in range(11))]
    fp = [m for m in range(1 << 11) if circuit(m) and not edge_function(m)]
    fn = [m for m in range(1 << 11) if edge_function(m) and not circuit(m)]
    boundary_ok = all(not circuit(m) and all(
        m >> v & 1 or circuit(m | (1 << v)) for v in range(11)) for m in maximal)
    result = {
        "source_lemma": "L-meta-1006",
        "inputs_checked": 1 << 11,
        "maximal_independent_sets": len(maximal),
        "checked_boundary_condition_holds": boundary_ok,
        "full_function_false_positives": len(fp),
        "full_function_false_negatives": len(fn),
        "missed_edge_inputs": [list(e) for e in EDGES if not circuit((1 << e[0]) | (1 << e[1]))],
        "interpretation": "This witness satisfies its boundary theorem and does not compute the full edge function.",
    }
    assert boundary_ok and len(fp) == 0 and len(fn) == 39
    output = Path(__file__).with_name("boundary-witness-audit.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
