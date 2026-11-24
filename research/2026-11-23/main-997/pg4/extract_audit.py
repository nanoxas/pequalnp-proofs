"""Extract PG(2,4), then audit it through independent homogeneous incidence.

This script uses no SAT solver, Lean compiler, network, or operational state.
The affine generator is reused with attribution from negation-frontier/radon_probe.py.
"""
from datetime import datetime, timezone
import hashlib
import importlib.util
from itertools import combinations, product
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1]
GENERATOR = BASE / "negation-frontier/radon_probe.py"

# Independent GF(4) table for F_2[a]/(a^2+a+1), encoding a as 2.
MUL = ((0, 0, 0, 0), (0, 1, 2, 3), (0, 2, 3, 1), (0, 3, 1, 2))
INV = (None, 1, 3, 2)


def canonical(v):
    first = next(x for x in v if x)
    return tuple(MUL[INV[first]][x] for x in v)


def dot(a, b):
    return MUL[a[0]][b[0]] ^ MUL[a[1]][b[1]] ^ MUL[a[2]][b[2]]


def write(name, data):
    (HERE / name).write_text(json.dumps(data, indent=2) + "\n")


def main():
    spec = importlib.util.spec_from_file_location("pg4_affine_generator", GENERATOR)
    generator = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(generator)
    lines = generator.projective_lines(2)
    line_sets = [frozenset(line) for line in lines]
    masks = [sum(1 << p for p in line) for line in lines]

    # Validate the independent field table and agreement with the reused polynomial code.
    for a, b, c in product(range(4), repeat=3):
        assert MUL[MUL[a][b]][c] == MUL[a][MUL[b][c]]
        assert MUL[a][b ^ c] == MUL[a][b] ^ MUL[a][c]
    for a, b in product(range(4), repeat=2):
        assert MUL[a][b] == MUL[b][a] == generator.field_mul(a, b, 2)
    assert all(MUL[a][INV[a]] == 1 for a in range(1, 4))

    # The point labels match the affine generator; the independent check enumerates
    # every homogeneous one-dimensional subspace and every dual hyperplane.
    points = [(x, y, 1) for x in range(4) for y in range(4)]
    points += [(1, a, 0) for a in range(4)] + [(0, 1, 0)]
    projective = {canonical(v) for v in product(range(4), repeat=3) if any(v)}
    assert len(projective) == 21 == len(points)
    assert {canonical(p) for p in points} == projective
    homogeneous_lines = {frozenset(i for i, p in enumerate(points) if dot(c, p) == 0)
                         for c in projective}
    assert set(line_sets) == homogeneous_lines
    assert len(lines) == len(set(line_sets)) == 21
    assert all(len(line) == len(set(line)) == 5 for line in lines)
    assert all(len(a & b) == 1 for a, b in combinations(line_sets, 2))
    point_degrees = [sum(p in line for line in line_sets) for p in range(21)]
    assert point_degrees == [5] * 21
    assert all(sum(a in line and b in line for line in line_sets) == 1
               for a, b in combinations(range(21), 2))

    y_points = sorted(lines[0])[:3]
    y = sum(1 << p for p in y_points)
    assert y_points == [0, 4, 8] and y == 273
    assert all(p in lines[0] for p in y_points)
    hitting = [i for i, mask in enumerate(masks) if mask & y]
    disjoint = [i for i, mask in enumerate(masks) if not mask & y]
    contributions = [mask.bit_count() if not mask & y else min(y.bit_count(), mask.bit_count())
                     for mask in masks]
    assert len(hitting) == 13 and len(disjoint) == 8
    assert sum(contributions) == 79 and y.bit_count() == 3

    case = {"name": "pg2_4_three_collinear", "n": 21, "sets": masks,
            "y": y, "gate_bounds": [49]}
    write("case.json", case)
    # Compatibility path requested by the independent circuit-search agent.
    (HERE.parent / "pg4-case.json").write_text(json.dumps(case, indent=2) + "\n")
    write("geometry.json", {
        "name": case["name"], "field": "F_2[a]/(a^2+a+1)", "field_element_encoding": {"0": "0", "1": "1", "2": "a", "3": "a+1"},
        "points_homogeneous": points, "lines_points": lines, "line_masks": masks,
        "y_points": y_points, "y_mask": y, "containing_line_index": 0,
        "hitting_line_indices": hitting, "disjoint_line_indices": disjoint,
        "weight_contributions": contributions, "F": sum(contributions), "k": y.bit_count()
    })
    audit = {
        "status": "PASS", "scope": "Finite geometry and task-weight calculation only; no circuit synthesis or formal theorem proof.",
        "n": 21, "m": 21, "line_sizes": [5] * 21, "point_degrees": point_degrees,
        "incidences": 105, "line_pairs_checked": 210, "point_pairs_checked": 210,
        "distinct_lines_intersection_exactly_one": True,
        "distinct_points_on_exactly_one_line": True,
        "independent_homogeneous_enumeration_agrees": True,
        "y_points": y_points, "y": y, "y_collinear": True, "k": 3,
        "hitting_lines": 13, "disjoint_lines": 8, "F": 79,
        "weight_identity": "13*min(3,5) + 8*5 = 79",
        "requested_gate_bounds": [49],
        "counterexample_refund_requirement_at_49": "79 > 49 + R + 21 exactly when R <= 8; geometry alone does not establish a circuit or R.",
        "source_generator": "negation-frontier/radon_probe.py",
        "source_generator_sha256": hashlib.sha256(GENERATOR.read_bytes()).hexdigest(),
        "audit_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "case_sha256": hashlib.sha256((HERE / "case.json").read_bytes()).hexdigest(),
        "geometry_sha256": hashlib.sha256((HERE / "geometry.json").read_bytes()).hexdigest(),
        "created_utc": datetime.now(timezone.utc).isoformat()
    }
    write("audit.json", audit)
    print(json.dumps(audit, indent=2))


if __name__ == "__main__":
    main()
