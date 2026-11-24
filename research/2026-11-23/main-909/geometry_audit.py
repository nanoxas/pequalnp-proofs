#!/usr/bin/env python3
"""Exact, small enumeration of the public Petersen partial-function rows.

This is a geometry/necessary-condition audit, not a circuit search.
"""

import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
         (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
         (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
KG_LABELS = [(0, 1), (2, 3), (0, 4), (1, 3), (2, 4),
             (3, 4), (1, 4), (1, 2), (0, 2), (0, 3)]
UNIV = (1 << 10) - 1
NEIGHBORS = [0] * 10
for a, b in EDGES:
    NEIGHBORS[a] |= 1 << b
    NEIGHBORS[b] |= 1 << a


def vertices(mask):
    return [v for v in range(10) if mask >> v & 1]


def induced_edges(mask):
    return sorted([sorted((a, b)) for a, b in EDGES
                   if mask >> a & 1 and mask >> b & 1])


def independent(mask):
    return not induced_edges(mask)


def maximal(mask):
    return independent(mask) and all(
        (mask >> v & 1) or (NEIGHBORS[v] & mask)
        for v in range(10))


def row(mask):
    return {"mask": mask, "vertices": vertices(mask),
            "size": mask.bit_count(), "induced_edges": induced_edges(mask)}


def main():
    assert len(set(KG_LABELS)) == 10
    for a in range(10):
        for b in range(10):
            assert bool(NEIGHBORS[a] >> b & 1) == \
                set(KG_LABELS[a]).isdisjoint(KG_LABELS[b])

    indep = [x for x in range(1 << 10) if independent(x)]
    mis = [x for x in indep if maximal(x)]
    stars = sorted(sum(1 << v for v, label in enumerate(KG_LABELS)
                       if p in label) for p in range(5))
    triangles = sorted(sum(1 << v for v, label in enumerate(KG_LABELS)
                           if set(label) <= set(triple))
                       for triple in itertools.combinations(range(5), 3))
    assert sorted(mis) == sorted(stars + triangles)
    assert len(stars) == 5 and all(x.bit_count() == 4 for x in stars)
    assert len(triangles) == 10 and all(x.bit_count() == 3 for x in triangles)

    positive_occurrences = [(x, v, x | (1 << v)) for x in mis
                            for v in range(10) if not (x >> v & 1)]
    positives = sorted({z for _, _, z in positive_occurrences})
    positive4 = [x for x in positives if x.bit_count() == 4]
    positive5 = [x for x in positives if x.bit_count() == 5]
    assert len(positive_occurrences) == len(positives) == 100
    assert len(positive4) == 70 and len(positive5) == 30
    assert not (set(mis) & set(positives))
    containment = []
    for x in positive5:
        contained = [z for z in positive4 if z & x == z]
        assert contained
        containment.append({"five_point": x, "four_point_witness": min(contained),
                            "all_four_point_witnesses": contained})

    exposures = []
    for a, b in sorted(tuple(sorted(e)) for e in EDGES):
        witnesses = []
        for x, v, z in positive_occurrences:
            if induced_edges(z) == [[a, b]]:
                witnesses.append({"mis": x, "added_vertex": v, "positive": z})
        assert witnesses
        assert {w["added_vertex"] for w in witnesses} == {a, b}
        assert len(witnesses) == 4
        exposures.append({"edge": [a, b], "witnesses": witnesses})

    covers = [UNIV ^ x for x in indep]
    assert min(x.bit_count() for x in covers) == 6
    assert max(x.bit_count() for x in indep) == 4
    assert all((NEIGHBORS[a] & NEIGHBORS[b]).bit_count() <= 1
               for a in range(10) for b in range(a + 1, 10))

    bicliques = []
    for left in range(1, 1 << 10):
        common = UNIV
        for a in vertices(left):
            common &= NEIGHBORS[a]
        right = common
        while right:
            assert not (left & right)
            assert min(left.bit_count(), right.bit_count()) == 1
            assert left.bit_count() * right.bit_count() == \
                (left | right).bit_count() - 1
            bicliques.append([left, right])
            right = (right - 1) & common
    assert len(bicliques) == 110

    independent_pairs = []
    for a in range(10):
        for b in range(a, 10):
            if NEIGHBORS[a] >> b & 1:
                continue
            pair = (1 << a) | (1 << b)
            ts = [x for x in triangles if x & pair == pair]
            ss = [x for x in stars if x & pair == pair]
            assert ts and ss
            independent_pairs.append({"pair": [a, b],
                                      "triangle_mis": min(ts),
                                      "star_mis": min(ss)})

    report = {
        "status": "EXACT_FINITE_GEOMETRY_AUDIT",
        "scope": "All 1024 vertex subsets; no circuit search or lower-bound certificate.",
        "edges": EDGES,
        "kneser_label_for_each_posted_vertex": KG_LABELS,
        "independent_set_count": len(indep),
        "independent_size_histogram": {
            str(k): sum(x.bit_count() == k for x in indep) for k in range(5)},
        "maximal_independent_sets": [row(x) for x in mis],
        "positive_rows": [row(x) for x in positives],
        "positive_size_histogram": {"4": len(positive4), "5": len(positive5)},
        "positive4_induced_edge_count_histogram": {
            str(k): sum(len(induced_edges(x)) == k for x in positive4)
            for k in [1, 3]},
        "five_point_redundancy_witnesses": containment,
        "unique_edge_exposures": exposures,
        "minimum_vertex_cover": 6,
        "maximum_independent_set": 4,
        "nonempty_ordered_bicliques": bicliques,
        "nonempty_ordered_biclique_count": len(bicliques),
        "independent_pairs_extend_to_both_mis_types": independent_pairs,
        "canonical_triangle_mis": [0, 2, 6],
        "canonical_star_mis": [0, 2, 8, 9],
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (ROOT / "geometry-audit.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "independent": len(indep),
                      "negative_rows": len(mis), "positive_rows": len(positives),
                      "irreducible_positive_rows": len(positive4),
                      "ordered_bicliques": len(bicliques),
                      "script_sha256": report["script_sha256"]}))


if __name__ == "__main__":
    main()
