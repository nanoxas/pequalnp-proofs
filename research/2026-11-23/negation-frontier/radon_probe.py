"""Exact Walsh-slice construction for line sums in PG(2, 2**h).

This is a mathematical/algorithmic audit, not a Lean circuit certificate.
It uses addition and subtraction, so it does not satisfy a monotone AND/OR
task. It helps identify the limits of extrapolating monotone lower bounds.

Reference for the finite Fourier-slice principle:
https://doi.org/10.1049/iet-cvi.2013.0101
The binary-field Walsh implementation and the checks below are local work.
"""

import argparse
import json
import random
from pathlib import Path

MODULI = {1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101, 6: 0b1000011}


def field_mul(a, b, h):
    q = 1 << h
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & q:
            a ^= MODULI[h]
    return result


def fwht(values):
    out = list(values)
    width = 1
    while width < len(out):
        for start in range(0, len(out), 2 * width):
            for j in range(start, start + width):
                a, b = out[j], out[j + width]
                out[j], out[j + width] = a + b, a - b
        width *= 2
    return out


def transpose_mul(a, v, h):
    """u satisfying dot(u,x)=dot(v,a*x) in the chosen binary basis."""
    return sum(((v & field_mul(a, 1 << j, h)).bit_count() & 1) << j for j in range(h))


def projective_lines(h):
    q = 1 << h
    lines = []
    for a in range(q):
        for b in range(q):
            lines.append([x * q + (field_mul(a, x, h) ^ b) for x in range(q)] + [q * q + a])
    for b in range(q):
        lines.append([b * q + y for y in range(q)] + [q * q + q])
    lines.append(list(range(q * q, q * q + q + 1)))
    return lines


def slice_line_sums(values, h, slices):
    q = 1 << h
    spectrum = fwht(values[: q * q])
    result = []
    for direction, indices in enumerate(slices):
        scaled_sums = fwht([spectrum[i] for i in indices])
        for value in scaled_sums:
            assert value % q == 0
            result.append(value // q + values[q * q + direction])
    result.append(sum(values[q * q :]))
    return result


def check_order(h, basis=True, random_cases=12):
    q = 1 << h
    n = q * q + q + 1
    lines = projective_lines(h)
    assert len(lines) == n
    assert all(len(line) == q + 1 and len(set(line)) == q + 1 for line in lines)
    for a in range(1, q):
        assert len({field_mul(a, b, h) for b in range(q)}) == q
    if q <= 16:
        line_sets = [set(line) for line in lines]
        assert all(len(line_sets[i] & line_sets[j]) == 1 for i in range(n) for j in range(i))
    slices = [[transpose_mul(a, v, h) * q + v for v in range(q)] for a in range(q)]
    slices.append([v * q for v in range(q)])
    rng = random.Random(1395 + h)
    inputs = []
    if basis:
        for i in range(n):
            vec = [0] * n
            vec[i] = 1
            inputs.append(vec)
    if q == 2:
        inputs.extend([[int(mask >> i & 1) for i in range(n)] for mask in range(1 << n)])
    inputs.extend([[rng.randrange(2) for _ in range(n)] for _ in range(random_cases)])
    for vec in inputs:
        actual = slice_line_sums(vec, h, slices)
        direct = [sum(vec[p] for p in line) for line in lines]
        assert actual == direct
    return {
        "h": h,
        "q": q,
        "projective_points_and_lines": n,
        "basis_columns_checked": n if basis else 0,
        "total_inputs_checked": len(inputs),
        "matrix_identity_checked": basis,
        "transform_additions_and_subtractions": (3 * q * q + q) * h,
        "conservative_signed_word_bits": 3 * h + 2,
        "separate_line_or_formula_gate_count": q * n,
        "scope": "Exact integer line sums; Boolean compilation and NOT compression not formalized here.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("radon-audit.json"))
    args = parser.parse_args()
    result = {
        "method": "2D Walsh transform, binary-field transpose slices, 1D inverse Walsh transforms, infinity points",
        "orders": [check_order(h, basis=h <= 4) for h in range(1, 7)],
        "interpretation": "The construction uses subtraction and does not refute any monotone task.",
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
