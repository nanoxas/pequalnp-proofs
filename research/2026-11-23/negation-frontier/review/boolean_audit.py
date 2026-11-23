#!/usr/bin/env python3
"""Independent Boolean compilation audit of the binary-field Walsh proposal.

Only AND2, OR2, NOT1 and constants are primitive. Arithmetic is modulo 2**B.
The dual-rail circuit has no NOT gates. A separate explicit sorting-network
inverter supplies point complements with ceil(log2(n+1)) NOT gates and
O(n log^2 n) total gates. This is not the published BNT O(n log n) inverter.
"""

from collections import Counter
import json
from pathlib import Path
import random


MODULI = {1: 3, 2: 7, 3: 11, 4: 19, 5: 37, 6: 67}


def mul(a, b, h):
    """Carryless polynomial product followed by long-division reduction."""
    product = 0
    for i in range(h):
        if (b >> i) & 1:
            product ^= a << i
    for i in range(2 * h - 2, h - 1, -1):
        if (product >> i) & 1:
            product ^= MODULI[h] << (i - h)
    return product


def direct_lines(h):
    q = 1 << h
    return (
        [[x * q + (mul(a, x, h) ^ b) for x in range(q)] + [q*q+a]
         for a in range(q) for b in range(q)]
        + [[b*q+y for y in range(q)] + [q*q+q] for b in range(q)]
        + [list(range(q*q, q*q+q+1))]
    )


class Net:
    def __init__(self, inputs):
        self.inputs = inputs
        self.zero, self.one = inputs, inputs + 1
        self.gates = []

    def gate(self, op, *xs):
        assert len(xs) == (1 if op == 'not' else 2)
        index = self.inputs + 2 + len(self.gates)
        assert all(0 <= x < index for x in xs)
        self.gates.append((op, xs))
        return index

    def xor(self, a, b):
        either = self.gate('or', a, b)
        both = self.gate('and', a, b)
        neither_both = self.gate('not', both)
        return self.gate('and', either, neither_both)

    def add(self, a, b, carry=None):
        assert len(a) == len(b)
        carry = self.zero if carry is None else carry
        result = []
        for i, (x, y) in enumerate(zip(a, b)):
            propagate = self.xor(x, y)
            result.append(self.xor(propagate, carry))
            if i + 1 < len(a):
                generate = self.gate('and', x, y)
                passed = self.gate('and', propagate, carry)
                carry = self.gate('or', generate, passed)
        return result

    def subtract(self, a, b):
        return self.add(a, [self.gate('not', bit) for bit in b], self.one)

    def or_all(self, xs):
        if not xs:
            return self.zero
        xs = list(xs)
        while len(xs) > 1:
            xs = [self.gate('or', xs[i], xs[i+1]) if i+1 < len(xs) else xs[i]
                  for i in range(0, len(xs), 2)]
        return xs[0]

    def evaluate_packed(self, inputs, rows):
        assert len(inputs) == self.inputs
        mask = (1 << rows) - 1
        values = list(inputs) + [0, mask]
        for op, xs in self.gates:
            if op == 'and':
                value = values[xs[0]] & values[xs[1]]
            elif op == 'or':
                value = values[xs[0]] | values[xs[1]]
            else:
                value = values[xs[0]] ^ mask
            values.append(value)
        return values


def word_walsh(net, words):
    out = list(words)
    width = 1
    while width < len(out):
        for start in range(0, len(out), 2 * width):
            for i in range(start, start + width):
                a, b = out[i], out[i+width]
                out[i], out[i+width] = net.add(a, b), net.subtract(a, b)
        width *= 2
    return out


def build(h):
    q = 1 << h
    n = q*q + q + 1
    bits = 3*h + 2
    net = Net(n)
    words = [[i] + [net.zero]*(bits-1) for i in range(n)]
    spectrum = word_walsh(net, words[:q*q])
    indices = []
    for a in range(q):
        transpose = [sum((((v & mul(a, 1 << j, h)).bit_count() & 1) << j)
                         for j in range(h)) for v in range(q)]
        indices.append([u*q+v for v, u in enumerate(transpose)])
    indices.append([v*q for v in range(q)])
    line_words = []
    for direction, ids in enumerate(indices):
        scaled = word_walsh(net, [spectrum[i] for i in ids])
        for word in scaled:
            # True scaled sums are nonnegative, divisible by q, and <2**bits.
            divided = word[h:] + [net.zero]*h
            line_words.append(net.add(divided, words[q*q+direction]))
    infinity = [net.zero]*bits
    for word in words[q*q:]:
        infinity = net.add(infinity, word)
    line_words.append(infinity)
    nonzero = [net.or_all(word) for word in line_words]
    return net, line_words, nonzero


def dual_rail(source):
    """First n rails are x; next n rails are externally supplied not-x."""
    target = Net(2 * source.inputs)
    rails = [(i, i + source.inputs) for i in range(source.inputs)]
    rails += [(target.zero, target.one), (target.one, target.zero)]
    for op, xs in source.gates:
        if op == 'not':
            a, b = rails[xs[0]]
            rails.append((b, a))
        else:
            a, an = rails[xs[0]]
            b, bn = rails[xs[1]]
            opposite = 'or' if op == 'and' else 'and'
            rails.append((target.gate(op, a, b), target.gate(opposite, an, bn)))
    assert all(op != 'not' for op, _ in target.gates)
    return target, rails


def bitplanes(assignments, inputs):
    return [sum(((assignment >> i) & 1) << row
                for row, assignment in enumerate(assignments))
            for i in range(inputs)]


def sorting_inverter(n):
    """Explicit optimal-NOT-count inverter; total size O(n log^2 n)."""
    net = Net(n)
    k = n.bit_length()
    size = 1 << k  # Strictly greater than n, including when n is a power of2.
    wires = list(range(n)) + [net.zero] * (size - n)
    comparators = []
    span = 2
    while span <= size:
        stride = span // 2
        while stride:
            for i in range(size):
                j = i ^ stride
                if j <= i:
                    continue
                a, b = wires[i], wires[j]
                low = net.gate('and', a, b)
                high = net.gate('or', a, b)
                comparators.append((a, b, low, high))
                wires[i], wires[j] = ((low, high) if (i & span) == 0 else (high, low))
            stride //= 2
        span *= 2
    thresholds = [net.one] + [wires[size-j] for j in range(1, size)] + [net.zero]
    complements = {0: net.zero, size: net.one}
    weight_bit_complements = []
    for r in range(k-1, -1, -1):
        width = 1 << (r+1)
        intervals = [(lo, lo+width//2, lo+width) for lo in range(0, size, width)]
        bits = [net.gate('and', thresholds[mid], complements[hi])
                for lo, mid, hi in intervals]
        bit = net.or_all(bits)
        not_bit = net.gate('not', bit)
        weight_bit_complements.append(not_bit)
        for lo, mid, hi in intervals:
            middle = net.gate('and', not_bit, complements[hi])
            complements[mid] = net.gate('or', complements[lo], middle)
    negative = {wire: complements[size-i] for i, wire in enumerate(wires)}
    for a, b, low, high in reversed(comparators):
        not_low, not_high = negative[low], negative[high]
        negative[a] = net.gate('or', not_high, net.gate('and', b, not_low))
        negative[b] = net.gate('or', not_high, net.gate('and', a, not_low))
    outputs = [negative[i] for i in range(n)]
    count = Counter(op for op, _ in net.gates)
    assert count['not'] == k
    assert len(comparators) == size*k*(k+1)//4
    assert len(net.gates) == 6*len(comparators) + 4*(size-1)
    return net, outputs, {
        'inputs': n, 'padded_sorting_length': size, 'NOT_gates': k,
        'comparators': len(comparators), 'total_gates': len(net.gates),
        'gate_counts': dict(count),
        'method': 'bitonic sorter, complemented dyadic thresholds, reversed comparators',
    }


def audit_inverter(n):
    net, outputs, metadata = sorting_inverter(n)
    rows = 1 << n
    planes = bitplanes(range(rows), n)
    values = net.evaluate_packed(planes, rows)
    rowmask = (1 << rows)-1
    assert all(values[output] == planes[i] ^ rowmask for i, output in enumerate(outputs))
    return dict(metadata, all_assignments_checked=rows, outputs_correct=True)


def append_net(target, source, inputs):
    assert len(inputs) == source.inputs
    mapping = list(inputs) + [target.zero, target.one]
    for op, xs in source.gates:
        mapping.append(target.gate(op, *(mapping[x] for x in xs)))
    return mapping


def audit(h):
    q = 1 << h
    n = q*q+q+1
    net, line_words, nonzero = build(h)
    dual, rails = dual_rail(net)
    rng = random.Random(139500 + h)
    if h == 1:
        assignments = list(range(1 << (2*n)))
        scope = 'all point and line assignments'
    else:
        assignments = [0, (1 << (2*n))-1]
        assignments += [(1 << i) | (1 << (n+j))
                        for i in range(n) for j in range(n)] if h == 2 else []
        assignments += [rng.getrandbits(2*n) for _ in range(256)]
        scope = 'extreme and random full assignments; all singleton pairs also for q=4'
    planes = bitplanes(assignments, 2*n)
    rowmask = (1 << len(assignments)) - 1
    source_values = net.evaluate_packed(planes[:n], len(assignments))
    target_values = dual.evaluate_packed(
        planes[:n] + [x ^ rowmask for x in planes[:n]], len(assignments))
    inverter, negative_outputs, inverter_info = sorting_inverter(n)
    complete = Net(2*n)
    inv_map = append_net(complete, inverter, list(range(n)))
    dual_map = append_net(complete, dual,
                          list(range(n)) + [inv_map[o] for o in negative_outputs])
    line_hits = [dual_map[rails[o][0]] for o in nonzero]
    final_output = complete.or_all([complete.gate('and', hit, n+i)
                                    for i, hit in enumerate(line_hits)])
    complete_values = complete.evaluate_packed(planes, len(assignments))
    lines = direct_lines(h)
    total_positive = 0
    total_reference = 0
    for line_id, points in enumerate(lines):
        reference = 0
        for p in points:
            reference |= planes[p]
        actual = source_values[nonzero[line_id]]
        converted = target_values[rails[nonzero[line_id]][0]]
        actual_complete = complete_values[line_hits[line_id]]
        assert actual == converted == actual_complete == reference
        total_positive |= actual & planes[n+line_id]
        total_reference |= reference & planes[n+line_id]
        for row, assignment in enumerate(assignments):
            actual_sum = sum(((source_values[bit] >> row) & 1) << i
                             for i, bit in enumerate(line_words[line_id]))
            expected_sum = sum((assignment >> p) & 1 for p in points)
            assert actual_sum == expected_sum
    assert total_positive == total_reference
    assert complete_values[final_output] == total_reference
    assert all(target_values[pos] ^ target_values[neg] == rowmask for pos, neg in rails)
    raw_counts = Counter(op for op, _ in net.gates)
    dual_counts = Counter(op for op, _ in dual.gates)
    complete_counts = Counter(op for op, _ in complete.gates)
    assert complete_counts['not'] == 2*h+1
    expected_size = q*q*(174*h*h+168*h+48) + q*(54*h*h+144*h+64) + 60*h+29
    assert len(complete.gates) == expected_size
    return {
        'h': h, 'q': q, 'N': n, 'word_bits': 3*h+2,
        'assignments_checked': len(assignments), 'scope': scope,
        'raw_gate_counts': dict(raw_counts),
        'dual_rail_gate_counts_excluding_external_inverter': dict(dual_counts),
        'final_positive_line_selection_gates': 2*n-1,
        'explicit_sorting_inverter': inverter_info,
        'complete_circuit_gate_counts': dict(complete_counts),
        'complete_circuit_size': len(complete.gates),
        'complete_size_if_two_constants_are_charged': len(complete.gates)+2,
        'complete_circuit_NOT_count': 2*h+1,
        'all_line_sums_match': True, 'all_dual_rails_complementary': True,
        'incidence_output_matches': True,
        'formal_certificate': False,
        'sorting_inverter_implemented': True,
        'BNT_inverter_implemented': False,
    }


if __name__ == '__main__':
    result = {
        'method': 'Explicit ripple-carry Boolean words; independent polynomial field multiplication; dual-rail conversion',
        'primitive_gate_set': ['AND fanin2', 'OR fanin2', 'NOT fanin1', 'constants'],
        'gate_count_convention': 'Constants are free in reported raw counts; add at most2 gates if constant0 and constant1 must be charged.',
        'inverter_exhaustive_tests': [audit_inverter(n) for n in range(11)],
        'tests': [audit(h) for h in range(1,4)],
        'scope_warning': 'Finite executable validation of the full compiler including an explicit sorting inverter; universal correctness follows the accompanying paper derivation. No Lean certificate. The O(n log n) BNT inverter is not implemented; our O(n log^2 n) inverter suffices for the same final asymptotic.',
    }
    path = Path(__file__).with_name('boolean-audit.json')
    path.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
