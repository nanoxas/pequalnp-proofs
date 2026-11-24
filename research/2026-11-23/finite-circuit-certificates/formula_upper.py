#!/usr/bin/env python3
"""Five-input monotone upper witnesses, with independent full-table evaluation.

Dynamic programming minimizes formula cost among discovered functions. Sharing
equal subfunctions then yields a circuit witness. Formula cost is never treated
as a circuit lower bound. The DNF baseline guarantees a witness for every
monotone table even if the bounded formula search stops early.
"""
from __future__ import annotations

import time

ALL = (1 << 32) - 1
VARIABLES = [sum(((row >> i) & 1) << row for row in range(32)) for i in range(5)]


def monotone(table):
    return all(not (table >> row & 1) or all(table >> (row | (1 << i)) & 1 for i in range(5))
               for row in range(32))


def essential_variables(table):
    return [any(bool(table >> row & 1) != bool(table >> (row ^ (1 << i)) & 1) for row in range(32))
            for i in range(5)]


def evaluate(witness):
    wires = VARIABLES.copy()
    for j, gate in enumerate(witness["gates"]):
        op, inputs = gate["op"], gate["inputs"]
        if op not in ("and", "or") or len(inputs) > 2:
            raise ValueError(f"Gate {j} is not a monotone fan-in-two gate")
        if any(type(w) is not int or w < 0 or w >= len(wires) for w in inputs):
            raise ValueError(f"Gate {j} reads an unavailable wire")
        value = ALL if op == "and" else 0
        for w in inputs:
            value = value & wires[w] if op == "and" else value | wires[w]
        wires.append(value)
    output = witness["output"]
    if type(output) is not int or not 0 <= output < len(wires):
        raise ValueError("Output wire is unavailable")
    return wires[output]


class Builder:
    def __init__(self):
        self.gates = []
        self.wire_values = VARIABLES.copy()
        self.by_value = {value:i for i,value in enumerate(VARIABLES)}

    def gate(self, op, inputs):
        value = ALL if op == "and" else 0
        for w in inputs:
            value = value & self.wire_values[w] if op == "and" else value | self.wire_values[w]
        if value in self.by_value:
            return self.by_value[value]
        wire = 5 + len(self.gates)
        self.gates.append({"op":op,"inputs":list(inputs)})
        self.wire_values.append(value)
        self.by_value[value] = wire
        return wire

    def combine(self, op, inputs):
        inputs = list(inputs)
        if not inputs:
            return self.gate(op, ())
        result = inputs[0]
        for w in inputs[1:]:
            result = self.gate(op, (result,w))
        return result

    def finish(self, output):
        # Drop gates rendered unnecessary by semantic sharing, then reindex.
        needed = set()
        def visit(w):
            if w < 5 or w in needed:
                return
            needed.add(w)
            for a in self.gates[w-5]["inputs"]:
                visit(a)
        visit(output)
        remap = {i:i for i in range(5)}
        gates = []
        for j,g in enumerate(self.gates):
            old = 5+j
            if old in needed:
                remap[old] = 5+len(gates)
                gates.append({"op":g["op"],"inputs":[remap[a] for a in g["inputs"]]})
        return {"gates":gates,"output":remap[output]}


def baseline(table):
    if not monotone(table):
        raise ValueError("Truth table is not monotone")
    builder = Builder()
    minimal = [row for row in range(32) if table >> row & 1 and
               all(not (table >> (row ^ (1 << i)) & 1) for i in range(5) if row >> i & 1)]
    terms = [builder.combine("and",(i for i in range(5) if row >> i & 1)) for row in minimal]
    witness = builder.finish(builder.combine("or",terms))
    assert evaluate(witness) == table
    return witness


def generate(tables, max_cost=16, seconds=60):
    started = time.monotonic()
    tables = list(tables)
    if any(type(t) is not int or not 0 <= t <= ALL or not monotone(t) for t in tables):
        raise ValueError("All tables must be monotone unsigned 32-bit integers")
    best = {t:("input",i) for i,t in enumerate(VARIABLES)}
    best[0], best[ALL] = ("const",0), ("const",1)
    levels = [list(best)]
    log = []
    stopped = "all_targets_found" if all(t in best for t in tables) else "formula_cost_limit"
    for cost in range(1,max_cost+1):
        if all(t in best for t in tables):
            stopped = "all_targets_found"
            break
        if time.monotonic()-started > seconds:
            stopped = "time_limit"
            break
        new = []
        timed_out = False
        for p in range((cost-1)//2+1):
            q = cost-1-p
            if q >= len(levels):
                continue
            left,right = levels[p],levels[q]
            for ia,a in enumerate(left):
                if time.monotonic()-started > seconds:
                    timed_out = True
                    break
                rb = right[:ia+1] if p == q else right
                for b in rb:
                    for op,z in (("and",a & b),("or",a | b)):
                        if z not in best:
                            best[z] = (op,a,b)
                            new.append(z)
            if timed_out:
                break
        levels.append(new)
        log.append({"formula_cost":cost,"new_functions":len(new),"targets_found":sum(t in best for t in tables)})
        if timed_out:
            stopped = "time_limit"
            break
    if all(t in best for t in tables):
        stopped = "all_targets_found"

    results = []
    for table in tables:
        witness = baseline(table)
        if table in best:
            builder = Builder()
            cache = {}
            def emit(t):
                if t in cache:
                    return cache[t]
                data = best[t]
                if data[0] == "input":
                    wire = data[1]
                elif data[0] == "const":
                    wire = builder.gate("and" if data[1] else "or",())
                else:
                    wire = builder.gate(data[0],(emit(data[1]),emit(data[2])))
                cache[t] = wire
                return wire
            candidate = builder.finish(emit(table))
            assert evaluate(candidate) == table
            if len(candidate["gates"]) < len(witness["gates"]):
                witness = candidate
        results.append({"truth_table":hex(table),**witness})
    return {"scope":"Upper witnesses only; formula cost does not establish circuit optimality.",
            "seconds":time.monotonic()-started,"stopped":stopped,"levels":log,"tables":results}
