#!/usr/bin/env python3
"""Small, exact truth-table circuit searches for the ownership bottleneck.

No network or task operations. This searches normalized binary AND/OR circuits,
with distinct valid predecessors, a last-gate output, and every gate live.
For a nonconstant graph function a size-minimum circuit admits this form by
constant/alias simplification and deleting unused gates. A UNSAT result about
bad ownership only concerns this normalized representation; SAT witnesses are
verified by a separate direct evaluator, including proper ancestor ownership.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "heawood-search/vendor"))
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver


def evaluate(n, edges, gates):
    """Independent exhaustive function check and strict-cone ownership audit."""
    ancestors = []
    for j, (op, a, b) in enumerate(gates):
        assert op in ("and", "or") and 0 <= a < b < n+j
        cone = set()
        for w in (a, b):
            if w >= n:
                cone.add(w-n)
                cone.update(ancestors[w-n])
        ancestors.append(cone)
    all_values = {}
    wrong = []
    for mask in range(1 << n):
        values = [bool(mask & (1 << i)) for i in range(n)]
        for op, a, b in gates:
            values.append(values[a] and values[b] if op == "and" else values[a] or values[b])
        target = any(mask & (1 << u) and mask & (1 << v) for u, v in edges)
        if values[-1] != bool(target):
            wrong.append(mask)
        all_values[mask] = values
    ownership = []
    critical = []
    for j, (op, _, _) in enumerate(gates):
        if op != "and":
            continue
        owned = []
        needed = []
        for u, v in edges:
            mask = (1 << u) | (1 << v)
            values = all_values[mask]
            if values[n+j] and all(gates[i][0] != "and" or not values[n+i] for i in ancestors[j]):
                owned.append([u, v])
            forced = [bool(mask & (1 << i)) for i in range(n)]
            for i, (o, a, b) in enumerate(gates):
                forced.append(False if i == j else (forced[a] and forced[b] if o == "and" else forced[a] or forced[b]))
            if not forced[-1]:
                needed.append([u, v])
        centers = sorted(set.intersection(*(set(e) for e in owned))) if owned else []
        ownership.append({"gate": j, "wire": n+j, "owned_edges": owned, "centers": centers})
        critical.append({"gate": j, "critical_edges": needed})
    return {"rows_checked": 1 << n, "wrong_rows": wrong, "ownership": ownership,
            "criticality": critical, "has_empty_owner": any(not r["owned_edges"] for r in ownership),
            "has_nonstar_owner": any(r["owned_edges"] and not r["centers"] for r in ownership)}


class Encoding:
    def __init__(self, n, edges, size, prop="any", ordered=True):
        self.n, self.edges, self.size, self.prop = n, edges, size, prop
        self.pool, self.cnf = IDPool(), CNF()
        self.ops = [self.var(("and", j)) for j in range(size)]
        self.sel = [[[self.var(("sel", j, p, w)) for w in range(n+j)] for p in (0,1)] for j in range(size)]
        self.val = [[self.var(("val", j, mask)) for mask in range(1 << n)] for j in range(size)]
        self.true = self.var(("constant", True)); self.add(self.true)
        self.false = -self.true
        for j in range(size):
            for choices in self.sel[j]:
                self.cnf.extend(CardEnc.equals(choices, bound=1, vpool=self.pool, encoding=EncType.seqcounter).clauses)
            for a in range(n+j):
                for b in range(a+1):
                    self.add(-self.sel[j][0][a], -self.sel[j][1][b])
            if ordered and j:
                for a in range(n+j-1):
                    for b in range(a):
                        self.add(-self.sel[j-1][1][a], -self.sel[j][1][b])
            for mask in range(1 << n):
                inputs = []
                for p in (0,1):
                    value = self.var(("input", j, p, mask))
                    for w, selected in enumerate(self.sel[j][p]):
                        prev = (self.true if mask & (1 << w) else self.false) if w < n else self.val[w-n][mask]
                        self.add(-selected, -value, prev)
                        self.add(-selected, value, -prev)
                    inputs.append(value)
                a,b = inputs; z = self.val[j][mask]; op = self.ops[j]
                self.add(-op, -z, a); self.add(-op, -z, b); self.add(-op, z, -a, -b)
                self.add(op, z, -a); self.add(op, z, -b); self.add(op, -z, a, b)
        for mask in range(1 << n):
            target = any(mask & (1 << u) and mask & (1 << v) for u, v in edges)
            self.add(self.val[-1][mask] if target else -self.val[-1][mask])
        for i in range(size-1):
            self.add(*(self.sel[j][p][n+i] for j in range(i+1,size) for p in (0,1)))
        if prop != "any":
            self.add_ownership()

    def var(self, key):
        return self.pool.id(key)

    def add(self, *clause):
        self.cnf.append(list(clause))

    def conjunction(self, literals, key):
        literals = list(literals)
        out = self.var(key)
        for lit in literals:
            self.add(-out, lit)
        self.add(out, *(-lit for lit in literals))
        return out

    def disjunction(self, literals, key):
        return -self.conjunction((-lit for lit in literals), key)

    def add_ownership(self):
        n,size = self.n,self.size
        uses = {}
        for j in range(size):
            for i in range(j):
                uses[j,i] = self.disjunction([self.sel[j][0][n+i], self.sel[j][1][n+i]], ("uses",j,i))
        reach = {}
        for j in range(size):
            for i in range(j):
                terms = [uses[j,i]]
                for p in range(i+1,j):
                    terms.append(self.conjunction([uses[j,p], reach[p,i]], ("path",j,p,i)))
                reach[j,i] = self.disjunction(terms, ("ancestor",j,i))
        owns = {}
        for j in range(size):
            for e,(u,v) in enumerate(self.edges):
                mask = (1 << u) | (1 << v)
                terms = [self.ops[j], self.val[j][mask]]
                for i in range(j):
                    inherited = self.conjunction([reach[j,i], self.ops[i], self.val[i][mask]], ("inherited",j,i,e))
                    terms.append(-inherited)
                owns[j,e] = self.conjunction(terms, ("owns",j,e))
        witnesses = []
        for j in range(size):
            if self.prop == "empty":
                terms = [self.ops[j]] + [-owns[j,e] for e in range(len(self.edges))]
            elif self.prop == "nonstar":
                terms = [self.ops[j]]
                for v in range(n):
                    terms.append(self.disjunction([owns[j,e] for e,edge in enumerate(self.edges) if v not in edge], ("not_center",j,v)))
            elif self.prop == "good":
                centers = []
                for v in range(n):
                    centers.append(self.conjunction([-owns[j,e] for e,edge in enumerate(self.edges) if v not in edge], ("center",j,v)))
                nonempty = self.disjunction([owns[j,e] for e in range(len(self.edges))], ("nonempty",j))
                self.add(-self.ops[j], nonempty)
                self.add(-self.ops[j], *centers)
                continue
            else:
                raise ValueError(self.prop)
            witnesses.append(self.conjunction(terms, ("property",j)))
        if self.prop != "good":
            self.add(*witnesses)

    def decode(self, model):
        positive = set(x for x in model if x > 0)
        return [["and" if self.ops[j] in positive else "or"] +
                [next(w for w,s in enumerate(self.sel[j][p]) if s in positive) for p in (0,1)]
                for j in range(self.size)]


def run(n, edges, size, prop="any", conflicts=2_000_000, ordered=True):
    start = time.monotonic()
    encoding = Encoding(n, edges, size, prop, ordered)
    with Solver(name="cadical300", bootstrap_with=encoding.cnf.clauses, use_timer=True) as solver:
        solver.conf_budget(conflicts)
        answer = solver.solve_limited()
        out = {"n": n, "edges": edges, "size": size, "property": prop,
               "status": "SAT" if answer is True else "UNSAT" if answer is False else "UNKNOWN",
               "seconds": time.monotonic()-start, "solver_stats": solver.accum_stats(),
               "variables": encoding.pool.top, "clauses": len(encoding.cnf.clauses),
               "restrictions": ["binary distinct valid predecessors", "last gate output", "all gates live"]+
                               (["nondecreasing largest predecessor"] if ordered else [])}
        if answer:
            gates = encoding.decode(solver.get_model())
            audit = evaluate(n, edges, gates)
            assert not audit["wrong_rows"]
            if prop == "empty": assert audit["has_empty_owner"]
            if prop == "nonstar": assert audit["has_nonstar_owner"]
            if prop == "good": assert not audit["has_empty_owner"] and not audit["has_nonstar_owner"]
            out.update({"gates": gates, "audit": audit})
        return out


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--n", type=int, required=True)
    p.add_argument("--edges", required=True, help="JSON list of unordered input-index pairs")
    p.add_argument("--size", type=int, required=True)
    p.add_argument("--property", choices=["any","empty","nonstar","good"], default="any")
    p.add_argument("--conflicts", type=int, default=2_000_000)
    p.add_argument("--unordered", action="store_true")
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    edges = sorted(tuple(sorted(e)) for e in json.loads(args.edges))
    assert args.n > 1 and args.size > 0 and edges and len(set(edges)) == len(edges)
    assert all(0 <= u < v < args.n for u,v in edges)
    result = run(args.n, edges, args.size, args.property, args.conflicts, not args.unordered)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k not in ("gates","audit")},indent=2),flush=True)
    if "gates" in result:
        print(json.dumps({"gates":result["gates"],"ownership":result["audit"]["ownership"]},indent=2),flush=True)


if __name__ == "__main__":
    main()
