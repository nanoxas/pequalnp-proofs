#!/usr/bin/env python3
"""Complete bounded circuit search for the ten public L-meta-1418 tables.

Rows are all32 assignments, variable0 the low-order assignment bit.
The model has five inputs, free constant0/1, exactly k binary AND/OR or
unary NOT slots, equal fanins, and dead slots. At most one slot may be NOT.
The final slot is the output. Any circuit of size<=k can be padded with
AND(output,output), so this is a complete superset for bounded UNSAT.

Project list gates with zero/one inputs and invalid/future references map
to this model without extra slots: invalid reads are false; empty AND is
true; empty OR is false; empty NOT is true; a one-input AND/OR is an alias;
NOT reads only its first input. This model permits free constants, which
can only make its UNSAT result stronger. SAT witnesses are simplified and
independently evaluated without the CNF evaluator before being reported.

The symmetry rules sort commutative fanins, duplicate the unused NOT port,
and (optionally) order gates by maximum fanin. Greedy topological scheduling
proves the last rule complete: existing ready gates have maximum fanin no
smaller than the last chosen one; newly ready gates read the latest output,
whose index is larger. Pruning unused gates before padding the output by
aliases preserves final-output form. No semantic pruning is used.
"""

from pathlib import Path
import argparse
import functools
import hashlib
import json
import resource
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'heawood-search/vendor'))
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

TABLES = [0xe8808080,0xa8888880,0xa888a080,0xe8808880,0xe888a000,
          0xa8888888,0xa888a880,0xa8a8a800,0xe880a880,0xe8888880]
ALL = (1 << 32) - 1
N = 5


def reduce_terms(terms):
    terms = set(terms)
    return tuple(sorted(t for t in terms if not any(s != t and s & t == s for s in terms)))


def node(op, a, b):
    if a == b:
        return a
    if op == 'and':
        if a == ('const', 0) or b == ('const', 0): return ('const', 0)
        if a == ('const', 1): return b
        if b == ('const', 1): return a
    else:
        if a == ('const', 1) or b == ('const', 1): return ('const', 1)
        if a == ('const', 0): return b
        if b == ('const', 0): return a
    a, b = sorted((a, b), key=repr)
    return (op, a, b)


def expr_cost(expr):
    seen = set()
    def visit(e):
        if e[0] in ('var', 'const') or e in seen: return
        seen.add(e)
        visit(e[1]); visit(e[2])
    visit(expr)
    return len(seen)


@functools.lru_cache(None)
def factor(terms):
    if not terms: return ('const', 0)
    if terms == (0,): return ('const', 1)
    candidates = []
    for v in range(N):
        if not any(t >> v & 1 for t in terms): continue
        yes = reduce_terms(t & ~(1 << v) for t in terms if t >> v & 1)
        no = reduce_terms(t for t in terms if not (t >> v & 1))
        candidates.append(node('or', factor(no), node('and', ('var', v), factor(yes))))
    return min(candidates, key=lambda e: (expr_cost(e), repr(e)))


def dual_expr(e):
    if e[0] == 'var': return e
    if e[0] == 'const': return ('const', 1 - e[1])
    return node('or' if e[0] == 'and' else 'and', dual_expr(e[1]), dual_expr(e[2]))


def minterms(T):
    return reduce_terms(mask for mask in range(32) if T >> mask & 1)


def baseline(T):
    dual = sum((1 - ((T >> (31 ^ m)) & 1)) << m for m in range(32))
    expr = min((factor(minterms(T)), dual_expr(factor(minterms(dual)))),
               key=lambda e: (expr_cost(e), repr(e)))
    gates, cache = [], {}
    def emit(e):
        if e[0] == 'var': return e[1]
        if e[0] == 'const': return 5 + e[1]
        if e in cache: return cache[e]
        a, b = emit(e[1]), emit(e[2])
        w = 7 + len(gates)
        gates.append([e[0], a, b]); cache[e] = w
        return w
    out = emit(expr)
    return normalize(gates, out)


def normalize(gates, output):
    """Eliminate free constants, aliases, duplicate gates and dead gates.

    Returned circuit uses five inputs and ordinary project gate numbering.
    Targets in this shard are nonconstant, so no constant gate is needed.
    """
    values = {i: ('wire', i) for i in range(5)}
    values[5], values[6] = ('const', False), ('const', True)
    built, cache = [], {}
    def make(op, a, b):
        if op == 'not':
            if a[0] == 'const': return ('const', not a[1])
            key = ('not', a[1], a[1])
        else:
            if a == b: return a
            if a[0] == 'const':
                return b if a[1] == (op == 'and') else a
            if b[0] == 'const':
                return a if b[1] == (op == 'and') else b
            x, y = sorted((a[1], b[1])); key = (op, x, y)
        if key in cache: return ('wire', cache[key])
        w = 5 + len(built); built.append(list(key)); cache[key] = w
        return ('wire', w)
    for i, (op, a, b) in enumerate(gates):
        assert a < 7+i and b < 7+i
        values[7+i] = make(op, values[a], values[b])
    ans = values[output]
    assert ans[0] == 'wire', 'Shard target unexpectedly constant'
    used = set()
    def mark(w):
        if w < 5 or w-5 in used: return
        j = w-5; used.add(j)
        op, a, b = built[j]; mark(a)
        if op != 'not': mark(b)
    mark(ans[1])
    remap = {i: i for i in range(5)}; live = []
    for j, (op, a, b) in enumerate(built):
        if j not in used: continue
        remap[5+j] = 5+len(live)
        live.append([op, remap[a], remap[a] if op == 'not' else remap[b]])
    return {'gates': live, 'output': remap[ans[1]]}


def truth(circuit):
    """Independent plain Boolean evaluator, with no CNF value variables."""
    T = 0
    for row in range(32):
        wires = [bool(row >> i & 1) for i in range(5)]
        for op, a, b in circuit['gates']:
            assert 0 <= a < len(wires) and 0 <= b < len(wires)
            if op == 'and': z = wires[a] and wires[b]
            elif op == 'or': z = wires[a] or wires[b]
            elif op == 'not': z = not wires[a]
            else: raise ValueError(op)
            wires.append(z)
        T |= int(wires[circuit['output']]) << row
    return T


class Encoding:
    def __init__(self, T, k, not_budget, order=True, gate_order=True):
        self.T, self.k, self.not_budget = T, k, not_budget
        self.pool, self.cnf = IDPool(), CNF()
        self.ops = [[self.v(('op', i, q)) for q in range(3)] for i in range(k)]
        self.sel = [[[self.v(('sel', i, side, w)) for w in range(7+i)]
                     for side in range(2)] for i in range(k)]
        self.val = [[self.v(('val', i, row)) for row in range(32)] for i in range(k)]
        for i in range(k):
            self.one(self.ops[i])
            for side in self.sel[i]: self.one(side)
            # NOT ignores its second argument, so it may be duplicated.
            for w in range(7+i):
                self.add(-self.ops[i][2], -self.sel[i][0][w], self.sel[i][1][w])
            if order:
                for a in range(7+i):
                    for b in range(a):
                        self.add(-self.sel[i][0][a], -self.sel[i][1][b])
            if order and gate_order and i:
                for old in range(7+i-1):
                    for new in range(old):
                        self.add(-self.sel[i-1][1][old], -self.sel[i][1][new])
            for row in range(32):
                x, y = self.v(('x', i, row)), self.v(('y', i, row))
                z = self.val[i][row]
                for side, value in [(0, x), (1, y)]:
                    for w, select in enumerate(self.sel[i][side]):
                        if w < 7:
                            c = bool(row >> w & 1) if w < 5 else w == 6
                            self.add(-select, value if c else -value)
                        else:
                            p = self.val[w-7][row]
                            self.add(-select, -value, p); self.add(-select, value, -p)
                a, o, neg = self.ops[i]
                self.add(-a, -x, -y, z); self.add(-a, x, -z); self.add(-a, y, -z)
                self.add(-o, x, y, -z); self.add(-o, -x, z); self.add(-o, -y, z)
                self.add(-neg, x, z); self.add(-neg, -x, -z)
        nots = [op[2] for op in self.ops]
        if not_budget == 0:
            for lit in nots: self.add(-lit)
        elif not_budget < len(nots):
            self.cnf.extend(CardEnc.atmost(nots, bound=not_budget, vpool=self.pool,
                                          encoding=EncType.seqcounter).clauses)
        if k:
            for row in range(32): self.add(self.val[-1][row] if T >> row & 1 else -self.val[-1][row])

    def v(self, key): return self.pool.id(key)
    def add(self, *lits): self.cnf.append(list(lits))
    def one(self, lits):
        self.cnf.extend(CardEnc.equals(lits, bound=1, vpool=self.pool,
                                      encoding=EncType.seqcounter).clauses)

    def solve(self, budget, solver='cadical300'):
        started = time.monotonic()
        if self.k == 0:
            tables = [sum(((m >> i) & 1) << m for m in range(32)) for i in range(5)] + [0, ALL]
            return {'status': 'SAT' if self.T in tables else 'UNSAT', 'seconds': 0,
                    'variables': 0, 'clauses': 0, 'stats': {}}
        with Solver(name=solver, bootstrap_with=self.cnf.clauses) as s:
            s.conf_budget(budget)
            ans = s.solve_limited(expect_interrupt=True)
            result = {'status': 'SAT' if ans is True else 'UNSAT' if ans is False else 'UNKNOWN',
                      'seconds': time.monotonic()-started, 'variables': self.pool.top,
                      'clauses': len(self.cnf.clauses), 'stats': s.accum_stats()}
            if ans is True:
                model = set(lit for lit in s.get_model() if lit > 0)
                gates = []
                for i in range(self.k):
                    op = ['and', 'or', 'not'][next(q for q, lit in enumerate(self.ops[i]) if lit in model)]
                    a, b = [next(w for w, lit in enumerate(side) if lit in model) for side in self.sel[i]]
                    gates.append([op, a, b])
                c = normalize(gates, 7+self.k-1)
                assert truth(c) == self.T
                assert sum(g[0] == 'not' for g in c['gates']) <= self.not_budget
                assert len(c['gates']) <= self.k
                result['circuit'] = c
            return result


def search_one(T, budget, order=True, gate_order=True, seed=None):
    mono = seed or baseline(T)
    assert truth(mono) == T and all(g[0] != 'not' for g in mono['gates'])
    assert all(not (T >> m & 1) or all(T >> (m | (1 << i)) & 1 for i in range(5)) for m in range(32))
    record = {'table': f'0x{T:08x}', 'monotone_upper': mono, 'queries': [], 'status': 'UNKNOWN'}
    while True:
        M = len(mono['gates']); k = M-1
        q = Encoding(T, k, 1, order, gate_order).solve(budget)
        q.update({'gates_bound': k, 'not_budget': 1})
        record['queries'].append(q)
        if q['status'] == 'UNKNOWN': break
        if q['status'] == 'UNSAT':
            record.update(status='EXHAUSTED', minimum_size=M)
            break
        c = q['circuit']
        if not any(g[0] == 'not' for g in c['gates']):
            mono = c; record['monotone_upper'] = mono
            continue
        k = len(c['gates'])
        m = Encoding(T, k, 0, order, gate_order).solve(budget)
        m.update({'gates_bound': k, 'not_budget': 0})
        record['queries'].append(m)
        if m['status'] == 'SAT':
            mono = m['circuit']; record['monotone_upper'] = mono
            continue
        if m['status'] == 'UNSAT':
            record.update(status='COUNTEREXAMPLE', one_not_witness=c,
                          witness_size=k, monotone_lower_bound=k+1)
        break
    return record


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--budget', type=int, default=200000)
    p.add_argument('--table', type=lambda s: int(s, 0), action='append')
    p.add_argument('--no-fanin-order', action='store_true')
    p.add_argument('--no-gate-order', action='store_true')
    p.add_argument('--seed-results', type=Path)
    p.add_argument('--output', type=Path, default=Path(__file__).with_name('results.json'))
    args = p.parse_args()
    resource.setrlimit(resource.RLIMIT_AS, (768 << 20, 768 << 20))
    records = []
    seeds = {}
    if args.seed_results:
        for r in json.loads(args.seed_results.read_text())['tables']:
            seeds[int(r['table'], 0)] = r['monotone_upper']
    result = {'task': 'L-meta-1418', 'tables': [], 'all_exhausted': False,
              'code_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'budget': args.budget, 'fanin_order': not args.no_fanin_order,
              'gate_order': not args.no_fanin_order and not args.no_gate_order,
              'scope': 'Complete bounded model, full32-row semantics; independent normalized SAT witness evaluation.'}
    for T in (args.table or TABLES):
        print(json.dumps({'starting': f'0x{T:08x}',
                          'baseline': len(seeds.get(T, baseline(T))['gates'])}), flush=True)
        r = search_one(T, args.budget, not args.no_fanin_order,
                       not args.no_gate_order, seeds.get(T))
        records.append(r); result['tables'] = records
        result['all_exhausted'] = (len(records) == len(TABLES)
            and {r['table'] for r in records} == {f'0x{t:08x}' for t in TABLES}
            and all(r['status'] == 'EXHAUSTED' for r in records))
        args.output.write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps({'table': r['table'], 'status': r['status'],
                          'upper': len(r['monotone_upper']['gates']),
                          'queries': [(q['gates_bound'],q['not_budget'],q['status'],round(q['seconds'],2)) for q in r['queries']]}), flush=True)


if __name__ == '__main__': main()
