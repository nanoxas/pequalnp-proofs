#!/usr/bin/env python3
"""Exact finite-sample monotone circuit synthesis for the Heawood edge function.

The 58 rows consist of every edge and every maximal independent set. For
monotone candidates agreement on these rows implies agreement on all inputs.
SAT witnesses are independently checked on all 16384 inputs before being saved.
Additional search restrictions are recorded explicitly in each result.
"""
import argparse
import itertools
import json
import os
from pathlib import Path
import resource
import sys
import time

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'vendor'))
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

E = [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
     (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
     (6,8),(6,9),(6,11)]
N = 14
HEAWOOD_EDGES=tuple(E)

def target(mask):
    return any(mask >> u & 1 and mask >> v & 1 for u, v in E)

def samples():
    adj = [0] * N
    for u, v in E:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    positives = [(1 << u) | (1 << v) for u, v in E]
    negatives = [m for m in range(1 << N) if not target(m) and
                 all(m >> u & 1 or adj[u] & m for u in range(N))]
    return positives + negatives, [True] * len(positives) + [False] * len(negatives)

def baseline():
    gates = []
    stars = []
    for u in range(7):
        ns = [v for a, v in E if a == u]
        a = N + len(gates); gates.append(['or', ns[0], ns[1]])
        b = N + len(gates); gates.append(['or', ns[2], a])
        c = N + len(gates); gates.append(['and', u, b])
        stars.append(c)
    a = stars[0]
    for b in stars[1:]:
        c = N + len(gates); gates.append(['or', a, b]); a = c
    return canonical(gates)

def canonical(gates):
    """Topological order by maximum then minimum already-numbered fanin."""
    rem = set(range(len(gates)))
    rename = {i: i for i in range(N)}
    out = []
    while rem:
        ready = []
        for i in rem:
            op, a, b = gates[i]
            if a in rename and b in rename:
                x, y = sorted((rename[a], rename[b]))
                ready.append((y, x, op, i))
        y, x, op, i = min(ready)
        rename[N+i] = N+len(out)
        out.append([op, x, y]); rem.remove(i)
    assert rename[N+len(gates)-1] == N+len(gates)-1
    return out

def verify(gates):
    for mask in range(1 << N):
        ws = [bool(mask >> i & 1) for i in range(N)]
        for op, a, b in gates:
            assert 0 <= a < len(ws) and 0 <= b < len(ws)
            ws.append(ws[a] and ws[b] if op == 'and' else ws[a] or ws[b])
        if ws[-1] != target(mask):
            return mask
    return None

class Encoding:
    def __init__(self, count, args):
        self.count = count
        self.args = args
        self.pool = IDPool()
        self.cnf = CNF()
        if getattr(args,'clean_abstract',False):
            self.rows=[(1<<u)|(1<<v) for u,v in E]+[1<<u for u in range(N)]
            self.answers=[True]*len(E)+[False]*N
        else:self.rows, self.answers = samples()
        if getattr(args,'dirty_pair_class',None) is not None:
            if N!=14 or tuple(E)!=HEAWOOD_EDGES:
                raise ValueError('Dirty pair classes are specific to this Heawood graph.')
            if args.clean_abstract or args.dirty_class is not None:
                raise ValueError('Use one dirty profile and the full boundary model.')
            self.rows.append({7:(1<<0)|(1<<1),5:(1<<2)|(1<<7)}[args.dirty_pair_class])
            self.answers.append(False)
        self.ops = [self.v(('op',i)) for i in range(count)]
        self.sel = [[[self.v(('sel',i,k,j)) for j in range(N+i)]
                     for k in range(2)] for i in range(count)]
        self.val = [[self.v(('val',i,t)) for t in range(len(self.rows))]
                    for i in range(count)]
        self.active = [self.v(('active',i)) for i in range(count)] if args.at_most else []
        self.output = [self.v(('output',i)) for i in range(count)] if args.at_most else []
        self.build()

    def v(self, key): return self.pool.id(key)
    def add(self, *lits): self.cnf.append(list(lits))
    def useful(self,i,lits):
        self.cnf.append(([-self.active[i]] if self.active else [])+list(lits))

    def exactly_one(self, lits):
        self.cnf.extend(CardEnc.equals(lits, bound=1, vpool=self.pool,
                                      encoding=EncType.seqcounter).clauses)

    def prefix_or(self,lits,key):
        out=[]
        for i,lit in enumerate(lits):
            v=self.v((key,i));out.append(v)
            if i==0:
                self.add(-v,lit);self.add(-lit,v)
            else:
                old=out[-2]
                self.add(-old,v);self.add(-lit,v);self.add(old,lit,-v)
        return out

    def mux(self, selectors, val, row, i):
        for j, s in enumerate(selectors):
            if j < N:
                self.add(-s, val if self.rows[row] >> j & 1 else -val)
            else:
                prev = self.val[j-N][row]
                self.add(-s, -val, prev)
                self.add(-s, val, -prev)

    def build(self):
        if self.active:
            self.add(self.active[0])
            for i in range(self.count-1):
                a,b,o=self.active[i],self.active[i+1],self.output[i]
                self.add(-b,a)
                self.add(-o,a);self.add(-o,-b);self.add(-a,b,o)
            self.add(-self.output[-1],self.active[-1])
            self.add(self.output[-1],-self.active[-1])
        for i in range(self.count):
            a, b = self.sel[i]
            self.exactly_one(a); self.exactly_one(b)
            for x in range(N+i):
                for y in range(x if self.args.allow_equal else x+1):
                    self.add(-a[x], -b[y])
            if self.args.orbit is not None and self.args.orbit>=1:
                for x in range(N):
                    for y in range(x+1,N):
                        samepart=(x<7)==(y<7)
                        edge=(x,y) in E
                        guard=[-self.active[i]] if self.active else []
                        if samepart:
                            self.cnf.append(guard+[-self.ops[i],-a[x],-b[y]])
                        if self.args.orbit>=2 and edge:
                            self.cnf.append(guard+[self.ops[i],-a[x],-b[y]])
                        if self.args.orbit>=3 and edge:
                            self.cnf.append(guard+[-self.ops[i],-a[x],-b[y]])
            if self.args.ordered and i:
                oldb = self.sel[i-1][1]
                for x in range(N+i-1):
                    for y in range(x): self.add(-oldb[x], -b[y])
            if getattr(self.args,'lex_order',False):
                self.prefix_or(a,('fanin_a_le',i))
                if i:
                    eqb=self.v(('same_b',i));eqa=self.v(('same_a',i))
                    olda,oldb=self.sel[i-1]
                    for x in range(len(oldb)):
                        self.add(-oldb[x],-b[x],eqb)
                        self.add(-olda[x],-a[x],eqa)
                    for x in range(len(olda)):
                        self.add(-eqb,-self.v((('fanin_a_le',i),x)),
                                 self.v((('fanin_a_le',i-1),x)))
                    self.add(-eqb,-eqa,-self.ops[i-1],self.ops[i])
            op = self.ops[i]
            for t in range(len(self.rows)):
                x = self.v(('mux',i,0,t)); y = self.v(('mux',i,1,t))
                z = self.val[i][t]
                self.mux(a,x,t,i); self.mux(b,y,t,i)
                self.add(op,-x,-y,z); self.add(op,x,-z); self.add(op,y,-z)
                self.add(-op,x,y,-z); self.add(-op,-x,z); self.add(-op,-y,z)
            if getattr(self.args,'clean_abstract',False):
                edge_set={tuple(sorted(e)) for e in E}
                for u in range(N):
                    for v in range(N):
                        if u==v or tuple(sorted((u,v))) not in edge_set:
                            self.useful(i,[op,-self.v(('mux',i,0,len(E)+u)),
                                              -self.v(('mux',i,1,len(E)+v))])
            if self.args.nondegenerate or self.args.semantic_pruning:
                # A useful gate differs from each fanin on at least one test row.
                for side in (0,1):
                    diffs=[]
                    for t in range(len(self.rows)):
                        x=self.v(('mux',i,side,t)); z=self.val[i][t]
                        d=self.v(('diff',i,side,t)); diffs.append(d)
                        self.add(-d,x,z); self.add(-d,-x,-z)
                        self.add(d,-x,z); self.add(d,x,-z)
                    self.useful(i,diffs)
                    if self.args.semantic_pruning:
                        # An AND must improve the negative rows of either input;
                        # an OR must improve the positive rows of either input.
                        self.useful(i,[op]+diffs[len(E):])
                        self.useful(i,[-op]+diffs[:len(E)])
            if self.args.semantic_pruning:
                self.useful(i,self.val[i][:len(E)])
                self.useful(i,[-v for v in self.val[i][len(E):]])
            if getattr(self.args,'edge_singletons',False):
                # A wire true on exactly one edge e can be replaced at equal
                # gate cost by the direct conjunction of e's two endpoints.
                for t,(u,v) in enumerate(E):
                    antecedent=[-self.val[i][t]]+[
                        self.val[i][s] for s in range(len(E)) if s!=t]
                    for literal in [-op,a[min(u,v)],b[max(u,v)]]:
                        self.useful(i,antecedent+[literal])
            if self.args.dominance_all:
                for j in range(N+i):
                    improvements=[]
                    for t in range(len(self.rows)):
                        z=self.val[i][t]
                        if j<N:
                            old=bool(self.rows[t]>>j&1)
                            if t<len(E) and not old: improvements.append(z)
                            if t>=len(E) and old: improvements.append(-z)
                        else:
                            old=self.val[j-N][t]
                            d=self.v(('improves',i,j,t));improvements.append(d)
                            if t<len(E):
                                self.add(-d,z);self.add(-d,-old)
                            else:
                                self.add(-d,-z);self.add(-d,old)
                    self.useful(i,improvements)
        for t, answer in enumerate(self.answers):
            if self.output:
                for i in range(self.count):
                    self.add(-self.output[i],self.val[i][t] if answer else -self.val[i][t])
            else: self.add(self.val[-1][t] if answer else -self.val[-1][t])
        if getattr(self.args,'clean_and',False):
            for i in range(self.count):
                for t in range(len(E),len(self.rows)):
                    self.useful(i,[self.ops[i],-self.val[i][t]])
        if getattr(self.args,'any_dirty',False):
            if getattr(self.args,'clean_abstract',False):
                raise ValueError('Dirty witnesses require the full boundary model.')
            witnesses=[]
            for i in range(self.count):
                for t in range(len(E),len(self.rows)):
                    d=self.v(('any_dirty',i,t));witnesses.append(d)
                    self.add(-d,-self.ops[i]);self.add(-d,self.val[i][t])
                    if self.active:self.add(-d,self.active[i])
            self.cnf.append(witnesses)
        if getattr(self.args,'dirty_class',None) is not None:
            if N!=14 or tuple(E)!=HEAWOOD_EDGES:raise ValueError('Dirty classes are specific to this Heawood graph.')
            if self.args.orbit is not None or self.args.first:
                raise ValueError('Do not combine independently normalized pair and MIS representatives.')
            cardinality=self.args.dirty_class
            mask={7:127,5:244,4:432}[cardinality]
            t=self.rows.index(mask)
            witnesses=[]
            for i in range(self.count):
                d=self.v(('dirty_witness',i));witnesses.append(d)
                self.add(-d,-self.ops[i]);self.add(-d,self.val[i][t])
                if self.active:self.add(-d,self.active[i])
                for u in range(len(E),len(self.rows)):
                    if self.rows[u].bit_count()>cardinality:
                        self.useful(i,[self.ops[i],-self.val[i][u]])
            self.cnf.append(witnesses)
        if getattr(self.args,'dirty_pair_class',None) is not None:
            if self.args.orbit is not None or self.args.first:
                raise ValueError('Do not combine independently normalized pair representatives.')
            t=len(self.rows)-1
            witnesses=[]
            for i in range(self.count):
                d=self.v(('dirty_pair_witness',i));witnesses.append(d)
                self.add(-d,-self.ops[i]);self.add(-d,self.val[i][t])
                if self.active:self.add(-d,self.active[i])
                if self.args.dirty_pair_class==5:
                    for u in range(len(E),len(self.rows)):
                        if self.rows[u].bit_count()==7:
                            self.useful(i,[self.ops[i],-self.val[i][u]])
            self.cnf.append(witnesses)
        if self.args.live:
            for wire in range(N+self.count if self.active else N+self.count-1):
                if self.active:
                    if wire<N:continue
                    k=wire-N
                    uses=[-self.active[k],self.output[k]]
                    for i in range(k+1,self.count):
                        for side in (0,1):
                            u=self.v(('used_active',i,side,k))
                            s=self.sel[i][side][wire];a=self.active[i]
                            self.add(-u,s);self.add(-u,a);self.add(-s,-a,u)
                            uses.append(u)
                else:
                    uses=[self.sel[i][side][wire] for i in range(self.count)
                          if N+i>wire for side in (0,1)]
                self.cnf.append(uses)
        if self.args.first:
            parts=self.args.first.split(':')
            if len(parts)==2: op,b=parts; a=0; b=int(b)
            else: op,a,b=parts; a=int(a); b=int(b)
            self.add(self.ops[0] if op=='or' else -self.ops[0])
            self.add(self.sel[0][0][a]);self.add(self.sel[0][1][b])
        if self.args.and_count is not None:
            if self.active: raise ValueError('Exact AND-count option is for exact-size models only.')
            self.cnf.extend(CardEnc.equals([-v for v in self.ops],
                bound=self.args.and_count,vpool=self.pool,encoding=EncType.seqcounter).clauses)
        if getattr(self.args,'max_ors',None) is not None:
            counted=[]
            for i,op in enumerate(self.ops):
                if self.active:
                    a=self.active[i];v=self.v(('counted_or',i));counted.append(v)
                    self.add(-v,a);self.add(-v,op);self.add(-a,-op,v)
                else:counted.append(op)
            self.cnf.extend(CardEnc.atmost(counted,bound=self.args.max_ors,
                vpool=self.pool,encoding=EncType.seqcounter).clauses)
        if self.args.last_or:
            if self.output:
                for i in range(self.count):self.add(-self.output[i],self.ops[i])
            else:self.add(self.ops[-1])

    def fix(self,gates,prefix=None):
        lits=[]
        for i,(op,a,b) in enumerate(gates[:prefix]):
            lits += [self.ops[i] if op=='or' else -self.ops[i],
                     self.sel[i][0][min(a,b)],self.sel[i][1][max(a,b)]]
        return lits

    def decode(self,model):
        m=set(model)
        count=sum(a in m for a in self.active) if self.active else self.count
        return [['or' if self.ops[i] in m else 'and',
                 next(j for j,v in enumerate(self.sel[i][0]) if v in m),
                 next(j for j,v in enumerate(self.sel[i][1]) if v in m)]
                for i in range(count)]

def main():
    global N,E
    p=argparse.ArgumentParser()
    p.add_argument('--graph-json')
    p.add_argument('--gates',type=int,default=26)
    p.add_argument('--at-most',action='store_true')
    p.add_argument('--allow-equal',action='store_true')
    p.add_argument('--solver',default='cadical300')
    p.add_argument('--ordered',action='store_true')
    p.add_argument('--lex-order',action='store_true')
    p.add_argument('--live',action='store_true')
    p.add_argument('--nondegenerate',action='store_true')
    p.add_argument('--semantic-pruning',action='store_true')
    p.add_argument('--dominance-all',action='store_true')
    p.add_argument('--edge-singletons',action='store_true')
    p.add_argument('--clean-and',action='store_true')
    p.add_argument('--clean-abstract',action='store_true')
    p.add_argument('--any-dirty',action='store_true',
                   help='Require a live AND true on some maximal independent input')
    p.add_argument('--dirty-class',type=int,choices=[4,5,7])
    p.add_argument('--dirty-pair-class',type=int,choices=[5,7],
                   help='Require an AND true on a canonical independent pair; class5 also forbids full-part dirt')
    p.add_argument('--last-or',action='store_true')
    p.add_argument('--first',help='First gate op:a:b, or op:b with a=0')
    p.add_argument('--orbit',type=int,choices=range(4),help='Priority partition by first input-pair gate orbit')
    p.add_argument('--and-count',type=int)
    p.add_argument('--max-ors',type=int)
    p.add_argument('--baseline-check',action='store_true')
    p.add_argument('--baseline-phases',action='store_true')
    p.add_argument('--prefix-json')
    p.add_argument('--prefix-length',type=int)
    p.add_argument('--repair-json')
    p.add_argument('--edit-budget',type=int,default=3)
    p.add_argument('--conflicts',type=int)
    p.add_argument('--cnf')
    p.add_argument('--result',default='result.json')
    p.add_argument('--memory-gib',type=int,default=4)
    args=p.parse_args()
    if args.clean_abstract:
        if args.dirty_class is not None:raise ValueError('Clean abstraction cannot encode a dirty class.')
        args.clean_and=True
    if args.graph_json:
        data=json.load(open(args.graph_json));N=int(data['n'])
        E=sorted(set(tuple(sorted(map(int,e))) for e in data['edges']))
        assert all(0<=a<b<N for a,b in E)
    if args.lex_order:args.ordered=True
    if args.orbit is not None:
        if args.first:raise ValueError('Use either --orbit or --first.')
        args.first=['or:0:1','and:0:7','or:0:7','or:2:7'][args.orbit]
    resource.setrlimit(resource.RLIMIT_AS,(args.memory_gib*1024**3,)*2)
    start=time.monotonic()
    enc=Encoding(args.gates,args)
    repair=None
    if args.repair_json:
        data=json.load(open(args.repair_json))
        repair=canonical(data['gates'] if isinstance(data,dict) else data)
        assert len(repair)==args.gates
        edits=[]
        for i,(op,a,b) in enumerate(repair):
            d=enc.v(('edit',i));edits.append(d)
            for lit in [enc.ops[i] if op=='or' else -enc.ops[i],
                        enc.sel[i][0][a],enc.sel[i][1][b]]:
                enc.add(d,lit)
        enc.cnf.extend(CardEnc.atmost(edits,bound=args.edit_budget,vpool=enc.pool,
                                     encoding=EncType.seqcounter).clauses)
    print(json.dumps({'event':'encoded','variables':enc.pool.top,
        'clauses':len(enc.cnf.clauses),'rows':len(enc.rows),'seconds':time.monotonic()-start,
        'options':vars(args)}),flush=True)
    with Solver(name=args.solver,bootstrap_with=enc.cnf.clauses,use_timer=True) as solver:
        def phases(literals):
            try: solver.set_phases(literals)
            except NotImplementedError: pass
        if enc.active:phases(enc.active)
        assumptions=[]
        if args.baseline_check:
            assert args.gates==27
            gates=baseline(); assert verify(gates) is None
            assumptions=enc.fix(gates)
        if args.baseline_phases:
            gates=baseline()[:args.gates]
            phases(enc.fix(gates))
        if repair is not None: phases(enc.fix(repair))
        if args.prefix_json:
            data=json.load(open(args.prefix_json))
            gates=data['gates'] if isinstance(data,dict) else data
            assumptions+=enc.fix(gates,args.prefix_length)
        for lit in assumptions:
            solver.add_clause([lit]); enc.cnf.append([lit])
        if args.cnf: enc.cnf.to_file(args.cnf)
        print(json.dumps({'event':'solving','time':time.time()}),flush=True)
        if args.conflicts:
            solver.conf_budget(args.conflicts)
            sat=solver.solve_limited()
        else: sat=solver.solve()
        try:stats=solver.accum_stats()
        except NotImplementedError:stats=None
        data={'status':sat,'options':vars(args),'seconds':time.monotonic()-start,
              'stats':stats}
        if sat:
            gates=enc.decode(solver.get_model());bad=verify(gates)
            data.update(gates=gates,full_truth_table_validated=bad is None,counterexample=bad)
            if bad is not None: raise AssertionError(data)
        Path(args.result).write_text(json.dumps(data,indent=2)+'\n')
        print(json.dumps(data),flush=True)

if __name__=='__main__':main()
