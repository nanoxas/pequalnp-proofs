#!/usr/bin/env python3
"""Full-truth-table counterexample synthesis for public task L-meta-997.

This is a local finite search. It never changes a lease or sends a result.
Only n>0, |y|>=1 and distinct targets of size>=2 are encoded. Every satisfying
model is independently evaluated with the project's list-circuit semantics.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
import resource
import sys
import time
from functools import lru_cache

BASE = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(BASE/'heawood-search/vendor'))
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

PRIVATE_STATE = BASE/'pequalnp-proofs/.pnp/L-meta-997.json'


class InactiveTask(RuntimeError):
    pass


def check_live():
    try:
        state = json.loads(PRIVATE_STATE.read_text())
    except (OSError,json.JSONDecodeError):
        raise InactiveTask('task state is unavailable')
    if state.get('inactive') or state.get('closed') or any(state.get(k)==410 for k in ('status','last_http_status','last_beat_status')):
        raise InactiveTask('task state is inactive or closed')


def evaluate(n, circuit, sets, y):
    gate_count = len(circuit['gates'])
    rows = []
    for row in range(1<<n):
        wires = [bool(row>>i&1) for i in range(n)]
        for gate in circuit['gates']:
            args = [wires[w] if w < len(wires) else False for w in gate['inputs']]
            if gate['op']=='and': value=all(args)
            elif gate['op']=='or': value=any(args)
            elif gate['op']=='not': value=not (args[0] if args else False)
            else: raise ValueError('unsupported operation')
            wires.append(value)
        rows.append(wires)
    not_indices = [j for j,g in enumerate(circuit['gates']) if g['op']=='not']
    assert len(not_indices)==1
    t = not_indices[0]
    assert all(len(g['inputs'])<=2 for g in circuit['gates'])
    assert all((a&b).bit_count()<=1 for a,b in itertools.combinations(sets,2))
    violated_rows=sorted({row for S,o in zip(sets,circuit['outputs']) for row in range(1<<n) if rows[row][o] != bool(row&S)})
    outputs_ok = not violated_rows
    threshold_ok = all(rows[row][n+t] for row in range(1<<n) if row.bit_count()<y.bit_count()) and not rows[y][n+t]
    disjoint = [S for S in sets if not S&y]
    refunds=[]
    for j in range(gate_count):
        singleton = sum(rows[1<<p][n+j]<<p for p in range(n))
        shifted = sum(rows[y|(1<<p)][n+j]<<p for p in range(n) if not y>>p&1)
        if singleton in sets and shifted in disjoint:
            refunds.append(j)
    weight = sum(S.bit_count() if not S&y else min(y.bit_count(),S.bit_count()) for S in sets)
    rhs = gate_count+len(refunds)+len(sets)
    return {'outputs_correct':outputs_ok,'not_window_correct':threshold_ok,
            'all_input_rows':1<<n,'violated_rows':violated_rows,'violated_row_count':len(violated_rows),'not_index':t,'refunded_gates':refunds,
            'weight':weight,'right_hand_side':rhs,'violation':outputs_ok and threshold_ok and weight>rhs}


@lru_cache(maxsize=2)
def input_vectors(n):
    length=1<<n
    byte_count=(length+7)//8
    top=(1<<length)-1
    vectors=[]
    for j in range(n):
        if j<3:
            pattern=bytes([(0xaa,0xcc,0xf0)[j]])*byte_count
        else:
            block=1<<(j-3)
            pattern=(bytes(block)+b'\xff'*block)*(byte_count//(2*block))
        vectors.append(int.from_bytes(pattern,'little')&top)
    return top,tuple(vectors)


def evaluate_vectors(n,circuit,sets,y):
    """Evaluate every assignment simultaneously, one bit per truth-table row."""
    top,inputs=input_vectors(n)
    wires=list(inputs)
    for gate in circuit['gates']:
        args=[wires[w] if w<len(wires) else 0 for w in gate['inputs']]
        if gate['op']=='not':value=top^(args[0] if args else 0)
        else:
            value=top if gate['op']=='and' else 0
            for a in args:value=value&a if gate['op']=='and' else value|a
        wires.append(value)
    not_indices=[j for j,g in enumerate(circuit['gates']) if g['op']=='not']
    assert len(not_indices)==1
    t=not_indices[0]
    bad_mask=0
    for S,o in zip(sets,circuit['outputs']):
        expected=0
        for p in range(n):
            if S>>p&1:expected|=inputs[p]
        bad_mask|=wires[o]^expected
    bad_count=bad_mask.bit_count()
    first_bad=[]
    remaining=bad_mask
    for _ in range(min(16,bad_count)):
        low=remaining&-remaining
        first_bad.append(low.bit_length()-1)
        remaining^=low
    byte_count=((1<<n)+7)//8
    not_bytes=wires[n+t].to_bytes(byte_count,'little')
    at=lambda data,row:bool(data[row>>3]>>(row&7)&1)
    low_rows=(sum(1<<p for p in part) for size in range(y.bit_count()) for part in itertools.combinations(range(n),size))
    threshold_ok=all(at(not_bytes,row) for row in low_rows) and not at(not_bytes,y)
    disjoint=[S for S in sets if not S&y]
    refunds=[]
    for j in range(len(circuit['gates'])):
        data=wires[n+j].to_bytes(byte_count,'little')
        first=sum(at(data,1<<p)<<p for p in range(n))
        second=sum(at(data,y|(1<<p))<<p for p in range(n) if not y>>p&1)
        if first in sets and second in disjoint:refunds.append(j)
    weight=sum(S.bit_count() if not S&y else min(y.bit_count(),S.bit_count()) for S in sets)
    rhs=len(circuit['gates'])+len(refunds)+len(sets)
    return {'outputs_correct':not bad_count,'not_window_correct':threshold_ok,
            'all_input_rows':1<<n,'violated_rows':first_bad,'violated_row_count':bad_count,
            'not_index':t,'refunded_gates':refunds,'weight':weight,'right_hand_side':rhs,
            'violation':not bad_count and threshold_ok and weight>rhs}


class Encoder:
    def __init__(self,n,sets,y,k,ordered=True,refund_bound_override=None,rows=None):
        assert n>0 and y>0 and y < 1<<n and k>0
        assert len(set(sets))==len(sets) and all(S.bit_count()>=2 for S in sets)
        self.n,self.sets,self.y,self.k=n,sets,y,k
        initial_rows=set(range(1<<n)) if rows is None else set(rows)
        required={row for row in range(1<<n) if row.bit_count()<y.bit_count()}|{y}|{1<<p for p in range(n)}
        if any(not S&y for S in sets):required|={y|(1<<p) for p in range(n) if not y>>p&1}
        assert required<=initial_rows and all(0<=row<1<<n for row in initial_rows)
        self.rows=set()
        self.cnf,self.pool=CNF(),IDPool()
        self.truth=self.new('true'); self.cnf.append([self.truth])
        self.ops=[];self.a=[];self.b=[];self.values=[];self.outputs=[];self.refunds=[]
        for j in range(k):
            ops={name:self.new(('op',j,name)) for name in ('and','or','not','one')}
            a=[self.new(('a',j,w)) for w in range(n+1+j)]
            b=[self.new(('b',j,w)) for w in range(n+1+j)]
            self.onehot(list(ops.values()));self.onehot(a);self.onehot(b)
            self.ops.append(ops);self.a.append(a);self.b.append(b)
            self.values.append({})
            for u in range(len(a)):
                for v in range(u): self.cnf.append([-a[u],-b[v]])
                self.cnf.append([-ops['not'],-a[u],b[u]])
            self.cnf.append([-ops['one'],a[0]]);self.cnf.append([-ops['one'],b[0]])
            if ordered and j:
                for u in range(len(self.b[j-1])):
                    for v in range(u): self.cnf.append([-self.b[j-1][u],-b[v]])
        self.onehot([op['not'] for op in self.ops])
        for i,S in enumerate(sets):
            out=[self.new(('output',i,j)) for j in range(k)]
            self.onehot(out);self.outputs.append(out)
        self.add_rows(initial_rows)
        for j in range(k):
            on_singletons=[];on_shifted=[]
            for i,S in enumerate(sets):
                on_singletons.append(self.conjunction([self.values[j][1<<p] if S>>p&1 else -self.values[j][1<<p] for p in range(n)],('A',j,i)))
                if not S&y:
                    on_shifted.append(self.conjunction([self.values[j][y|(1<<p)] if S>>p&1 else -self.values[j][y|(1<<p)] for p in range(n) if not y>>p&1],('B',j,i)))
            first=self.disjunction(on_singletons,('hasA',j))
            second=self.disjunction(on_shifted,('hasB',j))
            self.refunds.append(self.conjunction([first,second],('refund',j)))
        weight=sum(S.bit_count() if not S&y else min(y.bit_count(),S.bit_count()) for S in sets)
        self.weight=weight;self.refund_bound=weight-len(sets)-k-1 if refund_bound_override is None else refund_bound_override
        if self.refund_bound<0:self.cnf.append([])
        elif self.refund_bound<k:self.cnf.extend(CardEnc.atmost(self.refunds,bound=self.refund_bound,vpool=self.pool,encoding=EncType.seqcounter).clauses)

    def new(self,key):return self.pool.id(key)
    def add_rows(self,rows):
        start=len(self.cnf.clauses)
        for row in sorted(set(rows)-self.rows):
            for j in range(self.k):self.values[j][row]=self.new(('v',j,row))
            for j in range(self.k):
                av,bv=self.new(('av',j,row)),self.new(('bv',j,row))
                for w in range(self.n+1+j):
                    val=self.wire(w,row)
                    if abs(val)==self.truth:
                        self.cnf.extend([[-self.a[j][w],av if val>0 else -av],
                                         [-self.b[j][w],bv if val>0 else -bv]])
                    else:
                        self.cnf.extend([[-self.a[j][w],-av,val],[-self.a[j][w],av,-val],
                                         [-self.b[j][w],-bv,val],[-self.b[j][w],bv,-val]])
                v=self.values[j][row];o=self.ops[j]
                self.cnf.extend([[-o['and'],-av,-bv,v],[-o['and'],av,-v],[-o['and'],bv,-v],
                                 [-o['or'],av,bv,-v],[-o['or'],-av,v],[-o['or'],-bv,v],
                                 [-o['not'],av,v],[-o['not'],-av,-v],[-o['one'],v]])
                if row.bit_count()<self.y.bit_count():self.cnf.append([-o['not'],v])
                if row==self.y:self.cnf.append([-o['not'],-v])
            for i,S in enumerate(self.sets):
                for j in range(self.k):self.cnf.append([-self.outputs[i][j],self.values[j][row] if row&S else -self.values[j][row]])
            self.rows.add(row)
        return start
    def onehot(self,lits):
        self.cnf.extend(CardEnc.equals(lits,bound=1,vpool=self.pool,encoding=EncType.seqcounter).clauses)
    def conjunction(self,lits,key):
        a=self.new(key)
        self.cnf.extend([[-a,lit] for lit in lits]);self.cnf.append([a]+[-lit for lit in lits])
        return a
    def disjunction(self,lits,key):
        a=self.new(key)
        self.cnf.extend([[a,-lit] for lit in lits]);self.cnf.append([-a]+lits)
        return a
    def wire(self,w,row):
        if w<self.n:return self.truth if row>>w&1 else -self.truth
        if w==self.n:return -self.truth
        return self.values[w-self.n-1][row]
    def decode(self,model):
        positive=set(v for v in model if v>0)
        def actual(w):return w if w<self.n else self.n+self.k if w==self.n else w-1
        gates=[]
        for j in range(self.k):
            op=next(op for op,lit in self.ops[j].items() if lit in positive)
            a=next(i for i,lit in enumerate(self.a[j]) if lit in positive)
            b=next(i for i,lit in enumerate(self.b[j]) if lit in positive)
            gates.append({'op':'and' if op=='one' else op,
                          'inputs':[] if op=='one' else [actual(a)] if op=='not' else [actual(a),actual(b)]})
        outputs=[self.n+next(j for j,lit in enumerate(o) if lit in positive) for o in self.outputs]
        return {'gates':gates,'outputs':outputs}


def initial_rows(case):
    n,y,sets=case['n'],case['y'],case['sets']
    all_inputs=(1<<n)-1
    return sorted({row for row in range(1<<n) if row.bit_count()<y.bit_count()}|
                  {y}|{1<<p for p in range(n)}|{all_inputs^S for S in sets}|
                  {y|(1<<p) for p in range(n) if not y>>p&1})


def solve_case(case,k,seconds=30,ordered=True,cegis=False):
    check_live()
    started=time.monotonic()
    selected=initial_rows(case) if cegis else None
    enc=Encoder(case['n'],case['sets'],case['y'],k,ordered,rows=selected)
    result={'name':case['name'],'n':case['n'],'sets':case['sets'],'y':case['y'],
            'gates':k,'weighted_sum':enc.weight,'refund_bound':enc.refund_bound,
            'variables':enc.pool.top,'clauses':len(enc.cnf.clauses),'ordered':ordered,
            'cegis':cegis,'initial_rows':len(enc.rows),'rounds':[]}
    progress_path=Path(__file__).resolve().parent/'solver-progress.json'
    progress_path.write_text(json.dumps({'status':'MODEL_BUILT',**result},indent=2)+'\n')
    with Solver(name='cadical300',bootstrap_with=enc.cnf) as solver:
        answer=None
        while True:
            check_live()
            if time.monotonic()-started>=seconds:answer=None;break
            solver.conf_budget(20_000)
            answer=solver.solve_limited(expect_interrupt=True)
            if answer is False:break
            if answer is None:
                progress_path.write_text(json.dumps({'status':'SOLVING','elapsed_seconds':time.monotonic()-started,
                    'stats':solver.accum_stats(),'sampled_rows':len(enc.rows),**result},indent=2)+'\n')
                continue
            candidate=enc.decode(solver.get_model())
            verified=evaluate_vectors(case['n'],candidate,case['sets'],case['y'])
            assert verified['not_window_correct']
            assert verified['weight']>verified['right_hand_side']
            if verified['violation']:
                result.update({'circuit':candidate,'independent_audit':verified})
                break
            assert cegis and verified['violated_rows']
            bad=[row for row in verified['violated_rows'] if row not in enc.rows]
            assert bad
            chosen=bad[:16]
            result['rounds'].append({'sampled_rows':len(enc.rows),'full_truth_failures':verified['violated_row_count'],'added_rows':chosen})
            start=enc.add_rows(chosen)
            solver.append_formula(enc.cnf.clauses[start:])
        result.update({'status':'SAT' if answer else 'UNSAT' if answer is False else 'UNKNOWN',
                       'seconds':time.monotonic()-started,'stats':solver.accum_stats(),
                       'final_rows':len(enc.rows),'variables':enc.pool.top,'clauses':len(enc.cnf.clauses)})
        progress_path.write_text(json.dumps(result,indent=2)+'\n')
    return result


def bounds(case):
    sets,y=case['sets'],case['y']
    weight=sum(S.bit_count() if not S&y else min(y.bit_count(),S.bit_count()) for S in sets)
    disjoint=sum(not S&y for S in sets)
    low=len(sets)+1
    high=weight-len(sets)-1-disjoint
    if 'gate_bounds' in case:
        assert all(low<=k<=high for k in case['gate_bounds'])
        return case['gate_bounds']
    if high<low:return []
    return [high] if disjoint==0 else list(range(low,high+1))


def load_cases(path):
    data=json.loads(path.read_text())
    cases=data.get('cases',[data]) if isinstance(data,dict) else data
    for case in cases:
        n=case['n'];sets=case['sets'];y=case['y']
        assert isinstance(n,int) and n>0 and 0<y<1<<n
        assert len(set(sets))==len(sets) and all(0<S<1<<n and S.bit_count()>=2 for S in sets)
        assert all((a&b).bit_count()<=1 for a,b in itertools.combinations(sets,2))
        assert isinstance(case['name'],str)
    return cases


def canonical(sets,n,d):
    best=None
    for left in itertools.permutations(range(d)):
        for right in itertools.permutations(range(d,n)):
            perm=left+right
            image=tuple(sorted(sum((1<<perm[i]) for i in range(n) if S>>i&1) for S in sets))
            if best is None or image<best:best=image
    return best


def small_families(max_n=5):
    result=[]
    for n in range(3,max_n+1):
        edges=[S for S in range(1<<n) if S.bit_count()>=2]
        for d in range(3,n+1):
            seen=set()
            def visit(chosen,remaining):
                if chosen and any(S.bit_count()>=3 for S in chosen):
                    case={'n':n,'sets':list(chosen),'y':(1<<d)-1}
                    if bounds(case):
                        key=canonical(chosen,n,d)
                        if key not in seen:
                            seen.add(key)
                            result.append({'name':f'all-n{n}-d{d}-{len(seen)}','n':n,'sets':list(key),'y':(1<<d)-1})
                for index,S in enumerate(remaining):
                    visit(chosen+(S,),[T for T in remaining[index+1:] if (S&T).bit_count()<=1])
            visit((),edges)
    return result


def named_families():
    mask=lambda vertices:sum(1<<v for v in vertices)
    pasch=[mask(v) for v in [(0,1,2),(0,3,4),(1,3,5),(2,4,5)]]
    fano=[mask([i,j,i^j]) for i in range(1,8) for j in range(i+1,8) if i^j>j]
    fano=[S>>1 for S in fano]
    cases=[]
    for name,n,sets in [('pasch',6,pasch),('fano',7,fano)]:
        for d in (3,4):
            seen=set()
            for verts in itertools.combinations(range(n),d):
                y=mask(verts)
                # Keep labeled y choices: the family is small, no unproved orbit cut.
                case={'name':f'{name}-y{y}','n':n,'sets':sets,'y':y}
                if bounds(case):cases.append(case)
    return cases


def k5_case():
    pairs=list(itertools.combinations(range(5),2))
    stars=[sum(1<<j for j,e in enumerate(pairs) if v in e) for v in range(5)]
    return {'name':'k5-vertex-stars-y-first-star','n':10,'sets':stars,'y':stars[0]}


def pin_circuit(enc,circuit):
    def logical(w):return w if w<enc.n else w+1 if w<enc.n+enc.k else enc.n
    for j,gate in enumerate(circuit['gates']):
        op='one' if gate['op']=='and' and not gate['inputs'] else gate['op']
        enc.cnf.append([enc.ops[j][op]])
        inputs=gate['inputs']
        a=logical(inputs[0]) if inputs else 0
        b=logical(inputs[1]) if len(inputs)>1 else a
        if a>b:a,b=b,a
        enc.cnf.append([enc.a[j][a]]);enc.cnf.append([enc.b[j][b]])
    for i,o in enumerate(circuit['outputs']):enc.cnf.append([enc.outputs[i][o-enc.n]])


def sanity():
    check_live()
    examples=[
      {'n':3,'sets':[7],'y':7,'refunds':[],
       'circuit':{'gates':[{'op':'and','inputs':[0,1]},{'op':'or','inputs':[0,1]},
                           {'op':'and','inputs':[2,3]},{'op':'or','inputs':[2,4]},
                           {'op':'not','inputs':[5]}],'outputs':[6]}},
      {'n':5,'sets':[9,24],'y':7,'refunds':[1,2],
       'circuit':{'gates':[{'op':'and','inputs':[0,1]},{'op':'or','inputs':[0,3]},
                           {'op':'or','inputs':[3,4]},{'op':'and','inputs':[2,5]},
                           {'op':'not','inputs':[8]}],'outputs':[6,7]}}]
    records=[]
    for ex in examples:
        k=len(ex['circuit']['gates'])
        audit=evaluate(ex['n'],ex['circuit'],ex['sets'],ex['y'])
        assert evaluate_vectors(ex['n'],ex['circuit'],ex['sets'],ex['y'])==audit
        assert audit['outputs_correct'] and audit['not_window_correct'] and audit['refunded_gates']==ex['refunds']
        enc=Encoder(ex['n'],ex['sets'],ex['y'],k,True,k)
        pin_circuit(enc,ex['circuit'])
        with Solver(name='cadical300',bootstrap_with=enc.cnf) as solver:
            assert solver.solve()
            positive=set(l for l in solver.get_model() if l>0)
            encoded=[j for j,l in enumerate(enc.refunds) if l in positive]
            assert encoded==ex['refunds']
            decoded=enc.decode(solver.get_model())
            assert evaluate(ex['n'],decoded,ex['sets'],ex['y'])==audit
        records.append({'n':ex['n'],'forced_circuit':'SAT','refunds':encoded,'audit':audit})
    ex=examples[1]
    enc=Encoder(ex['n'],ex['sets'],ex['y'],5,True,1)
    pin_circuit(enc,ex['circuit'])
    with Solver(name='cadical300',bootstrap_with=enc.cnf) as solver:assert not solver.solve()
    records.append({'forced_circuit_refund_cap':1,'status':'UNSAT','actual_refunds':2})
    bad=json.loads(json.dumps(ex['circuit']))
    bad['gates'][-1]['inputs']=[6]
    enc=Encoder(ex['n'],ex['sets'],ex['y'],5,False,5)
    pin_circuit(enc,bad)
    with Solver(name='cadical300',bootstrap_with=enc.cnf) as solver:assert not solver.solve()
    records.append({'forced_wrong_NOT_predecessor':'UNSAT'})
    # A deliberately wrong output matches the initial CEGIS rows, then fails
    # on a new row. Adding that row must refute the pinned circuit.
    case={'n':6,'sets':[9],'y':7}
    partial={'gates':[{'op':'and','inputs':[0,1]},{'op':'and','inputs':[2,6]},
                      {'op':'and','inputs':[3,4]},{'op':'and','inputs':[5,8]},
                      {'op':'or','inputs':[7,9]},{'op':'not','inputs':[10]},
                      {'op':'and','inputs':[3,11]},{'op':'or','inputs':[0,12]}],
             'outputs':[13]}
    rows=initial_rows(case)
    enc=Encoder(6,[9],7,8,False,8,rows=rows)
    pin_circuit(enc,partial)
    with Solver(name='cadical300',bootstrap_with=enc.cnf) as solver:
        assert solver.solve()
        audit=evaluate(6,partial,[9],7)
        assert evaluate_vectors(6,partial,[9],7)==audit
        assert audit['violated_rows'] and audit['not_window_correct']
        chosen=audit['violated_rows'][0]
        assert chosen not in rows
        start=enc.add_rows([chosen])
        solver.append_formula(enc.cnf.clauses[start:])
        assert not solver.solve()
    records.append({'cegis_pinned_partial_circuit':'SAT_THEN_UNSAT','added_row':chosen,
                    'full_truth_failures':audit['violated_rows']})
    path=Path(__file__).resolve().parent/'encoding-sanity.json'
    path.write_text(json.dumps({'status':'PASS','records':records},indent=2)+'\n')
    print(json.dumps({'status':'SANITY_PASS','path':str(path)}),flush=True)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--suite',choices=['small','named','fano-line','k5'],default='small')
    parser.add_argument('--seconds',type=float,default=20)
    parser.add_argument('--limit',type=int)
    parser.add_argument('--unordered',action='store_true')
    parser.add_argument('--sanity',action='store_true')
    parser.add_argument('--cegis',action='store_true')
    parser.add_argument('--case-file',type=Path)
    args=parser.parse_args()
    resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
    check_live()
    if args.sanity:
        sanity()
        return
    cases=load_cases(args.case_file) if args.case_file else small_families() if args.suite=='small' else [k5_case()] if args.suite=='k5' else named_families()
    if args.suite=='fano-line':
        cases=[c for c in cases if c['name'].startswith('fano') and c['y'] in c['sets']]
    if args.limit:cases=cases[:args.limit]
    here=Path(__file__).resolve().parent
    label=args.case_file.stem if args.case_file else args.suite
    output=here/f'results-{label}{"-cegis" if args.cegis else ""}{"-unordered" if args.unordered else ""}.json'
    records=[]
    print(json.dumps({'suite':args.suite,'families':len(cases),'queries':sum(len(bounds(c)) for c in cases)}),flush=True)
    try:
        for case in cases:
            for k in bounds(case):
                record=solve_case(case,k,args.seconds,not args.unordered,args.cegis)
                records.append(record)
                output.write_text(json.dumps({'suite':args.suite,'status':'IN_PROGRESS','results':records},indent=2)+'\n')
                print(json.dumps({key:record[key] for key in ['name','gates','status','seconds']}),flush=True)
                if record['status']=='SAT':
                    output.write_text(json.dumps({'suite':args.suite,'status':'VERIFIED_COUNTEREXAMPLE','results':records},indent=2)+'\n')
                    return
        status='COMPLETE_FINITE_SCOPE' if all(r['status']=='UNSAT' for r in records) else 'INCOMPLETE_FINITE_SCOPE'
    except InactiveTask as exc:
        status='STOPPED_INACTIVE_TASK'
        print(json.dumps({'status':status,'reason':str(exc)}),flush=True)
    output.write_text(json.dumps({'suite':args.suite,'status':status,'results':records},indent=2)+'\n')
    print(json.dumps({'status':status,'queries':len(records),'output':str(output)}),flush=True)


if __name__=='__main__':main()
