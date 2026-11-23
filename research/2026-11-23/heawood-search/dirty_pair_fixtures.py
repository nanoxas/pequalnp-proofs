"""Exact witness fixtures for the two canonical dirty-pair encodings.
These deliberately nonoptimal circuits validate constraints and decode only.
"""
import argparse,json
from pathlib import Path
import synth
from synth import Encoding,Solver

def add(gates,op,a,b):
    gates.append([op,a,b]);return synth.N+len(gates)-1

def stars(gates,edges):
    outs=[]
    for u in range(7):
        ns=[b for a,b in edges if a==u]
        if not ns:continue
        s=ns[0]
        for v in ns[1:]:s=add(gates,'or',s,v)
        outs.append(add(gates,'and',u,s))
    return outs

def merge(gates,outs):
    w=outs[0]
    for x in outs[1:]:w=add(gates,'or',w,x)
    return w

def seed5():
    gs=[]
    left=add(gs,'or',0,2);right=add(gs,'or',7,8)
    dirty=add(gs,'and',left,right)
    guard=add(gs,'or',0,8);clean=add(gs,'and',dirty,guard)
    rest=[e for e in synth.E if e not in [(0,7),(0,8),(2,8)]]
    merge(gs,[clean]+stars(gs,rest))
    return synth.canonical(gs)

def seed7():
    gs=[];outs=[]
    for u in range(7):
        ns=[b for a,b in synth.E if a==u]
        s=add(gs,'or',ns[0],ns[1]);s=add(gs,'or',s,ns[2])
        if u==1:
            wider=add(gs,'or',0,s)
            dirty=add(gs,'and',u,wider)
            outs.append(add(gs,'and',dirty,s))
        else:outs.append(add(gs,'and',u,s))
    merge(gs,outs)
    return synth.canonical(gs)

records=[]
for k,gs in [(5,seed5()),(7,seed7())]:
    assert synth.verify(gs) is None
    args=argparse.Namespace(at_most=False,allow_equal=False,ordered=True,lex_order=True,
        live=True,nondegenerate=False,semantic_pruning=False,dominance_all=False,
        edge_singletons=False,clean_and=False,clean_abstract=False,dirty_class=None,
        dirty_pair_class=k,any_dirty=False,orbit=None,first=None,and_count=None,max_ors=None,last_or=False)
    enc=Encoding(len(gs),args)
    for lit in enc.fix(gs):enc.add(lit)
    with Solver(name='cadical300',bootstrap_with=enc.cnf.clauses) as s:
        ok=s.solve();assert ok
        decoded=enc.decode(s.get_model());assert decoded==gs
    p=Path(f'dirty{k}-fixture.json')
    p.write_text(json.dumps({'gates':gs,'output':14+len(gs)-1,
        'full_truth_table_validated':True,'dirty_pair_class':k},indent=2)+'\n')
    records.append({'class':k,'gates':len(gs),'rows':len(enc.rows),'status':ok,
                    'full_truth_table_validated':True})
print(json.dumps(records))
