#!/usr/bin/env python3
"""Profile Heawood candidates by dirty ANDs and cone-based edge ownership."""
import json
from pathlib import Path
import sys
import synth

ROWS,ANS=synth.samples()
P=(1<<len(synth.E))-1
ALL=(1<<len(ROWS))-1
NEG=ALL^P

def profile(path):
    data=json.loads(Path(path).read_text())
    gates=data['gates'];out=data.get('output',synth.N+len(gates)-1)
    values=[sum(((row>>i)&1)<<t for t,row in enumerate(ROWS)) for i in range(synth.N)]
    seen=[0]*synth.N
    raw=[1<<i for i in range(synth.N)]
    singleton=raw.copy()
    depth=[0]*synth.N
    ands=[]
    for i,(op,a,b) in enumerate(gates):
        assert a<synth.N+i and b<synth.N+i
        val=values[a]&values[b] if op=='and' else values[a]|values[b]
        strict=seen[a]|seen[b]
        if op=='and':
            own=val&P&~strict
            owned=[e for t,e in enumerate(synth.E) if own>>t&1]
            dirty=[m for t,m in enumerate(ROWS) if t>=len(synth.E) and val>>t&1]
            centers=[v for v in range(synth.N) if all(v in e for e in owned)]
            ands.append({'gate':i,'wire':synth.N+i,'fanins':[a,b],
                'positive_count':(val&P).bit_count(),'dirty_count':len(dirty),
                'dirty_by_cardinality':{str(k):sum(m.bit_count()==k for m in dirty) for k in [4,5,7]},
                'dirty_masks':dirty,'owned_edges':owned,'star_centers':centers,
                'raw_supports':[[v for v in range(synth.N) if raw[w]>>v&1] for w in [a,b]]})
        values.append(val)
        seen.append(strict|(val if op=='and' else 0))
        raw.append(0 if op=='and' else raw[a]|raw[b])
        singleton.append(singleton[a]&singleton[b] if op=='and' else singleton[a]|singleton[b])
        depth.append(max(depth[a],depth[b])+(op=='and'))
    wrong=(values[out]^P)&ALL
    bad=None
    for mask in range(1<<synth.N):
        ws=[bool(mask>>i&1) for i in range(synth.N)]
        for op,a,b in gates:ws.append(ws[a] and ws[b] if op=='and' else ws[a] or ws[b])
        if ws[out]!=synth.target(mask):bad=mask;break
    return {'path':str(path),'gates':len(gates),'and_count':len(ands),
        'or_count':len(gates)-len(ands),'and_depth':depth[out],
        'boundary_errors':wrong.bit_count(),'first_full_counterexample':bad,
        'first_dirty_and':next((a['gate'] for a in ands if a['dirty_count']),None),
        'nonstar_owners':[a['gate'] for a in ands if not a['star_centers']],
        'ands':ands}

if __name__=='__main__':
    records=[profile(p) for p in sys.argv[1:]]
    Path('circuit-profiles.json').write_text(json.dumps(records,indent=2)+'\n')
    for d in records:
        print(json.dumps({k:v for k,v in d.items() if k!='ands'}))
