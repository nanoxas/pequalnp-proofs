#!/usr/bin/env python3
"""Build extra monotone upper witnesses by minimum-formula dynamic programming.

This is only an upper-bound generator. Every generated DAG is checked on
all32 rows; no circuit lower bound is inferred from its formula search.
"""
from pathlib import Path
import importlib.util
import json
import time

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('local_search', HERE/'search.py')
s = importlib.util.module_from_spec(spec); spec.loader.exec_module(s)

started = time.monotonic()
variables = [sum(((m >> i) & 1) << m for m in range(32)) for i in range(5)]
best = {t: ('input', i) for i, t in enumerate(variables)}
best[0], best[s.ALL] = ('const', 0), ('const', 1)
levels = [list(best)]
for cost in range(1, 16):
    new = []
    for p in range((cost-1)//2 + 1):
        q = cost-1-p
        if q >= len(levels): continue
        left, right = levels[p], levels[q]
        for ia, a in enumerate(left):
            rb = right[:ia+1] if p == q else right
            for b in rb:
                for op, z in (('and', a & b), ('or', a | b)):
                    if z not in best:
                        best[z] = (op, a, b); new.append(z)
    levels.append(new)
    print(json.dumps({'formula_cost':cost,'new_functions':len(new),
                      'targets_found':sum(t in best for t in s.TABLES)}),flush=True)
    if all(t in best for t in s.TABLES): break

records = []
for T in s.TABLES:
    incumbent = s.baseline(T)
    if T in best:
        gates, cache = [], {}
        def emit(t):
            if t in cache: return cache[t]
            data = best[t]
            if data[0] == 'input': return data[1]
            if data[0] == 'const': return 5+data[1]
            a, b = emit(data[1]), emit(data[2])
            w = 7+len(gates); gates.append([data[0],a,b]); cache[t] = w
            return w
        out = emit(T)
        c = s.normalize(gates,out)
        assert s.truth(c) == T
        if len(c['gates']) < len(incumbent['gates']): incumbent = c
    records.append({'table':f'0x{T:08x}','monotone_upper':incumbent})

result = {'scope':'Independently evaluated upper witnesses only; formula optimality does not imply circuit optimality.',
          'seconds':time.monotonic()-started,'tables':records}
(HERE/'formula-uppers.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'seconds':result['seconds'],'uppers':[(r['table'],len(r['monotone_upper']['gates'])) for r in records]}),flush=True)
