"""Exact partial-function AndCount search for live task L-meta-909."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import resource
import shutil
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
BASE = ROOT / 'and-count-audit/search.py'
N = 10
EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
         (5,7),(7,9),(9,6),(6,8),(8,5)]
LEASE = ROOT / 'pequalnp-proofs/.pnp/L-meta-909.json'


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1 << 20), b''): h.update(block)
    return h.hexdigest()


def utc(): return datetime.now(timezone.utc).isoformat()


def save(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def inactive():
    try:
        d = json.loads(LEASE.read_text())
        expiry = datetime.fromisoformat(d['lease']['expires_at'].replace('Z', '+00:00'))
        return bool(d.get('inactive')) or datetime.now(timezone.utc) >= expiry
    except (OSError, ValueError, KeyError, TypeError): return True


def graph_value(mask):
    return any(mask >> a & 1 and mask >> b & 1 for a,b in EDGES)


NEGATIVE = [m for m in range(1 << N) if not graph_value(m) and
            all(graph_value(m | (1 << v)) for v in range(N) if not (m >> v & 1))]
POSITIVE = sorted({m | (1 << v) for m in NEGATIVE for v in range(N) if not (m >> v & 1)})
ROWS = [(m, False) for m in NEGATIVE] + [(m, True) for m in POSITIVE]
assert len(NEGATIVE) == 15 and len(POSITIVE) == 100 and len(ROWS) == 115
assert all(any(m >> v & 1 for m in NEGATIVE) for v in range(N))


def module(rows):
    manifest = json.loads((HERE / 'encoder-dependency.json').read_text())
    if sha(BASE) != manifest['sha256']: raise RuntimeError('Reviewed encoder dependency changed')
    spec = importlib.util.spec_from_file_location('l909_and_count_base', BASE)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    mod.N, mod.EDGES, mod.ROWS = N, EDGES, list(rows)
    return mod


def encoding(mod, count, limit=2):
    from pysat.card import CardEnc, EncType
    enc = mod.Encoding(count)
    for v in range(N):
        readers = []
        for g in range(count):
            hit = enc.pool.id(('bare_reader', v, g))
            left, right = enc.select[g,0,v], enc.select[g,1,v]
            enc.cnf.extend([[-left, hit], [-right, hit], [-hit, left, right]])
            readers.append(hit)
        enc.cnf.extend(CardEnc.atmost(readers, bound=limit, vpool=enc.pool,
                                     encoding=EncType.seqcounter).clauses)
    return enc


def evaluate(circuit, mask):
    values = [bool(mask >> v & 1) for v in range(N)]
    for i, gate in enumerate(circuit['gates']):
        assert all(0 <= w < N+i for side in ('left','right') for w in gate[side])
        values.append(any(values[w] for w in gate['left']) and
                      any(values[w] for w in gate['right']))
    return any(values[N+i] for i in circuit['output_gates'])


def assess(circuit, count):
    assert len(circuit['gates']) == count
    truth = [evaluate(circuit, m) for m in range(1 << N)]
    readers = [sum(v in set(g['left']) | set(g['right']) for g in circuit['gates']) for v in range(N)]
    bad = [m for m, want in ROWS if truth[m] != want]
    assert not bad and max(readers) <= 2
    assert all(not truth[m] or graph_value(m) for m in range(1 << N))
    return {'partial_rows_checked': len(ROWS), 'truth_values_evaluated': len(truth),
            'bare_reader_counts': readers, 'global_soundness_checked': True,
            'full_edge_function': all(truth[m] == bool(graph_value(m)) for m in range(1 << N))}


def selftest():
    controls = []
    examples = [
        ('nested', {'gates':[{'left':[0], 'right':[1]},
                            {'left':[2,10], 'right':[3,10]},
                            {'left':[4,11], 'right':[5,11]}], 'output_gates':[2]}, 2),
        ('repeated-port-counted-once', {'gates':[{'left':[0], 'right':[0]}], 'output_gates':[0]}, 1),
    ]
    for name, c, limit in examples:
        rows = [(m, evaluate(c,m)) for m in range(1 << N)]
        mod = module(rows); enc = encoding(mod, len(c['gates']), limit)
        with mod.Solver(name='cadical300', bootstrap_with=enc.cnf.clauses + enc.fix(c)) as solver:
            answer = solver.solve()
        assert answer is True
        controls.append({'name':name, 'result':'SAT_AS_EXPECTED'})
    c = examples[0][1]
    rows = [(m, evaluate(c,m)) for m in range(1 << N)]
    rows[0] = (0, True)
    mod = module(rows); enc = encoding(mod, len(c['gates']))
    with mod.Solver(name='cadical300', bootstrap_with=enc.cnf.clauses + enc.fix(c)) as solver:
        answer = solver.solve()
    assert answer is False
    controls.append({'name':'wrong-output-bit','result':'UNSAT_AS_EXPECTED'})
    c = {'gates':[{'left':[0], 'right':[v]} for v in (1,2,3)], 'output_gates':[0,1,2]}
    rows = [(m,evaluate(c,m)) for m in range(1 << N)]
    mod = module(rows); enc = encoding(mod,3)
    with mod.Solver(name='cadical300', bootstrap_with=enc.cnf.clauses + enc.fix(c)) as solver:
        answer = solver.solve()
    assert answer is False
    controls.append({'name':'three-bare-readers-rejected','result':'UNSAT_AS_EXPECTED'})
    record = {'status':'PASS','program_sha256':sha(__file__),'dependency_sha256':sha(BASE),
              'controls':controls,'utc':utc()}
    save(HERE / 'selftest.json', record)
    print(json.dumps(record), flush=True)


def worker(args):
    resource.setrlimit(resource.RLIMIT_AS, (2 << 30, 2 << 30))
    if inactive(): raise RuntimeError('Lease inactive')
    out = Path(args.output); out.mkdir(exist_ok=True)
    start = time.monotonic()
    mod = module(ROWS); enc = encoding(mod,args.count)
    enc.cnf.to_file(str(out / 'query.cnf'))
    save(out / 'rows.json', ROWS)
    record = {'status':'RUNNING','started_utc':utc(),'and_gates':args.count,'rows':len(ROWS),
              'variables':enc.pool.top,'clauses':len(enc.cnf.clauses),
              'program_sha256':sha(__file__),'dependency_sha256':sha(BASE),
              'cnf_sha256':sha(out / 'query.cnf'),'rows_sha256':sha(out / 'rows.json'),
              'bound_seconds':args.seconds,'proof_verified':False,'lean_verified':False,
              'output_variables':[], 'symmetry_cuts':[],
              'scope':'Exact partial-function model with empty outputs, overlapping sides, and unused gates allowed. At most2 actual reader gates per variable.'}
    save(out / 'result.json',record)
    status = None; reason = None
    with mod.Solver(name='cadical300', bootstrap_with=enc.cnf.clauses, with_proof=True) as solver:
        while status is None:
            if inactive(): reason='lease_inactive'; break
            if (out / 'STOP').exists(): reason='stop_file'; break
            if time.monotonic()-start >= args.seconds: reason='wall_time'; break
            if shutil.disk_usage(out).free < (2 << 30): reason='disk_reserve'; break
            solver.conf_budget(2000)
            status = solver.solve_limited(expect_interrupt=True)
            record.update(elapsed_seconds=round(time.monotonic()-start,3),utc=utc(),stats=solver.accum_stats())
            save(out / 'progress.json',record)
            if os.fstat(solver.solver.prfile.fileno()).st_size > (2 << 30): reason='proof_size_limit'; break
        record.update(status='SAT' if status is True else 'UNSAT' if status is False else 'UNKNOWN',
                      stop_reason=reason,stats=solver.accum_stats())
        if status is True:
            circuit=enc.decode(solver.get_model())
            record.update(circuit=circuit,validation=assess(circuit,args.count))
            save(out / 'witness.json', {'circuit':circuit, 'validation':record['validation']})
        else:
            import pysolvers
            pysolvers.flushpr(solver.solver.prfp)
            size=os.fstat(solver.solver.prfile.fileno()).st_size
            if shutil.disk_usage(out).free >= size+(2 << 30):
                proof=out / ('unsat.drat.bin' if status is False else 'partial.drat.bin')
                solver.solver.prfile.seek(0)
                with proof.open('wb') as stream:shutil.copyfileobj(solver.solver.prfile,stream,1 << 20)
                record.update(proof_file=proof.name,proof_sha256=sha(proof),proof_bytes=proof.stat().st_size)
    record.update(elapsed_seconds=round(time.monotonic()-start,3),completed_utc=utc())
    save(out / 'result.json',record);print(json.dumps(record),flush=True)


def supervise(args):
    out=Path(args.output);out.mkdir(exist_ok=True)
    if inactive():raise RuntimeError('Lease inactive')
    if (out/'result.json').exists():raise RuntimeError('Existing run directory; use a new one')
    command=[sys.executable,str(Path(__file__).resolve()),'--worker','--count',str(args.count),
             '--seconds',str(args.seconds),'--output',str(out.resolve())]
    process=None;reason=None;requested=None;start=time.monotonic()
    def stop(signum,frame):
        nonlocal requested
        requested=signum
    old={sig:signal.signal(sig,stop) for sig in (signal.SIGINT,signal.SIGTERM)}
    try:
        with (out/'solver.log').open('w') as log:
            process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            while process.poll() is None:
                if requested is not None:reason='supervisor_signal';break
                if inactive():reason='lease_inactive';break
                if (out/'STOP').exists():reason='stop_file';break
                if time.monotonic()-start>args.seconds+40:reason='hard_wall_time';break
                time.sleep(2)
    finally:
        if process is not None and process.poll() is None:
            process.terminate()
            try:process.wait(timeout=5)
            except subprocess.TimeoutExpired:process.kill();process.wait()
        path=out/'result.json';record=json.loads(path.read_text()) if path.exists() else {}
        code=process.returncode if process is not None else None
        if reason or code!=0 or record.get('status')=='RUNNING':
            record.update(status='UNKNOWN',stop_reason=reason or 'worker_failure',worker_exit_code=code)
        record['supervisor_reaped_child']=process is not None and process.poll() is not None
        save(path,record)
        for sig,handler in old.items():signal.signal(sig,handler)
    print(json.dumps(record),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();group=p.add_mutually_exclusive_group(required=True)
    group.add_argument('--selftest',action='store_true');group.add_argument('--setup',action='store_true')
    group.add_argument('--run',action='store_true');group.add_argument('--worker',action='store_true')
    p.add_argument('--count',type=int,default=6);p.add_argument('--seconds',type=int,default=300)
    p.add_argument('--output',default=str(HERE/'run-six'))
    args=p.parse_args()
    if args.count<1 or args.seconds<1:p.error('Positive count and time required')
    if args.selftest:selftest()
    elif args.setup:
        enc=encoding(module(ROWS),args.count)
        print(json.dumps({'rows':len(ROWS),'variables':enc.pool.top,'clauses':len(enc.cnf.clauses),'program_sha256':sha(__file__),'dependency_sha256':sha(BASE)}))
    elif args.worker:worker(args)
    else:supervise(args)
