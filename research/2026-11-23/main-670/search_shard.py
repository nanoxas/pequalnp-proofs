#!/usr/bin/env python3
"""Complete bounded exact-cost search for the assigned L-meta-670 shard 7.

Nine inputs, the false missing-wire value, fifteen binary AND/OR or unary NOT slots,
unrestricted NOT count, all 512 assignments, output the final slot, and
the first slot fixed to AND(x4,x6). Equal fanins and unused gates remain.
The only symmetry rule sorts commutative fanins; the unused NOT port is
duplicated. No gate-order, monotonicity, liveness, or semantic pruning.

The false sentinel is an unavailable wire in the project model. Each
unavailable read maps to it; empty AND becomes NOT(false), and other
empty/unary gates normalize without additional slots. Keep
the prefix ending at the original output (or the first slot if the output
is raw/unavailable) and append OR aliases up to the bound. This preserves
the prescribed first gate and covers every circuit of size at most 15 in
the shard. An UNSAT solver result alone is not a Lean-checked theorem.
"""

from pathlib import Path
import argparse
import hashlib
import json
import os
import random
import re
import resource
import shutil
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'heawood-search/vendor'))
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

N = 9
BASE = N + 1
FALSE = N
ROWS = 1 << N
EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
TARGET = [any((r >> a & 1) and (r >> b & 1) for a,b in EDGES) for r in range(ROWS)]
LEASE = ROOT / 'pequalnp-proofs/.pnp/L-meta-670.json'


def utc():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def save(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def inactive():
    try:
        return bool(json.loads(LEASE.read_text()).get('inactive', False))
    except (OSError, ValueError):
        return True


def evaluate_project(gates, output):
    """Independent list semantics, including empty and unavailable reads."""
    ans = []
    for row in range(ROWS):
        wires = [bool(row >> p & 1) for p in range(N)]
        for op, refs in gates:
            values = [wires[r] if r < len(wires) else False for r in refs]
            if op == 'and': value = all(values)
            elif op == 'or': value = any(values)
            elif op == 'not': value = not (values[0] if values else False)
            else: raise ValueError(op)
            wires.append(value)
        ans.append(wires[output] if output < len(wires) else False)
    return ans


def evaluate_free(gates, output=None):
    """Independent ordinary evaluator for the SAT model; no CNF variables."""
    ans = []
    if output is None: output = BASE + len(gates) - 1
    for row in range(ROWS):
        wires = [bool(row >> p & 1) for p in range(N)] + [False]
        for op, a, b in gates:
            assert 0 <= a < len(wires) and 0 <= b < len(wires)
            if op == 'and': value = wires[a] and wires[b]
            elif op == 'or': value = wires[a] or wires[b]
            elif op == 'not': value = not wires[a]
            else: raise ValueError(op)
            wires.append(value)
        ans.append(wires[output])
    return ans


def normalize_project(gates, output, bound):
    """One-way completeness map, retaining the exact first gate."""
    assert gates and gates[0] == ['and', [4, 6]]
    assert len(gates) <= bound
    if N <= output < N + len(gates):
        prefix = output - N + 1
        target = output + 1
    elif output < N:
        prefix = 1
        target = output
    else:
        prefix = 1
        target = FALSE
    result = []
    for j, (op, refs) in enumerate(gates[:prefix]):
        mapped = [r if r < N else r + 1 if r < N+j else FALSE for r in refs]
        if op == 'not':
            a = mapped[0] if mapped else FALSE
            result.append([op, a, a])
        else:
            if not mapped:
                result.append(['not' if op == 'and' else 'or', FALSE, FALSE])
            else:
                if len(mapped) == 1: mapped *= 2
                a, b = sorted(mapped)
                result.append([op, a, b])
    while len(result) < bound:
        result.append(['or', target, target])
        target = BASE + len(result) - 1
    assert target == BASE + bound - 1 or prefix == bound
    return result


def project_from_free(gates):
    """Literal exact-cost translation: false is one permanently unavailable read."""
    unavailable = N + len(gates)
    def wire(w):
        if w < N: return w
        if w == FALSE: return unavailable
        return w - 1
    built = [[op, [wire(a)] if op == 'not' else [wire(a), wire(b)]]
             for op,a,b in gates]
    assert built[0] == ['and', [4, 6]]
    return {'gates': built, 'output': N + len(built) - 1}


class Encoding:
    def __init__(self, bound=15, target=TARGET):
        self.bound, self.target = bound, list(target)
        self.pool, self.cnf = IDPool(), CNF()
        self.ops = [[self.v(('op', j, q)) for q in range(3)] for j in range(bound)]
        self.sel = [[[self.v(('sel', j, side, w)) for w in range(BASE+j)]
                     for side in range(2)] for j in range(bound)]
        self.val = [[self.v(('val', j, row)) for row in range(ROWS)] for j in range(bound)]
        for j in range(bound):
            self.one(self.ops[j])
            for side in self.sel[j]: self.one(side)
            for w in range(BASE+j):
                self.add(-self.ops[j][2], -self.sel[j][0][w], self.sel[j][1][w])
            for a in range(BASE+j):
                for b in range(a):
                    self.add(-self.sel[j][0][a], -self.sel[j][1][b])
            for row in range(ROWS):
                x, y = self.v(('port', j, 0, row)), self.v(('port', j, 1, row))
                z = self.val[j][row]
                for side, port in [(0, x), (1, y)]:
                    for w, selected in enumerate(self.sel[j][side]):
                        if w < BASE:
                            bit = bool(row >> w & 1) if w < N else False
                            self.add(-selected, port if bit else -port)
                        else:
                            prior = self.val[w-BASE][row]
                            self.add(-selected, -port, prior)
                            self.add(-selected, port, -prior)
                a, o, neg = self.ops[j]
                self.add(-a, -x, -y, z); self.add(-a, x, -z); self.add(-a, y, -z)
                self.add(-o, x, y, -z); self.add(-o, -x, z); self.add(-o, -y, z)
                self.add(-neg, x, z); self.add(-neg, -x, -z)
        self.add(self.ops[0][0])
        self.add(self.sel[0][0][4]); self.add(self.sel[0][1][6])
        for row, bit in enumerate(self.target):
            self.add(self.val[-1][row] if bit else -self.val[-1][row])

    def v(self, key): return self.pool.id(key)
    def add(self, *lits): self.cnf.append(list(lits))
    def one(self, lits):
        self.cnf.extend(CardEnc.equals(lits, bound=1, vpool=self.pool,
                                      encoding=EncType.seqcounter).clauses)

    def fixed(self, gates):
        assert len(gates) == self.bound
        return [lit for j, (op, a, b) in enumerate(gates)
                for lit in [self.ops[j][['and','or','not'].index(op)],
                            self.sel[j][0][a], self.sel[j][1][b]]]

    def decode(self, model):
        positive = {v for v in model if v > 0}
        return [[['and','or','not'][next(q for q,v in enumerate(self.ops[j]) if v in positive)],
                 next(w for w,v in enumerate(self.sel[j][0]) if v in positive),
                 next(w for w,v in enumerate(self.sel[j][1]) if v in positive)]
                for j in range(self.bound)]


def baseline():
    source = (ROOT/'pequalnp-proofs/lean/PEqualNP/Outside/L_meta_1001.lean').read_text()
    raw = source.split('def C0 : Circuit :=', 1)[1].split('\n', 1)[0]
    original = [[op, [int(v) for v in refs.split(',')]]
                for op,refs in re.findall(r'GateOp\.(and|or), \[([^\]]*)\]', raw)]
    assert len(original) == 16
    assert evaluate_project(original, 24) == TARGET
    # Add the assigned first gate; the previously checked circuit may ignore it.
    shifted = [['and', [4,6]]]
    shifted += [[op, [r if r < N else r+1 for r in refs]] for op,refs in original]
    fixture = normalize_project(shifted, 25, 17)
    assert evaluate_free(fixture) == TARGET
    return fixture


def selftest():
    if inactive(): raise RuntimeError('Lease inactive; tests stopped')
    started = time.monotonic()
    rng = random.Random(670007)
    count = 0
    for _ in range(160):
        length = rng.randrange(1, 16)
        gates = [['and', [4,6]]]
        for j in range(1, length):
            op = rng.choice(['and','or','not'])
            refs = [rng.randrange(N+j+5) for _ in range(rng.randrange(3))]
            gates.append([op, refs])
        output = rng.randrange(N+length+5)
        normalized = normalize_project(gates, output, 15)
        assert evaluate_project(gates, output) == evaluate_free(normalized)
        count += 1
    fixture = baseline()
    enc = Encoding(17)
    with Solver(name='cadical300', bootstrap_with=enc.cnf.clauses) as s:
        assert s.solve(assumptions=enc.fixed(fixture)) is True
        decoded = enc.decode(s.get_model())
        assert decoded == fixture
        assert evaluate_free(decoded) == TARGET
    # The same fixed circuit cannot compute a truth table with one bit flipped.
    bad = TARGET.copy(); bad[0] = not bad[0]
    wrong = Encoding(17, bad)
    with Solver(name='cadical300', bootstrap_with=wrong.cnf.clauses) as s:
        assert s.solve(assumptions=wrong.fixed(fixture)) is False
    # Exercise NOT and the false sentinel in a smaller fixed-formula query.
    small = [['and',4,6], ['not',BASE,BASE], ['or',FALSE,BASE+1],
             ['not',FALSE,FALSE], ['and',BASE+2,BASE+3], ['not',BASE+4,BASE+4]]
    truth = evaluate_free(small)
    small_enc = Encoding(6, truth)
    with Solver(name='cadical300', bootstrap_with=small_enc.cnf.clauses) as s:
        assert s.solve(assumptions=small_enc.fixed(small)) is True
    result = {'status':'PASS','utc':utc(),'seconds':time.monotonic()-started,
              'normalization_cases':count,'rows_per_case':ROWS,'baseline_fixture_gates':17,
              'fixed_baseline':'SAT','one_bit_mismatch':'UNSAT',
              'fixed_NOT_and_constants':'SAT','program_sha256':sha(__file__)}
    save(HERE/'selftest.json', result); save(HERE/'baseline-fixture.json', fixture)
    print(json.dumps(result), flush=True)


def worker(args):
    # A hard address-space ceiling protects the shared environment.
    resource.setrlimit(resource.RLIMIT_AS, (3584 << 20, 3584 << 20))
    if inactive(): raise RuntimeError('Lease inactive before encoding')
    out = Path(args.output); out.mkdir(exist_ok=True)
    started = time.monotonic()
    enc = Encoding(15)
    cnf_path = out/'shard7.cnf'
    enc.cnf.to_file(str(cnf_path))
    metadata = {'status':'RUNNING','started_utc':utc(),'shard':7,'bound':15,
                'first_gate':['and',4,6],'inputs':9,'truth_rows':ROWS,
                'false_sentinel':True,'free_true':False,'not_budget':'unrestricted',
                'pruning':['commutative fanin ordering','NOT unused port duplicated'],
                'variables':enc.pool.top,'clauses':len(enc.cnf.clauses),
                'cnf_sha256':sha(cnf_path),'program_sha256':sha(__file__),
                'pysat_solver':'cadical300','wall_bound_seconds':args.seconds,
                'proof_format':'binary DRAT','proof_verified':False,
                'lean_verified':False,'global_L670_proved':False}
    save(out/'result.json', metadata)
    print(json.dumps({k:metadata[k] for k in ['status','variables','clauses','cnf_sha256']}),flush=True)
    status = None; reason = None
    with Solver(name='cadical300', bootstrap_with=enc.cnf.clauses, with_proof=True) as solver:
        while status is None:
            if inactive(): reason='lease_inactive'; break
            if (out/'STOP').exists(): reason='stop_file'; break
            if time.monotonic()-started >= args.seconds: reason='wall_time'; break
            if shutil.disk_usage(out).free < (2 << 30): reason='disk_reserve'; break
            solver.conf_budget(args.chunk)
            status = solver.solve_limited(expect_interrupt=True)
            stats = solver.accum_stats()
            metadata.update(elapsed_seconds=round(time.monotonic()-started,3),
                            stats=stats,utc=utc(),rss_max_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
            save(out/'progress.json', metadata)
            print(json.dumps({'elapsed_seconds':metadata['elapsed_seconds'],
                              'stats':stats,'answer':status}),flush=True)
            if os.fstat(solver.solver.prfile.fileno()).st_size > (4 << 30):
                reason='proof_size_limit'; break
        if status is True:
            gates=enc.decode(solver.get_model())
            assert gates[0]==['and',4,6]
            assert evaluate_free(gates)==TARGET
            ordinary=project_from_free(gates)
            assert evaluate_project(ordinary['gates'],ordinary['output'])==TARGET
            save(out/'witness-free.json',gates);save(out/'witness-project.json',ordinary)
            metadata['witness_gates']=len(ordinary['gates'])
        # Avoid duplicating a large temporary trace without sufficient disk.
        import pysolvers
        pysolvers.flushpr(solver.solver.prfp)
        trace_bytes = os.fstat(solver.solver.prfile.fileno()).st_size
        if shutil.disk_usage(out).free >= trace_bytes + (2 << 30):
            solver.solver.prfile.seek(0)
            proof=out/('shard7-unsat.drat.bin' if status is False else 'partial.drat.bin')
            with proof.open('wb') as dest:
                shutil.copyfileobj(solver.solver.prfile,dest,1<<20)
            metadata.update(proof_file=proof.name,proof_sha256=sha(proof),
                            proof_bytes=proof.stat().st_size,proof_retained=True)
        else:
            metadata.update(proof_retained=False,temporary_trace_bytes=trace_bytes,
                            proof_retention_reason='insufficient_disk_for_copy')
        metadata['stats']=solver.accum_stats()
    metadata.update(status='SAT' if status is True else 'UNSAT' if status is False else 'UNKNOWN',
                    stop_reason=reason,elapsed_seconds=round(time.monotonic()-started,3),completed_utc=utc())
    save(out/'result.json',metadata)
    print(json.dumps(metadata),flush=True)


def supervise(args):
    out=Path(args.output);out.mkdir(exist_ok=True)
    if inactive(): raise RuntimeError('Lease inactive; search not launched')
    command=[sys.executable,str(Path(__file__).resolve()),'--worker','--output',str(out.resolve()),
             '--seconds',str(args.seconds),'--chunk',str(args.chunk)]
    started=time.monotonic(); reason=None; process=None; code=None
    requested_signal = None
    def request_stop(signum, _frame):
        nonlocal requested_signal
        requested_signal = signum
    old_handlers = {sig: signal.signal(sig, request_stop) for sig in (signal.SIGTERM,signal.SIGINT)}
    try:
        with (out/'solver.log').open('w') as log:
            process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            while process.poll() is None:
                if requested_signal is not None: reason=f'supervisor_signal_{requested_signal}';break
                if inactive(): reason='lease_inactive';break
                if (out/'STOP').exists():reason='stop_file';break
                if time.monotonic()-started>args.seconds+45:reason='hard_wall_time';break
                time.sleep(2)
    except KeyboardInterrupt:
        reason='supervisor_keyboard_interrupt'
    except BaseException as exc:
        reason='supervisor_exception_'+type(exc).__name__
    finally:
        # Clean up only this Popen child, including on SIGTERM, Ctrl-C or errors.
        # Signal handlers stay non-raising until cleanup and result writing finish.
        if process is not None:
            if process.poll() is None:
                process.terminate()
                try: process.wait(timeout=10)
                except subprocess.TimeoutExpired:process.kill();process.wait()
            code=process.wait()
    try:
        result_path=out/'result.json'
        result=json.loads(result_path.read_text()) if result_path.exists() else {}
        if reason or code!=0 or result.get('status')=='RUNNING':
            result.update(status='UNKNOWN',stop_reason=reason or 'worker_failure',
                          worker_exit_code=code,completed_utc=utc(),elapsed_seconds=time.monotonic()-started)
            save(result_path,result)
        result['supervisor_reaped_child']=process is not None and process.poll() is not None
        save(result_path,result)
        print(json.dumps(result),flush=True)
    finally:
        for sig,handler in old_handlers.items():signal.signal(sig,handler)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--selftest',action='store_true')
    p.add_argument('--worker',action='store_true')
    p.add_argument('--seconds',type=int,default=1800)
    p.add_argument('--chunk',type=int,default=2000)
    p.add_argument('--output',default=str(HERE/'run-shard7'))
    a=p.parse_args()
    if a.selftest:selftest()
    elif a.worker:worker(a)
    else:supervise(a)
