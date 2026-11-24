#!/usr/bin/env python3
"""Strengthened necessary global14 class for original L670 range7.

This separately versioned model preserves the running base source. It adds:
core raw-input reader count at most2, two readers imply bothOR, no raw-rawAND,
every raw-rawOR endpoint has a second reader, and a canonical first gate from
NOT(0), OR(0,1), OR(0,2), OR(0,3). The orbit-minimum construction is compatible
with full greedy maximum-fanin ordering; see the separate completeness note.

All512 assignments and arbitrary NOT count remain. Every count is of actual
reader gates, not duplicated input ports. The positive control is deliberately
nonminimal and computes OR of all inputs; it tests this conservative encoding,
not the graph lower bound. No search is launched by source generation.

Base source SHA256:
9aa106bf7e24d1c56cc9ab01cd559d1539d0246acfef691fc5220ee5106aca05.
"""

from pathlib import Path
import argparse
import hashlib
import json
import os
import random
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
SPECIAL = (4, 6, 7)
CORE = (0, 1, 2, 3, 5, 8)
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
        data = json.loads(LEASE.read_text())
        expires = data.get('lease', {}).get('expires_at')
        if not expires or data.get('inactive'): return True
        deadline = datetime.fromisoformat(expires.replace('Z', '+00:00'))
        return datetime.now(timezone.utc) >= deadline
    except (OSError, ValueError, TypeError):
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


def normalize_project_base(gates, output, bound):
    """Basic list-semantics normalization with no prescribed first gate."""
    assert len(gates) <= bound
    if N <= output < N + len(gates):
        prefix = output - N + 1
        target = output + 1
    elif output < N:
        prefix = 0
        target = output
    else:
        prefix = 0
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


def structural_cuts(gates):
    """The four additional constraints, independently checked as predicates."""
    if not gates: return False
    for j, (op, a, b) in enumerate(gates):
        if not (0 <= a <= b < BASE+j): return False
        if op == 'not' and a != b: return False
        if op in ('and','or') and FALSE in (a,b): return False
        if op == 'not' and a >= BASE and gates[a-BASE][0] == 'not': return False
        if j >= 1 and b < gates[j-1][2]: return False
        if 0 <= j < len(gates)-1:
            wire = BASE+j
            if not any(wire == aa or (oo != 'not' and wire == bb)
                       for oo,aa,bb in gates[j+1:]): return False
    return True


def reader_cuts(gates):
    """Actual gate readers, not a count of repeated input ports."""
    for c in SPECIAL:
        readers = [(op,a,b) for op,a,b in gates
                   if a == c or (op != 'not' and b == c)]
        if len(readers) != 1: return False
        op,a,b = readers[0]
        if op != 'or': return False
        other = b if a == c else a
        if other < BASE: return False
    return True


def strengthened_cuts(gates):
    """Additional necessary predicates, separate from generic normalization."""
    if not gates:return False
    readers={c:[j for j,(op,a,b) in enumerate(gates)
                if a==c or (op!='not' and b==c)] for c in range(N)}
    for c in CORE:
        if len(readers[c])>2:return False
        if len(readers[c])==2 and any(gates[j][0]!='or' for j in readers[c]):return False
    for op,a,b in gates:
        if a<N and b<N:
            if op=='and':return False
            if op=='or' and any(len(readers[c])<2 for c in {a,b}):return False
    return tuple(gates[0]) in [('not',0,0),('or',0,1),('or',0,2),('or',0,3)]


def normalize_project(gates, output, bound):
    """Complete four-stage map for nonconstant outputs and bounds at least2."""
    assert bound >= 2
    base = normalize_project_base(gates, output, bound)
    values = {w:w for w in range(BASE)}
    clean = []
    # Stage1: false-operand and direct-double-NOT cleanup, left to right.
    for j, (op, old_a, old_b) in enumerate(base):
        a,b = values[old_a], values[old_b]
        if op == 'and' and FALSE in (a,b):
            value = FALSE
        elif op == 'or' and FALSE in (a,b):
            value = b if a == FALSE else a
        elif op == 'not' and a >= BASE and clean[a-BASE][0] == 'not':
            value = clean[a-BASE][1]
        else:
            if op == 'not': b = a
            else: a,b = sorted((a,b))
            value = BASE + len(clean)
            clean.append([op,a,b])
        values[BASE+j] = value
    current_output = values[BASE+len(base)-1]
    # The actual target is nonconstant; a constant-false result is out of scope.
    assert current_output != FALSE
    # Stage2: retain the output cone.
    live = set()
    def mark(w):
        if w < BASE or w-BASE in live: return
        j = w-BASE;live.add(j)
        op,a,b = clean[j];mark(a)
        if op != 'not':mark(b)
    mark(current_output)
    # Stage3: greedily schedule every ready gate, including the first.
    mapping = {w:w for w in range(BASE)}
    ordered = []
    remaining = set(live)
    while remaining:
        ready = []
        for j in remaining:
            op,a,b = clean[j]
            if a in mapping and b in mapping:
                aa,bb = sorted((mapping[a],mapping[b]))
                ready.append(((bb,aa,['and','or','not'].index(op),j),j,op,aa,bb))
        assert ready, 'The cleaned list is a DAG'
        _,j,op,a,b = min(ready)
        mapping[BASE+j] = BASE + len(ordered)
        ordered.append([op,a,b]);remaining.remove(j)
    target = mapping[current_output]
    # Stage4: aliases preserve liveness and increasing maximum-fanin keys.
    while len(ordered) < bound:
        ordered.append(['or',target,target])
        target = BASE + len(ordered) - 1
    assert len(ordered) == bound and target == BASE+bound-1
    assert structural_cuts(ordered)
    return ordered


def project_from_free(gates):
    """Literal exact-cost translation: false is one permanently unavailable read."""
    unavailable = N + len(gates)
    def wire(w):
        if w < N: return w
        if w == FALSE: return unavailable
        return w - 1
    built = [[op, [wire(a)] if op == 'not' else [wire(a), wire(b)]]
             for op,a,b in gates]
    return {'gates': built, 'output': N + len(built) - 1}


def prepend_assigned_gate(project):
    """Return a literal witness for the original prescribed-first range."""
    shifted = [['and', [4, 6]]]
    shifted += [[op, [w if w < N else w+1 for w in refs]]
                for op, refs in project['gates']]
    output = project['output']
    return {'gates': shifted, 'output': output if output < N else output+1}


class Encoding:
    def __init__(self, bound=14, target=TARGET):
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
        # A least global witness has no unused gate; schedule the entire DAG.
        for j in range(0, bound-1):
            wire = BASE+j
            self.add(*[self.sel[t][side][wire] for t in range(j+1,bound) for side in range(2)])
        for j in range(1, bound):
            for old_max in range(BASE+j-1):
                for new_max in range(old_max):
                    self.add(-self.sel[j-1][1][old_max],-self.sel[j][1][new_max])
        for j in range(bound):
            for op in (0,1):
                for side in range(2):self.add(-self.ops[j][op],-self.sel[j][side][FALSE])
            for earlier in range(j):
                self.add(-self.ops[j][2],-self.sel[j][0][BASE+earlier],-self.ops[earlier][2])
        # Exactly one actual OR reader of each special raw input. Sorted
        # fanins put it on the left; the other operand must be a gate wire.
        for c in SPECIAL:
            self.one([self.sel[j][0][c] for j in range(bound)])
            for j in range(bound):
                self.add(-self.sel[j][1][c])
                self.add(-self.sel[j][0][c], self.ops[j][1])
                for w in range(BASE):
                    self.add(-self.sel[j][0][c], -self.sel[j][1][w])
        # Count reader gates once, even when a raw input fills both ports.
        self.hits=[[self.v(('raw_reader',j,c)) for c in range(N)] for j in range(bound)]
        for j in range(bound):
            for c in range(N):
                hit=self.hits[j][c]
                self.add(-self.sel[j][0][c],hit)
                self.add(-self.sel[j][1][c],hit)
                self.add(-hit,self.sel[j][0][c],self.sel[j][1][c])
        for c in CORE:
            self.cnf.extend(CardEnc.atmost([self.hits[j][c] for j in range(bound)],
                bound=2,vpool=self.pool,encoding=EncType.seqcounter).clauses)
            for j in range(bound):
                for k in range(j+1,bound):
                    self.add(-self.hits[j][c],-self.hits[k][c],self.ops[j][1])
                    self.add(-self.hits[j][c],-self.hits[k][c],self.ops[k][1])
        for j in range(bound):
            # With sorted ports, right-raw is equivalent to both ports raw.
            right_raw=self.v(('right_raw',j))
            for c in range(N):self.add(-self.sel[j][1][c],right_raw)
            self.add(-right_raw,*self.sel[j][1][:N])
            self.add(-self.ops[j][0],-right_raw)
            for c in range(N):
                self.add(-self.ops[j][1],-right_raw,-self.hits[j][c],
                    *[self.hits[k][c] for k in range(bound) if k!=j])
        # Joint orbit-minimum + greedy normalization, not relabel-old-first.
        self.add(self.sel[0][0][0])
        self.add(-self.ops[0][0])
        self.add(-self.ops[0][1],self.sel[0][1][1],self.sel[0][1][2],self.sel[0][1][3])
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
    """Fourteen-gate nonminimal OR-all control satisfying the added clauses."""
    gates=[['or',[0,1]],['or',[0,N]],['or',[1,N+1]]]
    output=N+2
    for c in (2,3,5,8,4,6,7):
        gates.append(['or',[c,output]])
        output=N+len(gates)-1
    while len(gates)<14:
        gates.append(['or',[output,output]])
        output=N+len(gates)-1
    target=[bool(row) for row in range(ROWS)]
    assert evaluate_project(gates,output)==target
    fixture=normalize_project(gates,output,14)
    assert evaluate_free(fixture)==target
    assert reader_cuts(fixture) and strengthened_cuts(fixture)
    return fixture


def not_fixture(fixture):
    """The baseline extended by a counted NOT(false) and an AND identity."""
    original=project_from_free(fixture)
    gates=original['gates']
    gates.append(['not',[N+len(fixture)+2]])  # unavailable, hence false
    gates.append(['and',[original['output'],N+len(fixture)]])
    result=normalize_project(gates,N+len(gates)-1,len(gates))
    assert evaluate_free(result)==evaluate_free(fixture) and reader_cuts(result)
    assert strengthened_cuts(result)
    assert any(op=='not' and a==FALSE for op,a,b in result)
    return result


def selftest(with_solver=True):
    if inactive(): raise RuntimeError('Lease inactive; tests stopped')
    started=time.monotonic()
    rng=random.Random(670014)
    count=attempted=0
    while count<160:
        attempted+=1
        length=rng.randrange(0,15)
        gates=[]
        for j in range(length):
            op=rng.choice(['and','or','not'])
            refs=[rng.randrange(N+j+5) for _ in range(rng.randrange(3))]
            gates.append([op,refs])
        output=rng.randrange(N+length+5)
        original_truth=evaluate_project(gates,output)
        if all(original_truth) or not any(original_truth):continue
        normalized=normalize_project(gates,output,14)
        assert original_truth==evaluate_free(normalized)
        assert structural_cuts(normalized)
        count+=1
    fixture=baseline();extended=not_fixture(fixture)
    control_target=[bool(row) for row in range(ROWS)]
    assert structural_cuts(fixture) and structural_cuts(extended)
    assert reader_cuts(fixture) and reader_cuts(extended)
    assert strengthened_cuts(fixture) and strengthened_cuts(extended)
    for control in (fixture, extended):
        shifted=prepend_assigned_gate(project_from_free(control))
        assert evaluate_project(shifted['gates'],shifted['output'])==control_target
    result={'status':'NORMALIZATION_PASS','utc':utc(),'seconds':time.monotonic()-started,
            'normalization_cases':count,'attempted_cases':attempted,'rows_per_case':ROWS,
            'nonconstant_scope':True,'all_four_structural_constraints_hold':True,
            'reader_conditions_checked_on_controls':True,
            'reader_preservation_scope':'least14-gate witnesses, paper reduction; not arbitrary cleanup',
            'control_target':'OR of all9 raw inputs; deliberately nonminimal',
            'baseline_fixture_gates':14,'NOT_false_fixture_gates':16,
            'cnf_checks_run':False,'program_sha256':sha(__file__)}
    save(HERE/'global14-strengthened-baseline-fixture.json',fixture)
    save(HERE/'global14-strengthened-NOT-fixture.json',extended)
    if not with_solver:
        save(HERE/'global14-strengthened-normalization-selftest.json',result)
        print(json.dumps(result),flush=True)
        return
    enc=Encoding(14,control_target)
    with Solver(name='cadical300',bootstrap_with=enc.cnf.clauses) as solver:
        assert solver.solve(assumptions=enc.fixed(fixture)) is True
        decoded=enc.decode(solver.get_model())
        assert decoded==fixture and evaluate_free(decoded)==control_target
    bad=control_target.copy();bad[0]=not bad[0]
    wrong=Encoding(14,bad)
    with Solver(name='cadical300',bootstrap_with=wrong.cnf.clauses) as solver:
        assert solver.solve(assumptions=wrong.fixed(fixture)) is False
    extended_enc=Encoding(16,control_target)
    with Solver(name='cadical300',bootstrap_with=extended_enc.cnf.clauses) as solver:
        assert solver.solve(assumptions=extended_enc.fixed(extended)) is True
    result.update(status='PASS',seconds=time.monotonic()-started,cnf_checks_run=True,
                  fixed_baseline='SAT',one_bit_mismatch='UNSAT',fixed_NOT_false='SAT')
    save(HERE/'global14-strengthened-selftest.json',result)
    print(json.dumps(result),flush=True)


def encode_only(args):
    if inactive():raise RuntimeError('Lease inactive; encoding stopped')
    out=Path(args.output);out.mkdir(exist_ok=True)
    enc=Encoding(14)
    path=out/'global14.cnf';enc.cnf.to_file(str(path))
    metadata={'status':'ENCODED_NOT_RUN','utc':utc(),'bound':14,'inputs':N,
              'truth_rows':ROWS,'variables':enc.pool.top,'clauses':len(enc.cnf.clauses),
              'program_sha256':sha(__file__),'cnf_sha256':sha(path),
              'cnf_bytes':path.stat().st_size,'first_gate':'one of four canonical representatives',
              'special_inputs':list(SPECIAL),'raw_other_operand_excluded':True,
              'core_reader_at_most_two':True,'two_core_readers_are_OR':True,
              'no_raw_raw_AND':True,'raw_raw_OR_endpoints_have_two_readers':True,
              'canonical_first_cases':[['not',0],['or',0,1],['or',0,2],['or',0,3]],
              'complete_model_bridge_lean_checked':False,'solver_started':False}
    save(out/'encoding.json',metadata);print(json.dumps(metadata),flush=True)


def worker(args):
    # A hard address-space ceiling protects the shared environment.
    resource.setrlimit(resource.RLIMIT_AS, (3584 << 20, 3584 << 20))
    if inactive(): raise RuntimeError('Lease inactive before encoding')
    out = Path(args.output); out.mkdir(exist_ok=True)
    started = time.monotonic()
    enc = Encoding(14)
    cnf_path = out/'global14.cnf'
    enc.cnf.to_file(str(cnf_path))
    metadata = {'status':'RUNNING','started_utc':utc(),'assigned_shard':7,'bound':14,
                'query':'strengthened necessary class of least global14-gate witnesses',
                'complete_model_bridge_lean_checked':False,
                'first_gate':'one of four canonical representatives','inputs':9,'truth_rows':ROWS,
                'false_sentinel':True,'free_true':False,'not_budget':'unrestricted',
                'pruning':['commutative fanin ordering','NOT unused port duplicated',
                           'all-gate liveness','maximum-fanin ordering from gate0 onward',
                           'no false operand at AND/OR','no direct NOT-of-NOT',
                           'each4,6,7 has oneORreader with gate-valued other operand',
                           'core inputs have at most2 actual readers; any two are OR',
                           'no raw-raw AND; raw-raw OR endpoints have another reader',
                           'four canonical first gates via joint orbit-minimum scheduling'],
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
            assert structural_cuts(gates) and reader_cuts(gates) and strengthened_cuts(gates)
            assert evaluate_free(gates)==TARGET
            ordinary=project_from_free(gates)
            assert evaluate_project(ordinary['gates'],ordinary['output'])==TARGET
            save(out/'witness-free.json',gates);save(out/'witness-project.json',ordinary)
            metadata['witness_gates']=len(ordinary['gates'])
            assigned=prepend_assigned_gate(ordinary)
            assert len(assigned['gates'])==15
            assert assigned['gates'][0]==['and',[4,6]]
            assert evaluate_project(assigned['gates'],assigned['output'])==TARGET
            save(out/'witness-assigned-shard15.json',assigned)
            metadata['assigned_shard_witness_gates']=15
        # Avoid duplicating a large temporary trace without sufficient disk.
        import pysolvers
        pysolvers.flushpr(solver.solver.prfp)
        trace_bytes = os.fstat(solver.solver.prfile.fileno()).st_size
        if shutil.disk_usage(out).free >= trace_bytes + (2 << 30):
            solver.solver.prfile.seek(0)
            proof=out/('global14-unsat.drat.bin' if status is False else 'partial.drat.bin')
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
    p.add_argument('--normalization-only',action='store_true')
    p.add_argument('--encode-only',action='store_true')
    p.add_argument('--seconds',type=int,default=1800)
    p.add_argument('--chunk',type=int,default=2000)
    p.add_argument('--output',default=str(HERE/'run-global14-strengthened'))
    a=p.parse_args()
    if a.encode_only:encode_only(a)
    elif a.normalization_only:selftest(with_solver=False)
    elif a.selftest:selftest()
    elif a.worker:worker(a)
    else:supervise(a)
