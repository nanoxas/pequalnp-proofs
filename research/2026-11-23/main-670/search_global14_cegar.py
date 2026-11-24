#!/usr/bin/env python3
"""DRAFT reduced-row CEGAR for the frozen strengthened global14 class.

No new structural restriction is introduced. A partial-row SAT model is always
checked independently on all512 rows before it can be called a witness. Rebuild
at each refinement so a final UNSAT trace pairs with one exact saved subset CNF.
This file is not the current running solver. Launch requires an explicit --run.
The frozen base dependency is checked before import.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import itertools
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
BASE_PATH = HERE / 'search_global14_strengthened.py'
BASE_SHA = 'd0d299f313fe74c38552746a9e3d58a2659b6f6ee762e383a2425ce521b33880'
if hashlib.sha256(BASE_PATH.read_bytes()).hexdigest() != BASE_SHA:
    raise RuntimeError('Frozen reviewed base dependency changed')
spec = importlib.util.spec_from_file_location('l670_frozen_strengthened', BASE_PATH)
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
N, SPECIAL, CORE, BASE, FALSE, ROWS = (base.N, base.SPECIAL, base.CORE,
                                    base.BASE, base.FALSE, base.ROWS)
TARGET, EDGES = base.TARGET, base.EDGES
IDPool, CNF, CardEnc, EncType, Solver = (base.IDPool, base.CNF, base.CardEnc,
                                      base.EncType, base.Solver)
utc, sha, save, inactive = base.utc, base.sha, base.save, base.inactive

class Encoding:
    def __init__(self, bound=14, target=TARGET, rows=None):
        self.bound, self.target = bound, list(target)
        if len(self.target) != ROWS: raise ValueError('Target must contain all512 bits')
        supplied = list(range(ROWS)) if rows is None else list(rows)
        if any(type(row) is not int or not 0 <= row < ROWS for row in supplied):
            raise ValueError('Rows are actual integer assignment masks in0..511')
        self.rows = tuple(sorted(set(supplied)))
        if not self.rows: raise ValueError('At least one truth row is required')
        self.pool, self.cnf = IDPool(), CNF()
        self.ops = [[self.v(('op', j, q)) for q in range(3)] for j in range(bound)]
        self.sel = [[[self.v(('sel', j, side, w)) for w in range(BASE+j)]
                     for side in range(2)] for j in range(bound)]
        self.val = [{row: self.v(('val', j, row)) for row in self.rows} for j in range(bound)]
        for j in range(bound):
            self.one(self.ops[j])
            for side in self.sel[j]: self.one(side)
            for w in range(BASE+j):
                self.add(-self.ops[j][2], -self.sel[j][0][w], self.sel[j][1][w])
            for a in range(BASE+j):
                for b in range(a):
                    self.add(-self.sel[j][0][a], -self.sel[j][1][b])
            for row in self.rows:
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
        for row in self.rows:
            bit = self.target[row]
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


def initial_rows():
    """Actual row masks: low weights, cofactor extremes, pivotal orbit seeds."""
    edge_set = {tuple(sorted(edge)) for edge in EDGES}
    permutations = []
    for left in itertools.permutations(CORE):
        for right in itertools.permutations(SPECIAL):
            mapping = dict(zip(CORE, left)) | dict(zip(SPECIAL, right))
            perm = tuple(mapping[p] for p in range(N))
            if {tuple(sorted((perm[a], perm[b]))) for a, b in EDGES} == edge_set:
                permutations.append(perm)
    assert len(permutations) == 12
    representatives = {}
    for p in range(N):
        for q in range(N):
            if p == q: continue
            for bit in (0, 1):
                key = min((perm[p], perm[q], bit) for perm in permutations)
                representatives.setdefault(key, (p, q, bit))
    witnesses = []
    rows = {row for row in range(ROWS) if row.bit_count() <= 2}
    assert len(rows) == 46
    rows.add(ROWS - 1)
    rows.update((ROWS - 1) ^ (1 << p) for p in range(N))
    for p, q, bit in sorted(representatives):
        choices = [row for row in range(ROWS)
                   if not (row >> p & 1) and (row >> q & 1) == bit
                   and not TARGET[row] and TARGET[row | (1 << p)]]
        assert choices
        negative = min(choices, key=lambda row: (row.bit_count(), row))
        positive = negative | (1 << p)
        rows.update((negative, positive))
        witnesses.append({'input': p, 'fixed_input': q, 'fixed_value': bit,
                          'negative_mask': negative, 'positive_mask': positive})
    return sorted(rows), {'policy': 'weight0/1/2, all-ones, nine zero-cofactor extremes, pivotal orbit representatives',
                          'pivotal_cases_covered_by_orbits': 144,
                          'pivotal_orbit_count': len(witnesses),
                          'pivotal_witnesses': witnesses,
                          'graph_automorphisms': len(permutations)}


def assess_candidate(gates, target, selected_rows, batch=16):
    """Partial SAT is a refinement event unless all512 actual rows match."""
    if batch < 1: raise ValueError('A refinement must add at least one row')
    truth = base.evaluate_free(gates)
    if any(truth[row] != target[row] for row in selected_rows):
        raise AssertionError('Decoded circuit violates an encoded row')
    violated = [row for row in range(ROWS) if truth[row] != target[row]]
    if not violated:
        return {'status': 'FULL_WITNESS', 'full_rows_checked': ROWS,
                'violated_rows': [], 'added_rows': []}
    selected = set(selected_rows)
    assert all(row not in selected for row in violated)
    added = sorted(violated, key=lambda row: (row.bit_count(), row))[:batch]
    return {'status': 'REFINE', 'full_rows_checked': ROWS,
            'violated_rows': violated, 'added_rows': added}


def fixed_cnf_direct_check(enc, gates):
    """Verify one explicit semantic assignment, extending counter auxiliaries.

    This performs deterministic clause evaluation and unit propagation only.
    It never starts a SAT solver or searches circuit structures.
    """
    values = {}
    row_wires = {}
    for row in enc.rows:
        wires = [bool(row >> p & 1) for p in range(N)] + [False]
        for op, a, b in gates:
            wires.append(wires[a] and wires[b] if op == 'and' else
                         wires[a] or wires[b] if op == 'or' else not wires[a])
        row_wires[row] = wires
    for variable, key in enc.pool.id2obj.items():
        kind = key[0]
        if kind == 'op':
            _, j, q = key; values[variable] = ['and', 'or', 'not'][q] == gates[j][0]
        elif kind == 'sel':
            _, j, side, wire = key; values[variable] = gates[j][side + 1] == wire
        elif kind == 'val':
            _, j, row = key; values[variable] = row_wires[row][BASE + j]
        elif kind == 'port':
            _, j, side, row = key; values[variable] = row_wires[row][gates[j][side + 1]]
        elif kind == 'raw_reader':
            _, j, p = key; values[variable] = p in gates[j][1:]
        elif kind == 'right_raw':
            _, j = key; values[variable] = gates[j][2] < N
        else:
            raise AssertionError(('Unexpected named variable', key))
    while True:
        changed = False
        for clause in enc.cnf.clauses:
            if any(abs(lit) in values and values[abs(lit)] == (lit > 0) for lit in clause):
                continue
            unassigned = [lit for lit in clause if abs(lit) not in values]
            if not unassigned: return False
            if len(unassigned) == 1:
                lit = unassigned[0]
                values[abs(lit)] = lit > 0
                changed = True
        if not changed: break
    # Sequential-counter residual clauses admit the false extension here.
    for variable in range(1, enc.pool.top + 1): values.setdefault(variable, False)
    assert all(any(values[abs(lit)] == (lit > 0) for lit in clause)
               for clause in enc.cnf.clauses), 'Explicit auxiliary extension failed'
    return True


def row_refactor_audit():
    """The copied encoding differs from the frozen class only in row selection."""
    original = BASE_PATH.read_text()
    original = original[original.index('class Encoding:'):original.index('\ndef baseline():')]
    expected = original.replace('def __init__(self, bound=14, target=TARGET):',
                                'def __init__(self, bound=14, target=TARGET, rows=None):', 1)
    expected = expected.replace('self.bound, self.target = bound, list(target)',
        """self.bound, self.target = bound, list(target)
        if len(self.target) != ROWS: raise ValueError('Target must contain all512 bits')
        supplied = list(range(ROWS)) if rows is None else list(rows)
        if any(type(row) is not int or not 0 <= row < ROWS for row in supplied):
            raise ValueError('Rows are actual integer assignment masks in0..511')
        self.rows = tuple(sorted(set(supplied)))
        if not self.rows: raise ValueError('At least one truth row is required')""", 1)
    expected = expected.replace("self.val = [[self.v(('val', j, row)) for row in range(ROWS)] for j in range(bound)]",
                                "self.val = [{row: self.v(('val', j, row)) for row in self.rows} for j in range(bound)]", 1)
    expected = expected.replace('for row in range(ROWS):', 'for row in self.rows:')
    expected = expected.replace('for row, bit in enumerate(self.target):\n            self.add',
                                'for row in self.rows:\n            bit = self.target[row]\n            self.add', 1)
    actual = Path(__file__).read_text()
    actual = actual[actual.index('class Encoding:'):actual.index('\ndef initial_rows():')]
    assert actual.strip() == expected.strip()
    return {'frozen_base_sha256': BASE_SHA,
            'structural_class_changes': 'none; only row-indexed allocations and equations changed',
            'exact_source_transform_match': True}


def static_selftest():
    if inactive(): raise RuntimeError('Lease inactive; tests stopped')
    started = time.monotonic()
    audit = row_refactor_audit()
    rows, policy = initial_rows()
    fixture = base.baseline()
    extended = base.not_fixture(fixture)
    control = [bool(row) for row in range(ROWS)]
    checks = []
    for name, chosen in [('initial', rows), ('sparse_actual_masks', [0, 17, 260, 511]),
                         ('all512', list(range(ROWS)))]:
        enc = Encoding(14, control, chosen)
        assert fixed_cnf_direct_check(enc, fixture)
        checks.append({'rows': name, 'row_count': len(chosen), 'explicit_model': 'PASS'})
    enc = Encoding(16, control, rows)
    assert fixed_cnf_direct_check(enc, extended)
    bad = control.copy(); bad[0] = not bad[0]
    assert fixed_cnf_direct_check(Encoding(14, bad, rows), fixture) is False
    unseen = next(row for row in range(ROWS) if row not in set(rows))
    hidden_bad = control.copy(); hidden_bad[unseen] = not hidden_bad[unseen]
    assert fixed_cnf_direct_check(Encoding(14, hidden_bad, rows), fixture)
    assessment = assess_candidate(fixture, hidden_bad, rows)
    assert assessment['status'] == 'REFINE' and assessment['added_rows'] == [unseen]
    assert fixed_cnf_direct_check(Encoding(14, hidden_bad, rows + [unseen]), fixture) is False
    assert assess_candidate(fixture, control, rows)['status'] == 'FULL_WITNESS'
    enc = Encoding(14, TARGET, rows)
    result = {'status': 'STATIC_CONTROLS_PASS', 'utc': utc(),
              'seconds': round(time.monotonic() - started, 3),
              'program_sha256': sha(__file__), **audit,
              'solver_started': False, 'initial_row_count': len(rows),
              'initial_rows': rows, 'seed_policy': policy,
              'initial_variables': enc.pool.top, 'initial_clauses': len(enc.cnf.clauses),
              'all512_variables': 22793, 'all512_clauses': 395638,
              'fixed_row_controls': checks, 'NOT_false_control': 'PASS',
              'encoded_bit_mismatch_detected': True,
              'unseen_bit_mismatch_refined_then_detected': True,
              'full_witness_requires_all512_rows': True,
              'scope': 'Direct fixed-assignment CNF and refinement controls only; no target search or UNSAT result'}
    save(HERE / 'global14-cegar-static-selftest.json', result)
    print(json.dumps(result), flush=True)


def solver_selftest():
    """Three fixed-CNF controls, to run only after the active search ends."""
    if inactive(): raise RuntimeError('Lease inactive; tests stopped')
    started = time.monotonic()
    rows, _ = initial_rows()
    control = [bool(row) for row in range(ROWS)]
    fixture = base.baseline(); extended = base.not_fixture(fixture)
    enc = Encoding(14, control, rows)
    with Solver(name='cadical300', bootstrap_with=enc.cnf.clauses) as solver:
        assert solver.solve(assumptions=enc.fixed(fixture)) is True
        assert base.evaluate_free(enc.decode(solver.get_model())) == control
    bad = control.copy(); bad[0] = not bad[0]
    enc = Encoding(14, bad, rows)
    with Solver(name='cadical300', bootstrap_with=enc.cnf.clauses) as solver:
        assert solver.solve(assumptions=enc.fixed(fixture)) is False
    enc = Encoding(16, control, rows)
    with Solver(name='cadical300', bootstrap_with=enc.cnf.clauses) as solver:
        assert solver.solve(assumptions=enc.fixed(extended)) is True
    result = {'status': 'PASS', 'utc': utc(), 'seconds': time.monotonic() - started,
              'program_sha256': sha(__file__), 'base_program_sha256': BASE_SHA,
              'fixed_OR_all': 'SAT', 'fixed_encoded_bit_mismatch': 'UNSAT',
              'fixed_NOT_false': 'SAT', 'initial_row_count': len(rows),
              'scope': 'Synthetic fixed-circuit controls; no target query'}
    save(HERE / 'global14-cegar-solver-selftest.json', result)
    print(json.dumps(result), flush=True)


def retain_trace(solver, directory, final_status):
    import pysolvers
    pysolvers.flushpr(solver.solver.prfp)
    size = os.fstat(solver.solver.prfile.fileno()).st_size
    if shutil.disk_usage(directory).free < size + (2 << 30):
        return {'proof_retained': False, 'temporary_trace_bytes': size,
                'proof_retention_reason': 'insufficient_disk_for_copy'}
    destination = directory / ('unsat.drat.bin' if final_status is False else 'partial.drat.bin')
    solver.solver.prfile.seek(0)
    with destination.open('wb') as stream:
        shutil.copyfileobj(solver.solver.prfile, stream, 1 << 20)
    return {'proof_retained': True, 'proof_file': destination.name,
            'proof_sha256': sha(destination), 'proof_bytes': destination.stat().st_size}


def worker(args):
    resource.setrlimit(resource.RLIMIT_AS, (3584 << 20, 3584 << 20))
    if inactive(): raise RuntimeError('Lease inactive before encoding')
    out = Path(args.output); out.mkdir(exist_ok=True)
    started = time.monotonic()
    rows, policy = initial_rows()
    metadata = {'status': 'RUNNING', 'started_utc': utc(), 'bound': 14, 'inputs': N,
                'query': 'reduced-row CEGAR for the frozen strengthened global14 class',
                'program_sha256': sha(__file__), 'base_program_sha256': BASE_SHA,
                'wall_bound_seconds': args.seconds, 'refinement_batch': args.batch,
                'seed_policy': policy, 'structural_constraints_changed': False,
                'complete_model_bridge_lean_checked': False, 'proof_verified': False,
                'lean_verified': False, 'global_L670_proved': False,
                'partial_row_SAT_is_witness': False, 'full_validation_rows': ROWS,
                'solver_rebuilt_each_refinement': True}
    save(out / 'result.json', metadata)
    for iteration in range(ROWS + 1):
        reason = None
        if inactive(): reason = 'lease_inactive'
        elif (out / 'STOP').exists(): reason = 'stop_file'
        elif time.monotonic() - started >= args.seconds: reason = 'wall_time'
        elif shutil.disk_usage(out).free < (2 << 30): reason = 'disk_reserve'
        if reason:
            metadata.update(status='UNKNOWN', stop_reason=reason)
            break
        directory = out / f'round-{iteration:03d}'
        directory.mkdir(exist_ok=False)
        enc = Encoding(14, TARGET, rows)
        cnf_path = directory / 'query.cnf'; enc.cnf.to_file(str(cnf_path))
        save(directory / 'rows.json', rows)
        phase = {'round': iteration, 'truth_rows': len(rows), 'row_ids': rows,
                 'variables': enc.pool.top, 'clauses': len(enc.cnf.clauses),
                 'cnf_sha256': sha(cnf_path), 'rows_sha256': sha(directory / 'rows.json'),
                 'proof_verified': False, 'started_utc': utc()}
        save(directory / 'phase.json', phase)
        metadata.update(round=iteration, truth_rows=len(rows), cnf_sha256=phase['cnf_sha256'],
                        phase_directory=directory.name, variables=enc.pool.top,
                        clauses=len(enc.cnf.clauses))
        save(out / 'result.json', metadata)
        status = None
        assessment = None
        with Solver(name='cadical300', bootstrap_with=enc.cnf.clauses, with_proof=True) as solver:
            while status is None:
                if inactive(): reason = 'lease_inactive'; break
                if (out / 'STOP').exists(): reason = 'stop_file'; break
                if time.monotonic() - started >= args.seconds: reason = 'wall_time'; break
                if shutil.disk_usage(out).free < (2 << 30): reason = 'disk_reserve'; break
                solver.conf_budget(args.chunk)
                status = solver.solve_limited(expect_interrupt=True)
                metadata.update(elapsed_seconds=round(time.monotonic() - started, 3),
                                utc=utc(), stats=solver.accum_stats(),
                                rss_max_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
                save(out / 'progress.json', metadata)
                if os.fstat(solver.solver.prfile.fileno()).st_size > (4 << 30):
                    reason = 'proof_size_limit'; break
            phase['stats'] = solver.accum_stats()
            if status is True:
                gates = enc.decode(solver.get_model())
                assert base.structural_cuts(gates) and base.reader_cuts(gates)
                assert base.strengthened_cuts(gates)
                assessment = assess_candidate(gates, TARGET, rows, args.batch)
                save(directory / 'candidate.json', {'gates': gates, **assessment})
                phase['status'] = 'FULL_WITNESS' if assessment['status'] == 'FULL_WITNESS' else 'PARTIAL_SAT_REFINED'
                if assessment['status'] == 'FULL_WITNESS':
                    ordinary = base.project_from_free(gates)
                    assigned = base.prepend_assigned_gate(ordinary)
                    assert base.evaluate_project(ordinary['gates'], ordinary['output']) == TARGET
                    assert len(assigned['gates']) == 15 and assigned['gates'][0] == ['and', [4, 6]]
                    assert base.evaluate_project(assigned['gates'], assigned['output']) == TARGET
                    save(out / 'witness-global14.json', ordinary)
                    save(out / 'witness-assigned15.json', assigned)
                    metadata.update(status='SAT', full_rows_verified=ROWS, witness_gates=14,
                                    assigned_witness_gates=15)
                else:
                    new_rows = sorted(set(rows) | set(assessment['added_rows']))
                    assert len(new_rows) > len(rows)
                    rows = new_rows
                    phase['refinement'] = assessment
            elif status is False:
                phase.update(status='UNSAT', **retain_trace(solver, directory, status))
                metadata.update(status='UNSAT', certificate_check_pending=True,
                                proof_verified=False, **{k: phase[k] for k in phase if k.startswith('proof_')})
            else:
                phase.update(status='UNKNOWN', stop_reason=reason,
                             **retain_trace(solver, directory, status))
                metadata.update(status='UNKNOWN', stop_reason=reason)
        phase['completed_utc'] = utc(); save(directory / 'phase.json', phase)
        print(json.dumps({'round': iteration, 'status': phase['status'],
                          'truth_rows': phase['truth_rows'], 'elapsed_seconds': time.monotonic() - started}), flush=True)
        if status is not True or assessment['status'] == 'FULL_WITNESS': break
    else:
        raise AssertionError('Strict row growth bounds the number of refinements')
    metadata.update(completed_utc=utc(), elapsed_seconds=round(time.monotonic() - started, 3))
    save(out / 'result.json', metadata)
    print(json.dumps(metadata), flush=True)


def supervise(args):
    out=Path(args.output);out.mkdir(exist_ok=True)
    if inactive(): raise RuntimeError('Lease inactive; search not launched')
    command=[sys.executable,str(Path(__file__).resolve()),'--worker','--output',str(out.resolve()),
             '--seconds',str(args.seconds),'--chunk',str(args.chunk),'--batch',str(args.batch)]
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


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--static-selftest', action='store_true')
    mode.add_argument('--selftest', action='store_true')
    mode.add_argument('--worker', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--seconds', type=int, default=1800)
    parser.add_argument('--chunk', type=int, default=2000)
    parser.add_argument('--batch', type=int, default=16)
    parser.add_argument('--output', default=str(HERE / 'run-global14-cegar'))
    arguments = parser.parse_args()
    if arguments.seconds <= 0 or arguments.chunk <= 0 or arguments.batch <= 0:
        parser.error('Resource bounds and refinement batch must be positive')
    if arguments.static_selftest: static_selftest()
    elif arguments.selftest: solver_selftest()
    elif arguments.worker: worker(arguments)
    else:
        if (Path(arguments.output) / 'result.json').exists():
            raise RuntimeError('Use a new output directory; completed or interrupted runs are preserved')
        supervise(arguments)
