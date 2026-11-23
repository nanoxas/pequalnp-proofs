import argparse
import itertools
import json
import pathlib
import resource
import sys
import time

ROOT = pathlib.Path('/workspace/scratch/91448c28ebe7')
sys.path.insert(0, str(ROOT / 'heawood-search/vendor'))
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

N = 11
EDGES = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

def target(mask):
    return any(mask & (1 << u) and mask & (1 << v) for u,v in EDGES)

NEGATIVES = [m for m in range(1 << N) if not target(m) and
             all(target(m | (1 << u)) for u in range(N) if not m & (1 << u))]
POSITIVES = [(1 << u) | (1 << v) for u,v in EDGES]
ROWS = [(m, True) for m in POSITIVES] + [(m, False) for m in NEGATIVES]

def evaluate(circuit, mask):
    values = [bool(mask & (1 << i)) for i in range(N)]
    gate_values = []
    for gate in circuit['gates']:
        value = any(values[i] for i in gate['left']) and any(values[i] for i in gate['right'])
        values.append(value)
        gate_values.append(value)
    return any(gate_values[i] for i in circuit['output_gates']), gate_values

def verify(circuit):
    errors = []
    for mask in range(1 << N):
        value, _ = evaluate(circuit, mask)
        if value != target(mask):
            errors.append(mask)
    return errors

class Encoding:
    def __init__(self, count):
        self.count = count
        self.pool = IDPool()
        self.cnf = CNF()
        self.select = {}
        self.values = {}
        self.outputs = [self.pool.id(('out', g)) for g in range(count)]
        for g in range(count):
            for side in range(2):
                for term in range(N + g):
                    self.select[g,side,term] = self.pool.id(('select',g,side,term))
        for r,(mask,wanted) in enumerate(ROWS):
            for g in range(count):
                sides = []
                for side in range(2):
                    terms = []
                    for term in range(N + g):
                        selected = self.select[g,side,term]
                        if term < N:
                            if mask & (1 << term):
                                terms.append(selected)
                        else:
                            value = self.values[r,term-N]
                            term_value = self.pool.id(('term',r,g,side,term))
                            self.cnf.extend([[-term_value,selected],[-term_value,value],
                                             [term_value,-selected,-value]])
                            terms.append(term_value)
                    side_value = self.pool.id(('side',r,g,side))
                    for term_value in terms:
                        self.cnf.append([-term_value,side_value])
                    self.cnf.append([-side_value] + terms)
                    sides.append(side_value)
                value = self.pool.id(('gate',r,g))
                self.values[r,g] = value
                left,right = sides
                self.cnf.extend([[-value,left],[-value,right],[value,-left,-right]])
            if wanted:
                output_terms = []
                for g in range(count):
                    term_value = self.pool.id(('outterm',r,g))
                    selected = self.outputs[g]
                    value = self.values[r,g]
                    self.cnf.extend([[-term_value,selected],[-term_value,value],
                                     [term_value,-selected,-value]])
                    output_terms.append(term_value)
                self.cnf.append(output_terms)
            else:
                for g in range(count):
                    self.cnf.append([-self.outputs[g],-self.values[r,g]])

    def fix(self, circuit):
        clauses = []
        for g in range(self.count):
            for side,name in enumerate(['left','right']):
                selected = set(circuit['gates'][g][name])
                for term in range(N + g):
                    v = self.select[g,side,term]
                    clauses.append([v if term in selected else -v])
            clauses.append([self.outputs[g] if g in circuit['output_gates'] else -self.outputs[g]])
        return clauses

    def decode(self, model):
        positive = {v for v in model if v > 0}
        return {'gates':[
            {name:[term for term in range(N+g) if self.select[g,side,term] in positive]
             for side,name in enumerate(['left','right'])}
            for g in range(self.count)],
            'output_gates':[g for g in range(self.count) if self.outputs[g] in positive]}

def star_baseline():
    cover = next(c for k in range(N+1) for c in itertools.combinations(range(N),k)
                 if all(u in c or v in c for u,v in EDGES))
    circuit = {'gates':[
        {'left':[u], 'right':[b if a == u else a for a,b in EDGES if a == u or b == u]}
        for u in cover], 'output_gates':list(range(len(cover)))}
    assert len(cover) == 7 and not verify(circuit)
    return circuit

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--count',type=int,default=6)
    parser.add_argument('--conflicts',type=int,default=5000000)
    parser.add_argument('--baseline',action='store_true')
    parser.add_argument('--result',required=True)
    parser.add_argument('--cnf')
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_AS,(2 * 1024**3,)*2)
    assert len(NEGATIVES) == 24 and len(ROWS) == 40
    enc = Encoding(args.count)
    if args.baseline:
        baseline = star_baseline()
        assert args.count == len(baseline['gates'])
        enc.cnf.extend(enc.fix(baseline))
    if args.cnf:
        enc.cnf.to_file(args.cnf)
    print(json.dumps({'event':'encoded','and_gates':args.count,'rows':len(ROWS),
                      'variables':enc.pool.top,'clauses':len(enc.cnf.clauses)}),flush=True)
    start = time.monotonic()
    with Solver(name='cadical300',bootstrap_with=enc.cnf.clauses,use_timer=True) as solver:
        solver.conf_budget(args.conflicts)
        answer = solver.solve_limited()
        result = {'status':answer,'seconds':time.monotonic()-start,'and_gates':args.count,
                  'options':vars(args),'statistics':solver.accum_stats(),
                  'scope':'Exploratory full-function AND-count model with free OR; not a report of exhaustion for assigned binary-circuit shard.'}
        if answer:
            circuit = enc.decode(solver.get_model())
            errors = verify(circuit)
            assert not errors, errors[:10]
            result['circuit'] = circuit
            result['validated_all_2048_inputs'] = True
            _,values = evaluate(circuit,sum(1 << i for i in [2,3,4,9]))
            result['dirty_and_on_shard6'] = any(values)
    pathlib.Path(args.result).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)

if __name__ == '__main__':
    main()
