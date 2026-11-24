#!/usr/bin/env python3
"""Independent finite-data and support-algebra audit. No SAT or Lean call."""
import hashlib
import itertools
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent


def main():
    case=json.loads((HERE/'case.json').read_text())
    n=case['n'];sets=case['sets'];y=case['y'];k=y.bit_count();m=len(sets)
    expected=[set(range(3,11)),{0,3,11},{1,4,11},{2,5,11},
              {0,6,12},{1,7,12},{2,8,12},{0,1,9},{0,2,10},{1,2,3}]
    decoded=[{p for p in range(n) if S>>p&1} for S in sets]
    assert n==13 and y==7 and decoded==expected
    intersections=[len(a&b) for a,b in itertools.combinations(decoded,2)]
    assert len(intersections)==45 and max(intersections)==1
    assert all(2<=len(S)<n for S in decoded)
    heavy=[i for i,S in enumerate(sets) if not S&y]
    light=[i for i,S in enumerate(sets) if S&y]
    F=sum(sets[i].bit_count() if i in heavy else min(k,sets[i].bit_count()) for i in range(m))
    B=sum(max(min(k,S.bit_count())-1,0) for S in sets)
    A=sum(max(sets[i].bit_count()-1,0) for i in heavy)
    Q=sum(max(min(k,sets[i].bit_count())-2,0) for i in light)
    excess=sum(max(sets[i].bit_count()-k-1,0) for i in heavy)
    assert (F,B,A,Q,excess,heavy)==(35,20,7,9,4,[0])
    allowed=[(N,R) for N in range(B+k,F-m)
             for R in range(len(heavy),N+1) if F>N+R+m]
    assert allowed==[(23,1)]

    # Necessary support types in the equality partition. Allow every possible
    # foreign-target subset, even when no actual circuit could make them all.
    # This is a safe algebraic superset, not a circuit search.
    target=sets[0];universe=(1<<n)-1
    outside={0,universe}|{1<<p for p in range(n)}
    for foreign in sets[1:]:
        subset=foreign
        while subset:
            if subset.bit_count()>=2:outside.add(subset)
            subset=(subset-1)&foreign
    inside=lambda U:U.bit_count()>=2 and U&~target==0

    def gates(available):
        # Nullary AND/OR and unary aliases, followed by binary gates. Equal
        # fan-ins are included. Invalid/future references use support zero.
        yield 'and0',(),universe
        yield 'or0',(),0
        for a in available:
            yield 'alias',(a,),a
        for a,b in itertools.product(available,repeat=2):
            yield 'and',(a,b),a&b
            yield 'or',(a,b),a|b

    first=[]
    for op,args,U in gates(outside):
        if inside(U):
            assert op=='or' and all(a.bit_count()==1 for a in args)
            assert U.bit_count()==2
            first.append(U)
    first_supports=set(first)
    assert len(first_supports)==28
    maximum_second=0;second_cases=0
    for first_U in first_supports:
        for op,args,U in gates(outside|{first_U}):
            if inside(U):
                second_cases+=1
                maximum_second=max(maximum_second,U.bit_count())
                assert U.bit_count()<=3
                if op=='and':assert U.bit_count()<=2
    assert maximum_second==3 and target.bit_count()==8
    record={
      'status':'DATA_AND_SUPPORT_ALGEBRA_PASS','n':n,'m':m,'k':k,
      'pair_intersections_checked':45,'all_targets_nontrivial_and_proper':True,
      'F':F,'B':B,'A':A,'Q_light':Q,'H':len(heavy),'heavy_excess_beyond_k_plus_one':excess,
      'light_minterm_lower_bound':B+k,'heavy_minterm_lower_bound':A+len(light)+k,
      'necessary_violation_size_refund_pairs':allowed,
      'escapes_n_le_3k_plus_one':n>3*k+1,'escapes_excess_criterion':excess>k,
      'escapes_heavy_small_surplus_criterion':Q>len(heavy)+k+2,
      'foreign_support_superset_size':len(outside),
      'possible_first_heavy_class_supports':len(first_supports),
      'second_heavy_class_gate_cases_checked':second_cases,
      'maximum_second_heavy_class_support_size':maximum_second,
      'required_heavy_output_support_size':target.bit_count(),
      'paper_exclusion':'At the only possible size23, the equality partition gives exactly two gates in every light-assigned class. The heavy class cannot reach support8 with two gates.',
      'whole_exclusion_kernel_checked':False,'sat_runs':0,
      'scope':'Exact family arithmetic and finite support-transition audit; complete exclusion is a separate paper argument, not a solver certificate.',
      'case_sha256':hashlib.sha256((HERE/'case.json').read_bytes()).hexdigest(),
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (HERE/'independent-audit.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))


if __name__=='__main__':main()
