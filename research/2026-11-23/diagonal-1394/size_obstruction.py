#!/usr/bin/env python3
"""Integer arithmetic audit of the elementary active-input/Moore obstruction.

This checks an extremal necessary inequality, not circuit existence or UNSAT.
No graph or circuit search is performed.
"""
import json
from pathlib import Path


def elementary_necessary(v):
    # v <= 2s and v <= 2N, while a nonempty diagonal family needs J >= 1.
    smin = (v + 1) // 2
    nmin = smin
    jmin = 1
    required_e = 400 * (smin + jmin) + 16 * nmin + 1
    # Adding Cauchy/2-path inequalities on both bipartition classes gives:
    # 2E^2 <= vE + (m*l)(v-2), with m*l <= floor(v^2/4).
    slack = v * required_e + (v*v//4)*(v-2) - 2*required_e*required_e
    return {'active_vertices':v,'minimum_s':smin,'minimum_N':nmin,'minimum_J':jmin,
            'required_edge_count':required_e,'extremal_inequality_slack':slack,
            'not_excluded_by_this_inequality':slack>=0}

def connected_cones_necessary(v):
    # Productive factor pairs have a common line input ancestor. Their union
    # therefore has at most J components, giving v <= s+J.
    nmin = (v + 1) // 2
    required_e = 400 * v + 16 * nmin + 1
    slack = v * required_e + (v*v//4)*(v-2) - 2*required_e*required_e
    return {'active_vertices':v,'minimum_s_plus_J':v,'minimum_N':nmin,
            'required_edge_count':required_e,'extremal_inequality_slack':slack,
            'not_excluded_by_this_inequality':slack>=0}

first = next(v for v in range(2,2000000) if connected_cones_necessary(v)['not_excluded_by_this_inequality'])
old_first = next(v for v in range(2,1000000) if elementary_necessary(v)['not_excluded_by_this_inequality'])
result = {
 'task':'L-meta-1394',
 'status':'Necessary obstruction only; no counterexample and no universal proof.',
 'first_active_vertex_count_not_excluded':first,
 'necessary_gate_count_at_least':first-1,
 'necessary_N_at_least':(first+1)//2,
 'necessary_one_component_active_vertices_at_least':first,
 'boundary_checks':[connected_cones_necessary(v) for v in range(first-4,first+2)],
 'earlier_weaker_obstruction':{
   'first_active_vertices':old_first,
   'minimum_s_and_N':(old_first+1)//2,
   'boundary_checks':[elementary_necessary(v) for v in range(old_first-2,old_first+2)]},
 'mathematical_premises':[
  'Every counted pair has one factor false on line-only and point-only but true on the pair.',
  'That factor depends on both inputs; both occur among gate input slots.',
  'Both factors of a productive product depend on the line coordinate, so their ancestor cones share that input vertex and their union is connected.',
  'The cone union over productive products has at most J components. With g internal gates and q input vertices, q <= g+J <= s+J.',
  'All active endpoints belong to that cone union, so v <= s+J, while v <= 2N.',
  'The counted incidence graph is bipartite and C4-free.',
  'Counting ordered two-paths on either side and applying Cauchy gives 2E^2 <= vE + ab(v-2).',
  'If each wiring component has at most 1330082 active endpoints, Moore implies e_i <= 408*v_i. Summing contradicts the required bound.',
  'Hence one connected wiring component has at least 1330083 active endpoints; its fanin count forces at least 1330082 internal gates.',
  'The lower bound on N concerns the declared equal side size, not a separate lower bound on each active side.'
 ]}
p=Path(__file__).with_name('size-obstruction.json')
p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
