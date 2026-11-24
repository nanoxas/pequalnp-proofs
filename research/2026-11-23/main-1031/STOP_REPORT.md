# L-meta-1031 stopped research checkpoint

The parent reported that the shared lease returned HTTP 410 at
2026-11-24 00:23:41.548 UTC. All target work is stopped. No proof was submitted,
and no Lean compiler was run for this task. The public reason for the lease
ending is not established by the HTTP status.

The last batch had finished before its session was revisited: every planned
case has a completed JSON result, and the local solver batch had ended.
There are no UNKNOWN or interrupted solver results in this checkpoint. This
does not establish the general posted theorem.

## Exact completed computational cases

The local encoder uses binary AND/OR gates with two distinct valid earlier
inputs, last-gate output, all gates live, and a topological ordering with
nondecreasing largest input index. It checks every input assignment and
encodes the proper ancestor relation, rather than treating all earlier ANDs
as ancestors. SAT circuits are independently evaluated by a separate direct
routine on the entire truth table and their ownership sets are recomputed.

These results are ordinary SAT solver results, not kernel-checked certificates.
The files under `search/` retain solver conflict counts, elapsed times, complete
witnesses where present, and the exact restrictions.

| Graph | Size | Searched property | Result | Result file |
|---|---:|---|---|---|
| Path P4 | 3 | Any correct circuit | UNSAT | `p4-lower.json` |
| Path P4 | 4 | Some AND owns no edge | UNSAT | `p4-empty-4.json` |
| Path P4 | 4 | Some AND owns a nonstar edge set | UNSAT | `p4-nonstar.json` |
| Path P4 | 5 | Some AND owns no edge; positive control | SAT | `p4-empty-positive-control.json` |
| Two disjoint edges | 3 | Some AND owns no edge | UNSAT | `matching2-empty.json` |
| Cycle C5 | 4 | Any correct circuit | UNSAT | `c5-lower4.json` |
| Cycle C5 | 5 | Any correct circuit | UNSAT | `c5-lower5.json` |
| Cycle C5 | 6 | Any correct circuit | UNSAT | `c5-lower6.json` |
| Cycle C5 | 7 | Every AND owns a nonempty star | SAT | `c5-good-7.json` |
| Cycle C5 | 7 | Some AND owns no edge | UNSAT | `c5-empty7.json` |
| Cycle C5 | 7 | Some AND owns a nonstar edge set | UNSAT | `c5-nonstar7.json` |
| Cycle C6 | 7 | Any correct circuit | UNSAT | `c6-any-7.json` |
| Cycle C6 | 8 | Every AND owns a nonempty star | SAT | `c6-good-8.json` |
| Cycle C6 | 8 | Some AND owns no edge | UNSAT | `c6-empty-8.json` |
| Cycle C6 | 8 | Some AND owns a nonstar edge set | UNSAT | `c6-nonstar-8.json` |
| C5 with one leaf | 7 | Any correct circuit | UNSAT | `c5leaf-any-7.json` |
| C5 with one leaf | 8 | Every AND owns a nonempty star | SAT | `c5leaf-good-8.json` |
| C5 with one leaf | 8 | Some AND owns no edge | UNSAT | `c5leaf-empty-8.json` |
| C5 with one leaf | 8 | Some AND owns a nonstar edge set | UNSAT | `c5leaf-nonstar-8.json` |

The C6 and C5-with-leaf runs took between 0.25 and 11.67 seconds per case.
The source is `ownership_search.py`. This checkpoint contains no exhaustive
classification of all graphs of any given order.

## Criticality differs from ownership

For the path with edges `ab, bc, cd`, the following four-gate circuit is correct:

1. `g1 = a AND b`.
2. `g2 = g1 OR c`.
3. `g3 = b OR d`.
4. `g4 = g2 AND g3`.

The output equals `ab OR bc OR cd`. The direct audit checks all 16 inputs.
Gate g4 is critical for all three edges: forcing it to zero changes the output
on each edge input. It owns only `bc, cd`, because its ancestor g1 already
accepts `ab`. Thus a critical edge need not be an owned edge, even at the
four-gate optimum. The independent audit is in `search/p4_optimal.json`.

A separate five-gate example for the path with edges `ab, ad, bc` computes

`((a OR b) AND (a OR c)) AND (b OR d)`.

Its first AND owns all three edges, which have no common center, and its final
AND owns none. All 16 inputs pass. It is not a minimum circuit: the same
function is `a AND (b OR d) OR (b AND c)`, using four gates. This example tests
an exchange argument but does not refute the existential minimum-circuit
statement. Its audit is `search/p4_dirty_nonminimal.json`.

## Unresolved logical step

Minimum size gives positive-edge criticality under forcing a gate to zero.
That fact alone does not give nonempty ownership. On an owned edge, all proper
AND ancestors are zero, so an operand evaluates through its syntactic OR-only
support. This yields a raw product containing the owned edges. For a dirty
AND, the raw product can also contain independent pairs; intersecting it with
the graph need not produce a star. The girth assumptions therefore cannot be
applied as though the whole raw product were a graph biclique.

The checked clean-AND support/counting components and the generic first-dirty
witness lemma remain available, but they do not supply a size-preserving
exchange that eliminates empty owners or dirty nonstar owners. No such
exchange was proved here.

## Reusable pipeline review

The separate target-neutral `finite-circuit-certificates/pipeline.py` source
review is complete. The exact-statement parser and source assembly had no
actionable issue. The 41,480-byte generic body is an exact contiguous block of
the accepted L-meta-1445 source, with SHA256
`19a0ec27e0a5f2a6010436f261f4b74e7db8a4e454af7e6a253e5a691c5fd527`.
That review preceded the later successful synthetic five-input Lean check.
The separate axiom audit and generic extension remain incomplete; see the
package's exact verification records.

## Public status after the stop

At 2026-11-24 00:39:34 UTC, the public catalog (updated 00:37:48 UTC) still
listed L-meta-1031 in `gaps`, with no matching checked, withdrawn, or paused
entry and zero recorded open PRs. An independent exact-ID GitHub PR search
also returned zero results. This establishes that no public settlement was
visible in those sources; it does not identify the cause of HTTP 410.

The compact timestamped status record is in `public-status-after-stop/`.
Full catalog and API snapshots are omitted from this public update.
