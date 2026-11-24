NONEMPTY HEAVY RESOURCE POOLS STILL MISS DELETED CONTEXT CREDIT

Status: exact symbolic gate audit and generator identity check; independently
reviewed in independent-review.json. No Lean proof, SAT search or complete
truth table of the large circuit is claimed. The actual997 inequality holds.

1. THE AUXILIARY CLAIM BEING TESTED

Let G_i be each target's original C1 private class. Enlarge the heavy pool
H_i^+ to EVERY original gate that is C0-sound for the heavy target and has
nonempty shifted support, including AND and singleton-support context gates.
The proposed quota matching allows light targets to use G_i and heavy
targets to use G_i union H_i^+, with one additional credit for each exact
refund. The example below refutes this exclusive resource budget, even if
every resource and refund credit is made globally fungible.

2. AFFINE GEOMETRY AND THE ORIGINAL CIRCUIT

Choose an odd prime q and k distinct slopes in F_q^2. The kq affine lines
of those slopes are the heavy targets, each of size q. Two heavy targets
intersect in at most one point. Give every affine point a second, separate
input p' and reserve k additional inputs Y={y_0,...,y_{k-1}}.

Within each line, pair its first q-1 points. For every pair {a,b} on a line
of slope s, add the light target {y_s,a',b'}. Lines of one slope partition
the points, so their light pairs are disjoint; different slopes share at
most one point. Thus all light targets form a linear family. Light and
heavy targets occupy disjoint point layers and have empty intersections.

Set h=AND(Y), z=NOT h. Share these three gates for each affine point p:

  u_p=p' AND z, v_p=p AND h, w_p=u_p OR v_p.

For a line T, its OR tree M_T starts by computing its paired cherries
w_a OR w_b, then joins the cherries and the unpaired final point. Each
light output is y_s OR its cherry. Also compute

  Q_T=AND_{y in Y}(y OR OR(T))=h OR OR(T),
  heavy_output_T=(Q_T AND z) OR(M_T AND h).

The displayed OR(T) in Q_T is distributed separately into every y clause;
the generator does not precompute a private OR(T) wire.

When h=false, every M_T is OR of the corresponding primed points and Q_T
is OR(T). When h=true, all y_s are true, M_T=OR(T), and Q_T=true. Therefore
every original light and heavy output is its exact required disjunction.
The NOT is true below weight k and false at Y. All ports read earlier wires,
all fan-ins are at most two, and every gate is structurally live.

3. EXACT RESOURCE COUNTS

Write H=kq for the number of heavy lines and P=q^2 for the number of affine
points. There are H(q-1)/2 light targets. Each light G_i consists of its
cherry and its output, so it has two gates and quota2. Each heavy G_i has
k+1 gates: the k-1 ANDs forming Q_T, the Q_T AND z gate, and the output.
Its quota is q-1, so it is deficient whenever q>k+2.

The union H^+ contains:

  - P shared v_p gates and P shared w_p gates;
  - q-1 OR-tree gates per heavy line;
  - M_T AND h and the final output per heavy line.

All Q_T clauses and ANDs are true at Y and therefore are not C0-sound for
a heavy target. All u_p and Q_T AND z gates have empty shifted support.
There are no other H^+ gates. The exact formulas are

  |G_all| = H(q+k),
  |H_all^+| = 2P+H(q+1),
  |G_all intersect H_all^+| = H((q-1)/2+1),
  |G_all union H_all^+| = 2P+H(3(q-1)/2+k+2).

The total quota is 2H(q-1). The exact refund count is H: precisely the final
heavy outputs. Every other full heavy singleton support either has empty
shifted support or is true on all shifted outside points.

For k=9 and q=47:

  inputs                         4,427
  gates                        219,405
  light targets                  9,729
  heavy targets                    423
  total quota                   38,916
  eligible resource union       38,258
  exact refunds                    423
  unpaid after refunds             235
  gates outside that union     181,147

The real997 inequality is49,068<=219,405+423+10,152=229,980. It has ample
slack. The missing auxiliary resource credit lies among the many discarded
contexts, including Q_T clause OR gates. For this construction those clause
ORs have stable singleton support inside T, so stable-support accounting
does see resources omitted by H^+.

4. WHAT THE AUDIT ACTUALLY CHECKS

Run `python3 main-997/nonempty-pool-obstruction/audit.py` from the workspace.
The script reconstructs the complete gate list deterministically in memory
for both (q,k)=(11,5) and (47,9), and records its hash. It verifies linearity
by checking every target point-pair, all port bounds, the unique NOT, and
liveness of all gate identities.

It propagates every original singleton signature exactly. On the entire
subcube Y=1, every gate function in this construction is a constant or a
disjunction. The script propagates that full symbolic function; an AND is
accepted only when its operands are nested disjunctions or constants, which
makes the simplification exact. This proves the shifted signatures and
every complement-input soundness test, not merely selected-row estimates.

Original-output correctness on arbitrary inputs is supplied by the explicit
generator identities in Section2, with all2,048 assignments of the k=9
control bits and aggregate OR values checked. It is not a full truth-table
check on4,427 variables. Results record this distinction and set both
lean_checked and solver_used to false.

The independent review checked the geometry, identities, exact resource
classification and counts without repeating the large audit. The scripts
and records are frozen. No further large audit is needed for this example.
