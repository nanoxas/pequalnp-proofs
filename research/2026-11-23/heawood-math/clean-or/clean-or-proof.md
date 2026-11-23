# Clean AND circuits: a paper proof of the OR charge

Status: local, unsubmitted research. The argument below has been independently
reviewed within this session. `TypedPortCount.lean` verifies the two finite
counting cores and the numerical assembly. The extraction of those finite
networks from the project's root circuit model remains to be formalized.

## Statement and hypotheses

Let G be a finite simple graph with at least one edge and no cycle of length
four. Write m for its number of edges and tau for its vertex-cover number.
Let C be a finite monotone circuit with binary AND and OR gates that computes
the edge function f_G. Assume every AND gate is **clean**: its output is false
on every independent input of G. Equivalently, each AND gate's function is
pointwise at most f_G. It suffices to check maximal independent inputs, because
every wire function is monotone.

The paper argument proves separately

    number of AND gates >= tau,
    number of OR gates >= m - 1.

Thus the total gate count is at least m + tau - 1. Applied to Heawood, m=21 and
tau=7, this gives at least 27 gates in the globally clean class.

This theorem concerns the globally clean class. It does not assert that an
arbitrary monotone circuit can be made globally clean without increasing size.

## 1. Raw supports and the sound bypass

For each wire w, define S(w) to be its raw support: the inputs that reach it by
a path containing only OR gates. Thus an input v has support {v}; an OR takes
the union of its two supports; every AND has empty raw support.

On an independent input I, all AND outputs are zero by cleanliness. Induction
over gates therefore gives

    w(I)=1 iff S(w) intersects I.

In particular, S(w) is exactly the set of singleton inputs accepted by w. A
wire with empty raw support is itself clean.

If an AND has an operand w with empty raw support, bypass the AND by w. The
replacement increases this gate's value pointwise. On every independent input
both the old AND and w equal zero, so all downstream values on these inputs
remain unchanged. The final output still accepts every positive input, and
still rejects every independent input. It therefore still computes f_G. All
remaining AND gates stay clean.

Repeat this bypass, remove dead gates, and remove constants and unary gates.
These operations do not increase either gate count. All remaining AND gates
have two nonempty raw supports. The output has empty raw support, since f_G
rejects every singleton input.

The original root model permits missing wire indices and fan-in at most two.
Missing indices are false constants. False branches, unary OR gates, and unary
AND gates can be eliminated before the count. A nullary AND is true on the
empty independent input and is therefore excluded by cleanliness.

## 2. Every normalized AND supplies a raw star

Let an AND's operand supports be S and T. They are nonempty. Cleanliness implies

* S and T are disjoint: otherwise a common singleton fires the AND.
* Every cross-pair s in S, t in T is an edge: otherwise the independent input
  {s,t} fires the AND.

If both supports had two distinct vertices, their complete cross-pairs would
give a four-cycle. Thus one support is a singleton {v}, and the other is a
nonempty set T contained in N(v). Choose v as this gate's center. When both
supports are singletons, choose either endpoint. Its raw star consists of the
edges {v,t}, t in T.

These raw stars cover every graph edge. For an edge e, the output accepts the
input supported exactly on e. Some AND must accept this input: if every AND
were false there, the output would equal the OR of its empty raw support and
would be false. Choose the first globally accepting AND in gate order. Every
earlier AND is false on this pair input, so each operand is true because of a
raw input. The two disjoint supports select the two different endpoints of e.
Hence e belongs to this AND's raw star.

Only this first-global-acceptance fact is used. It is distinct from the existing
`EdgeOwnership.Owns`, which excludes true ANDs in the strict cone rather than
all earlier AND gates.

The chosen centers consequently form a vertex cover. If A is the number of
normalized AND gates, then A >= tau.

## 3. Charge the raw unions, grouped by center

For each vertex v, let p_v be the number of AND gates assigned center v. Let
U_v be the union of their noncenter operand supports. There are p_v designated
raw-support outputs, and U_v is contained in N(v).

Take the union of the OR-only ancestries of these designated outputs. This is
only a network for computing raw supports; it is not a modification of the
Boolean circuit. Discard empty-support branches. Contract ORs with only one
nonempty-support child. Contract any wire whose support is a singleton to the
corresponding input label. Identify repeated occurrences of that input label.
Retain only nodes reaching a designated output.

The resulting finite union DAG has:

* |U_v| input nodes;
* at most p_v distinct output nodes;
* binary merge nodes corresponding to original OR gates with two nonempty
  operand supports and with output support of size at least two.

If it has M_v merge nodes and R_v output nodes, every input or merge node is
an output or is consumed by a merge. Counting consumed ports gives

    |U_v| + M_v <= R_v + 2 M_v,
    hence |U_v| <= M_v + p_v.

This is the formal lemma `CleanPortCount.binary_union_ports`. The count permits
fanout and shared intermediate unions.

A merge cannot be charged to two different centers v and w. Its full raw
support is contained in both N(v) and N(w), and has at least two vertices. This
would give two common neighbors of v and w, hence a four-cycle.

Let W be the total number of original OR gates with two nonempty-support
operands. The charged merge sets are pairwise disjoint subsets of these gates.
Every edge occurs in at least one raw star, and each distinct neighbor in U_v
represents one edge incident to v. Therefore

    m <= sum_v |U_v| <= sum_v M_v + sum_v p_v <= W + A.

Grouping by center avoids any need to separate repeated stars with the same
center or to assign an edge uniquely to a particular AND gate.

## 4. Charge aggregation by empty-support ports

Call a wire C-type if its support is empty, and D-type otherwise. After the
bypass normalization every AND is D,D -> C. Partition OR gates into:

* W: D,D -> D;
* c: C,C -> C;
* r: C,D -> D, in either operand order.

There are exactly A+c C-type gate outputs. Every one except the circuit output
has an outgoing use, because the circuit was trimmed. ANDs consume no C-type
wire. The two OR classes c and r have at most 2c+r input ports for C-type
wires. Counting distinct consumed wires through these ports gives

    A+c-1 <= 2c+r,
    hence A <= c+r+1.

Fanout can only increase the number of consumed ports. The final gate may be
AND or OR. This is the formal lemma
`CleanPortCount.typed_aggregation_ports`.

The aggregation ORs c+r are disjoint from the raw-union ORs W. Combining the
two counts gives

    m <= W+A <= W+c+r+1 = number of OR gates + 1.

Together with A >= tau, this proves the claimed separate bounds.

## 5. Small checks and limits of normalization

The exact semantic search in `small_or_search.py` treats AND gates as free and
uses the representation (S,E), where E is the set of graph-edge pair inputs
accepted by a wire. For globally clean circuits:

* OR takes unions of S and E.
* An AND is clean exactly when the two supports are disjoint and every
  cross-pair is an edge.
* A clean AND has support empty and edge signature equal to the intersection
  of its operand signatures.

The search found no clean circuit with fewer than m-1 ORs for every four-vertex
C4-free graph, for the five-cycle, and for the six-cycle. The cycle searches
examined 5,986 and 292,586 semantic states respectively. These computations
are diagnostics, not Lean certificates or a substitute for the proof.

Two explicit truth-table checks guard the normalization scope:

1. For the four-vertex path with edges ab,bc,cd, the four-gate circuit
   `(a OR c) AND (b OR (c AND d))` is correct and every AND is clean. Its final
   gate is AND; both AND gates survive the sound bypass. It has one raw-merge
   OR and one mixed OR, exactly matching the two charges. Thus an assumed
   OR-only final aggregation would be an invalid normalization requirement.

2. Empty singleton support alone is insufficient without global cleanliness.
   On the same path, h=a AND d is dirty but has empty singleton support, while
   g=h AND b is clean. The circuit `f_G OR g` computes f_G. Bypassing g by h
   makes the independent input {a,d} positive. The sound bypass above uses
   the global cleanliness hypothesis to infer that every empty-support
   operand is clean.

## 6. What is formally checked

`TypedPortCount.lean` checks:

* the binary union-network port inequality;
* the typed aggregation-port inequality;
* numerical assembly of the two charges and the cover bound;
* the Heawood conclusion 20 OR gates and 27 total gates from those hypotheses.

It imports only `Mathlib.Algebra.Order.BigOperators.Group.Finset` and compiles
with Lean 4.36.0. Its hypotheses explicitly describe the extracted finite
networks. The root-model normalization, raw-support semantics, star cover,
and private-network extraction still require Lean formalization before this
becomes a project-ready theorem about circuits.
