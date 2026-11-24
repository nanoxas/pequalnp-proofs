# Official L-meta-1031 reduction submission

The one-file, one-commit reduction was submitted upstream as
https://github.com/brilliant-hq/pequalnp-proofs/pull/3918
at commit 49043dba9bca45e818e44fdf2d829a8e3fddb92c. The published source is
mirrored under submission/PEqualNP/Outside/R_meta_1031_1.lean and matches its
publication hash. Its final conclusion is the exact posted statement.

The three proposed children isolate: existence of a minimum circuit with
nonempty pairwise-intersecting ownership; compatibility of the finite strict
cone definition with the posted path relation; and the triangle-free
pairwise-intersecting-edge-to-star fact. The first is the remaining substantive
exchange problem. The reduction does not prove all three children.

The outside source/import guard passed. Lean compilation passed in 55.627
seconds. The separate local full reduction verifier was terminated by signal 9
before producing a verdict; the cause is not established. Its generic wrapper
record says FAIL because the process exited -9, not because it returned a
mathematical rejection. The empty verifier log and verification record preserve
that distinction. The authoritative service refused this PR before building it
at 06:04:49 UTC. A subsequent comparison found that a distinct accepted
reduction already occupies the same R_meta_1031_1.lean path. The frozen outcome
is REFUSED_EXISTING_REDUCTION_PATH. The parent L-meta-1031 was still open in
the 06:17:24.662 UTC desk snapshot, and PR #3918 remains open. The original bot
wording is preserved separately in outcome.json; it does not establish that
the parent theorem was proved. See the authoritative comment:
https://github.com/brilliant-hq/pequalnp-proofs/pull/3918#issuecomment-7123560559
and run https://github.com/brilliant-hq/pequalnp-proofs/actions/runs/45337719693.
No official build or acceptance of our reduction is claimed. The earlier desk
acknowledgment recorded submission, not acceptance.

Older stop reports and finite searches in this directory remain historical;
the later fresh assignment allowed this separate reduction submission.
