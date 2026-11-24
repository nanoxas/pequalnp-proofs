# Official reader-profile reduction for L-meta-670

The exact posted no-15-gate statement is the conclusion of
R_meta_670_718.lean. This reduction was submitted upstream as [PR #4110](https://github.com/brilliant-hq/pequalnp-proofs/pull/4110)
at commit 66fde525c8d62b2a7f9622173dcd149925d3853c. The source SHA256 is
dab49ddb2f73397130333e5dd0e2184f75ae3c78f7103226e80898c73168228f. The API verified one file and one commit. The frozen official
verdict is PENDING; no official acceptance or full replay is claimed here.
Local reservation renewals were stopped and the recorded reservation awaits
natural expiry. No successful desk release acknowledgment is claimed. The
preflight.json record retains its earlier pre-submission check status;
published.json and outcome.json record the later official submission.

The four closed children are:

1. Normalize a putative size-at-most-15 witness to a clean minimum circuit in
   which each of inputs 4, 6, and 7 has one or two actual reader gates, and two
   readers must both be OR gates.
2. Exclude a representative with a non-OR reader of one of those inputs.
3. Exclude representatives whose special readers are all OR and one of those
   inputs has two readers.
4. Exclude representatives in which each of those inputs has one OR reader.

The checked theorem proves that these four children imply the exact parent
statement. It does not prove any of the four children. The clean-arity and
minimum-circuit hypotheses are explicit in the children; no restricted SAT
result is used as an unproved premise in the reduction proof.

Local Lean compilation passed in 1.870 seconds, with standard axioms only.
The lightweight canonical printer/readback preflight passed in 5.034 seconds;
the four child lengths are 1792, 1887, 1983, and 1915 characters. Each parsed
back to an expression identical to its original child. The preflight records
its public checker-function provenance and its limited loaded environment.
This local preflight is separate from the authoritative checker verdict.
An independent read-only mathematical/source review also passed.
