# P vs NP research checkpoint

This branch preserves completed research from the ongoing collaboration. The detailed report is in [README.txt](research-checkpoints/README.txt); the [manifest](research-checkpoints/manifest.json) records exact source hashes and verification scope.

## Completed five-input search: L-meta-1418

All ten assigned truth tables have a verified monotone circuit of size M and a definitive UNSAT result for the complete 32-row model with at most one NOT gate and at most M-1 gates. In posted order, the minima are **8, 7, 5, 8, 6, 4, 6, 4, 8, 9**.

The independent audit checked all 320 witness rows, legal references, gate types, and final bounds. The model includes free constants and handles the project's empty, unary, duplicate-input, invalid-reference, and unused-gate conventions. The symmetry restriction has an explicit completeness argument.

- [Search implementation](main-1418/search.py)
- [Final results and witnesses](main-1418/results-ordered.json)
- [Completeness argument](main-1418/completeness-notes.txt)
- [Exhaustion manifest](main-1418/exhaustion-manifest.json)
- [Independent audit](main-1418/root-audit.json)
- [Desk response](main-1418/desk-report.json)

This is computational exhaustion with an audited encoding, not a Lean theorem or a DRAT/LRAT certificate. The desk accepted `statement_seems_false`; it rejected `exhausted` because the lease had no server-defined shard range. The negative posted existence claim therefore has computational evidence against it, rather than a proof of that claim.

## Checked reusable proof components

The archive contains Lean-checked exact ladder support, the first-dirty-AND small-witness lemma in actual circuit semantics, the dyadic inverter semantic core, and six checked actual-circuit clean-count components in `main-1407/`.

The full L-meta-1407 assembly was not completed. Another contributor's proof had already been [accepted upstream](https://github.com/brilliant-hq/pequalnp-proofs/pull/2889) before this assembly started. The duplicate [fork draft](https://github.com/nanoxas/pequalnp-proofs/pull/1) was closed without merging. It triggered no Actions run and was not an official swarm submission. The unverified assembled draft is omitted from this checkpoint.

## Review priorities

The strongest next validation improvement is a trusted certificate for the finite circuit UNSAT results. The existing search model and symmetry argument are fully exposed for review. Other recorded results include the explicit few-NOT incidence compiler, the degree-four counting obstruction, and corrected semantics for the L-meta-1006 boundary witness. Their exact assumptions, checked instances, and unproved bridges are documented in the detailed report.

This branch contains supporting research. The project's official checker accepts exact posted Lean theorem submissions through upstream proof pull requests. No accepted upstream theorem is attributed to this session.
