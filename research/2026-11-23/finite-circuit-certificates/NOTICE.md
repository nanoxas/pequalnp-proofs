# Attribution and provenance

The generic Lean proof body is reused from the accepted PEqualNP contribution
**L-meta-1445**. Its source credits the live-wire semantics and search to
**L-meta-1007**, under **Apache-2.0**. The copied body is preserved exactly;
only the surrounding generated namespace and import header vary.

The accepted source SHA256 is:

```text
569aaa0aa1b5027191460a8f81feba9f78f40a583083328dfd4032fb86e257c6
```

The extracted generic-body SHA256 is:

```text
19a0ec27e0a5f2a6010436f261f4b74e7db8a4e454af7e6a253e5a691c5fd527
```

`engine/provenance.json` records the extraction boundary, source hashes, and
the status of the minimized import header. Every emitted Lean file retains
the attribution comments.

The Python evaluator follows the accepted engine's executable definitions.
Its independent reference variant recomputes coverage from the candidate
frontier and omits the optimized coverage-count and tight-frontier paths.
The witness generator and source assembler are project-session contributions
intended for reuse alongside the accepted proof infrastructure.

The project's Apache License 2.0 text is included as `LICENSE`.
