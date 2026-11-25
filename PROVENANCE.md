# Provenance

This repository is maintained by Haruhisa Enomoto. It formalizes in Lean 4 the paper
*Characterizations of E-finite algebras and conjectures on brick-finiteness* by
Haruhisa Enomoto, following the version identified in
[`docs/MANUSCRIPT.md`](docs/MANUSCRIPT.md). Formal coverage of the paper's 44 numbered
statements is documented in [`docs/PAPER-CORRESPONDENCE.md`](docs/PAPER-CORRESPONDENCE.md).

## Authorship and AI contributions

Haruhisa Enomoto formulated the research questions and scope, directed both the
mathematical research and the Lean formalization, and is responsible for the
manuscript and this repository.

- **Manuscript:** As recorded in the paper's *Use of AI* statement (Section 1), the
  mathematical results grew out of several AI-assisted research threads directed by the
  author: GPT-6 Astra developed the generic-grain, universal-localization, and
  open-locus arguments; Claude Fable 5.2 found the rank-two Stern–Brocot proof;
  GPT-6.2 Astra proved the equal-class semibrick extraction and carried out most of the
  independent mathematical audits; Gemini 4 Neon isolated the condition `(K₀-Hom)` from
  torsion-monoid cancellativity, unified the conjecture equivalences across arbitrary
  fields, and wrote the initial draft; GPT-6.2 Astra revised the manuscript with
  exposition reviews coordinated by Claude Opus 5.5; and GPT-6.2 Sol contributed proof
  simplifications.
- **Lean formalization:** The Lean 4 proof library, standalone statements, and
  alternative formal proof routes (summarized in
  [`docs/proofs/PROOF-ROUTES.md`](docs/proofs/PROOF-ROUTES.md)) were developed with
  OpenAI Codex under Haruhisa Enomoto's direction in November 2026, with documentation
  and Lean docstring polishing assisted by Gemini 4 Carbon. Twenty-four foundational
  modules were adapted from earlier Apache-2.0 formalizations as detailed in
  [`VENDORED.md`](VENDORED.md) and [`verification/module-origins.json`](verification/module-origins.json).

No independent line-by-line human review of the Lean source files has been recorded.

## Toolchain and licence

The proof package uses Lean `v4.35.0-rc3` and depends solely on Mathlib at commit
`c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`). All Lean sources and
documentation in this repository are released under the [Apache License 2.0](LICENSE).
