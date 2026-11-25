# Checking the Lean proofs

Use the Lean toolchain selected by `lean-toolchain`. At the repository root, fetch the pinned Mathlib build cache and build the proof library.

```sh
lake exe cache get
lake build
python3 scripts/scan_axioms.py
```

The scan imports the library in a non-module Lean file so that Lean can inspect the bodies of theorems across module boundaries. It calls `Lean.collectAxioms` on every declaration in the project’s proof modules and fails if any axiom besides `propext`, `Classical.choice` and `Quot.sound` occurs. The [concordance](PAPER-CORRESPONDENCE.md) identifies the exact result checked for each numbered statement in the manuscript.
