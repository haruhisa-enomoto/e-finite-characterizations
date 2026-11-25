# Checking the Lean proofs

Use the Lean toolchain selected by `lean-toolchain`. At the repository root, fetch the pinned Mathlib build cache and build the proof library.

```sh
lake exe cache get
lake build
python3 scripts/scan_axioms.py
```

The scan imports the library in a non-module Lean file so that Lean can inspect the bodies of theorems across module boundaries. It calls `Lean.collectAxioms` on every declaration in the project’s proof modules and fails if any axiom besides `propext`, `Classical.choice` and `Quot.sound` occurs. The [concordance](PAPER-CORRESPONDENCE.md) identifies the exact result checked for each numbered statement in the manuscript.

## Independent comparison

The Mathlib-only [statement](../EFiniteCharacterizations/Statement.lean) defines the hypotheses and conclusions independently of the proof library. The [generator](../scripts/generate_challenge.py) copies those definitions into [Challenge.lean](../Challenge.lean), with one placeholder per requested proof. The [solution](../Solution.lean) supplies all five proofs. The comparator checks their types and transitive declaration dependencies against the challenge and verifies the proofs with its external kernels.

```sh
python3 scripts/check-lean-sources.py
python3 scripts/generate_challenge.py --check
lake build Challenge Solution
python3 scripts/audit_axioms.py
python3 scripts/scan_axioms.py
./scripts/verify-comparator.sh
```

The comparator runs in Bubblewrap on Linux. Install `bwrap` on the executable path and use a real directory for `.lake/packages`. See the [verification record](../verification/README.md) for results and artifact hashes.
