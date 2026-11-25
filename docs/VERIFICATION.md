# Reproducing and checking the formalization

## 1. Building the library and checking axioms

Install [`elan`](https://github.com/leanprover/elan) so that `lean-toolchain` selects
`leanprover/lean4:v4.35.0-rc3`. From the repository root, download the precompiled
Mathlib cache, compile the library, and run the axiom checks:

```sh
lake exe cache get
lake build
python3 scripts/audit_axioms.py
python3 scripts/scan_axioms.py
```

- `scripts/audit_axioms.py` runs `#print axioms` on 19 principal theorems in a
  non-module wrapper (`scripts/AxiomAudit.lean`, so that proof bodies across `module`
  boundaries are visible) and checks that only `propext`, `Classical.choice`, and
  `Quot.sound` appear.
- `scripts/scan_axioms.py` calls `Lean.collectAxioms` on every declaration in the
  imported proof library and `Solution.lean` (6,463 declarations) and fails if `sorryAx`
  or any non-standard axiom occurs anywhere.

## 2. Independent Challenge–Solution comparison

To separate statement review from proof checking:

1. [`EFiniteCharacterizations/Statement.lean`](../EFiniteCharacterizations/Statement.lean)
   imports **only Mathlib** and defines the standalone propositions `ArbitraryField`,
   `InfiniteField`, `AlgebraicallyClosedField`, `RankTwo`, and
   `BrickDiscreteMultiplicityFree`.
2. [`scripts/generate_challenge.py`](../scripts/generate_challenge.py) generates
   [`Challenge.lean`](../Challenge.lean) from `Statement.lean` with one `sorry`
   placeholder for each of the five endpoints (`Challenge.arbitraryField`,
   `Challenge.infiniteField`, `Challenge.algebraicallyClosedField`,
   `Challenge.rankTwo`, `Challenge.brickDiscreteMultiplicityFree`).
3. [`Solution.lean`](../Solution.lean) proves those five declarations from the proof
   library without importing `Challenge.lean`.
4. [`scripts/verify-comparator.sh`](../scripts/verify-comparator.sh) invokes the
   toolchain's `lake comparator` (configured by [`comparator.json`](../comparator.json))
   inside `bwrap` (Bubblewrap) to verify definition/type identity and replay those five
   endpoint proofs together with their transitive proof dependencies through the Lean
   kernel and the external checkers **NanoDa** and **con-ron**.

Run the full verification sequence on Linux (with `bwrap` on `PATH` and `.lake/packages`
as a real directory rather than a symbolic link):

```sh
python3 scripts/check-lean-sources.py
python3 scripts/generate_challenge.py --check
lake build Challenge Solution
python3 scripts/audit_axioms.py
python3 scripts/scan_axioms.py
./scripts/verify-comparator.sh
```

Recorded local and hosted verification runs, timings, and artifact hashes are archived
in [`verification/`](../verification/README.md).
