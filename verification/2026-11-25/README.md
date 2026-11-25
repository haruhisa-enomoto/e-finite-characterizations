# Verification report — November 25, 2026

Toolchain: Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`.

## Local checks

| Check | Outcome |
| --- | --- |
| Proof library and `Solution` build (`lake build`) | Passed (3,873 build jobs) |
| Standalone `Challenge` and `Solution` build | Passed (five compared endpoints) |
| Targeted `#print axioms` audit (`scripts/audit_axioms.py`) | All 19 principal declarations passed |
| Full library & `Solution` axiom scan (`scripts/scan_axioms.py`) | 6,463 declarations checked; only `propext`, `Classical.choice`, and `Quot.sound` |
| Local `lake comparator` (`scripts/verify-comparator.sh`) | Passed Lean 4 kernel, NanoDa, and con-ron on all five endpoints |

Reproduction commands are documented in [`../../docs/VERIFICATION.md`](../../docs/VERIFICATION.md), and full statement coverage of all 44 numbered manuscript results is indexed in [`../../docs/PAPER-CORRESPONDENCE.md`](../../docs/PAPER-CORRESPONDENCE.md).

## Hosted Palomar mechanical preflight (`v0.1.0` / `f594ef1`)

The hosted [Palomar mechanical preflight](https://github.com/haruhisa-enomoto/e-finite-characterizations/actions/runs/45530650450) ran on proof release commit [`f594ef1`](https://github.com/haruhisa-enomoto/e-finite-characterizations/tree/f594ef1cc3337cf35db6bbc3a32b515d400b4a3e) (tagged [`v0.1.0`](https://github.com/haruhisa-enomoto/e-finite-characterizations/releases/tag/v0.1.0)) on November 25, 2026 (02:07:23–02:23:44 UTC) using pipeline commit `14aa8d6b3c2f14a8540605e37144560b9a00e7e7` and runner profile `palomar-standard-v1`.

| Hosted phase | Result |
| --- | --- |
| Lean source inspection | 392 files, zero errors |
| `Solution` build | 317 s, 2.13 GiB peak RSS |
| Comparator phase (Lean kernel & NanoDa) | 238 s, 2.20 GiB peak RSS |
| `con-ron` external kernel phase | 100 s, 1.84 GiB peak RSS |
| Challenge provenance | High trust (577 lines at `f594ef1`; within the 1,000-line limit, with the standard non-blocking >300-line review-surface note) |

The archived [`mechanical-report.json`](mechanical-report.json), [`comparator-tail.log`](comparator-tail.log), and [`SHA256SUMS`](SHA256SUMS) record the artifacts of that hosted `f594ef1` run; subsequent documentation and docstring revisions preserve all theorem types and proof terms identically.
