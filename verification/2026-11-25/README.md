# November 25 verification

Lean 4.35.0-rc3, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`.

| Check | Local result |
| --- | --- |
| Default proof library and Solution | Build passed, 3,873 jobs |
| Independent Challenge and Solution | Build passed, five compared declarations |
| Generated statement | 577 lines, 26,239 bytes |
| Selected axiom queries | All 19 passed |
| Axioms in the imported proof library and Solution | 6,463 declarations. Only `propext`, `Classical.choice` and `Quot.sound` |

The [verification guide](../../docs/VERIFICATION.md) gives the commands. The five compared declarations cover Theorem A(I–III), Theorem B and Corollary C. The [concordance](../../docs/PAPER-CORRESPONDENCE.md) locates each of the 44 numbered results.

## Palomar preflight

The hosted [mechanical preflight](https://github.com/haruhisa-enomoto/e-finite-characterizations/actions/runs/45530650450) passed on [release commit f594ef1](https://github.com/haruhisa-enomoto/e-finite-characterizations/tree/f594ef1cc3337cf35db6bbc3a32b515d400b4a3e). The verification job ran from 02:07:23 to 02:23:44 UTC on November 25. The pipeline was `14aa8d6b3c2f14a8540605e37144560b9a00e7e7` with the `palomar-standard-v1` runner profile.

| Hosted check | Result |
| --- | --- |
| Lean source inspection | 392 files, zero errors |
| Solution build | 317 s, 2.13 GiB peak RSS |
| Comparator phase | 238 s, 2.20 GiB peak RSS |
| con-ron verification phase | 100 s, 1.84 GiB peak RSS |
| Challenge provenance | High trust. The 577-line statement exceeds the preferred 300-line review size and is within the 1,000-line limit. |

The local comparator also accepted all five declarations with the Lean kernel, NanoDa and con-ron. The [mechanical report](mechanical-report.json) records the complete hosted result. The [comparator output](comparator-tail.log) and [file hashes](SHA256SUMS) identify its inputs and outcome.
