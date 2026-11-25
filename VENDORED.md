# Adapted Lean modules

Mathlib is the only external Lake dependency of this repository. Twenty-four of the
388 modules under `EFiniteCharacterizations/` were adapted from earlier Apache-2.0
Lean 4 formalizations, ported to the pinned Mathlib revision
(`c55e6e786f49471c72fbddbec5415808896aec1e`), and integrated into the subject
hierarchy and `EFiniteCharacterizations` namespace.

[`verification/module-origins.json`](verification/module-origins.json) records the
exact origin of each adapted file; all remaining 364 library modules were written for
this formalization.

| Source project | Modules | Material adapted | Licence |
| --- | ---: | --- | --- |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti), development commit `02160f039476c36211f34cf7cb338272193a0ab6` (not a published release) | 13 | Linear duals, balanced tensor products, injective modules over division rings and algebras, opposite modules, and the Nakayama functor | Apache-2.0 (The Tau Ceti contributors) |
| [`third-brauer-thrall-conjecture`](https://github.com/haruhisa-enomoto/third-brauer-thrall-conjecture) | 6 | Contragredient `k`-duality on `FGModuleCat`, full-idempotent Morita equivalence, and split basic corner reduction | Apache-2.0 |
| [`pretorsion-image-closed`](https://github.com/haruhisa-enomoto/pretorsion-image-closed), commit `e6e95f6c295649bccf0ca476c9a5b008320e9443` | 2 | Morphisms of finitely generated modules and composition series / length | Apache-2.0 |
| [`magnitude-conjecture`](https://github.com/haruhisa-enomoto/magnitude-conjecture) | 1 | Restricting Morita equivalences to finitely generated module categories (`Geometry/BasicPresentation.lean`) | Apache-2.0 |
| [`quotient-submodule-equidistribution`](https://github.com/haruhisa-enomoto/quotient-submodule-equidistribution) | 1 | Simplicity criterion in `FGModuleCat` (`Geometry/SplitBasicSimples.lean`) | Apache-2.0 |
| [`extension-closed-string-algebras`](https://github.com/haruhisa-enomoto/extension-closed-string-algebras) | 1 | Fourier–Motzkin proof of Farkas's lemma over an ordered field (`LinearAlgebra/Farkas.lean`) | Apache-2.0 |

Files ported from Tau Ceti retain their upstream copyright headers together with an
explicit adaptation notice naming the source module and commit SHA.
