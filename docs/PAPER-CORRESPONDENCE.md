# Paper correspondence

This document maps the results of Haruhisa Enomoto's
*Characterizations of E-finite algebras and conjectures on brick-finiteness*
([November 25, 2026 manuscript](MANUSCRIPT.md)) to their Lean 4 declarations in the
`EFiniteCharacterizations` namespace.

- **Module convention:** Following the paper, endpoints are stated for finite-dimensional
  right `Λ`-modules, realized in Lean as left modules over `Λᵐᵒᵖ` (`FGModuleCat Rᵐᵒᵖ`
  and `ModuleCat Rᵐᵒᵖ`). Many internal modules prove results for left `R`-modules and
  specialize to `R := Λᵐᵒᵖ` at the assembly layer.
- **Status labels:** `covered` (proved following the paper's statement);
  `covered (different route)` (same mathematical statement proved by an alternative
  route; see [proofs/PROOF-ROUTES.md](proofs/PROOF-ROUTES.md)); `expository`
  (conjecture, remark, or worked example not required by any proof).

---

## Quick lookup: `(E-fin)` and its 22 characterizations in Theorem A

All 17 arbitrary-field equivalences are bundled in
[`equivalences_arbitraryField`](../EFiniteCharacterizations/Characterizations/Equivalences.lean)
(and compared in `Challenge.arbitraryField`), the two infinite-field equivalences in
[`equivalences_infiniteField`](../EFiniteCharacterizations/Characterizations/Equivalences.lean)
(`Challenge.infiniteField`), and the three algebraically closed equivalences in
[`equivalences_algebraicallyClosedField`](../EFiniteCharacterizations/Characterizations/Equivalences.lean)
(`Challenge.algebraicallyClosedField`).

| Label | Field | Mathematical condition | Body result | Individual Lean theorem / predicate |
| --- | --- | --- | --- | --- |
| `(E-fin)` | any | `K₀(proj Λ) ⊆ Σ(Λ)` | Def., §1.1 | [`IsEFinite`](../EFiniteCharacterizations/Presentations/ProjectiveClasses.lean) (`Statement.EFinite`) |
| `(K₀-Hom)` | any | `[M] = [N] ≠ 0 ⇒ Hom_Λ(M, N) ≠ 0` | Thm. 3.2 | [`isEFinite_iff_equalClassHom`](../EFiniteCharacterizations/Characterizations/HomCharacterizations.lean) |
| `(mon-dim)` | any | `M(T) → K₀(mod Λ)` injective for every torsion class `T` | Thm. 4.1 | [`isEFinite_iff_injective_torsionMonoid`](../EFiniteCharacterizations/GrothendieckGroups/TorsionMonoidEmbedding.lean) |
| `(comp-tors)` | any | Every compact torsion class `⊥(M⊥)` is functorially finite | Thm. 3.2 | [`isEFinite_iff_generatedTorsionClass_functoriallyFinite`](../EFiniteCharacterizations/Subcategories/CompactTorsionEquivalences.lean) |
| `(num-disj)` | any | Every torsion pair `(T, F)` is numerically disjoint | Thm. 3.2 | [`isEFinite_iff_numericallyDisjointTorsionPairs`](../EFiniteCharacterizations/Characterizations/HomCharacterizations.lean) |
| `(wide)` | any | Every wide subcategory `W ⊆ mod Λ` is functorially finite | Thm. 5.1 | [`isEFinite_iff_functoriallyFinite_wideClasses`](../EFiniteCharacterizations/Subcategories/WideSubcategories.lean) |
| `(wide₁)` | any | `Filt(B)` is functorially finite for every brick `B` | Thm. 5.1 | [`isEFinite_iff_functoriallyFinite_filteredBy`](../EFiniteCharacterizations/Subcategories/BrickFiltrationEquivalences.lean) |
| `(brick-label)` | any | Every brick `B` labels a cover `T' ⋖ T` in `f-tors Λ` via `Filt(B) = T ∩ (T')⊥` | Thm. 5.1 | [`isEFinite_iff_brickLabels`](../EFiniteCharacterizations/Subcategories/BrickLabels.lean) |
| `(n-sbrick)` | any | `{S₁, …, S_n}` is the unique `n`-element semibrick | Thm. 3.2 | [`isEFinite_iff_unique_fullSize_semibrick`](../EFiniteCharacterizations/Characterizations/HomCharacterizations.lean) |
| `(fin-sbrick)` | any | Every semibrick in `mod Λ` is finite | Thm. 3.2 | [`isEFinite_iff_finite_semibricks`](../EFiniteCharacterizations/Characterizations/HomCharacterizations.lean) |
| `(brick-discrete)` | any | Only finitely many bricks of each endolength `r ≥ 1` | Thm. 5.2, Prop. 5.3 | [`isEFinite_iff_endo_brick`](../EFiniteCharacterizations/Stability/EndInvariantSubmodules.lean) |
| `(endo-stab)` | any | Only finitely many `θ`-stable bricks of each endolength `r ≥ 1` | Thm. 5.2, Prop. 5.3 | [`isEFinite_iff_endo_stab`](../EFiniteCharacterizations/ScalarExtension/GroundFieldWitnesses.lean) |
| `(poly-brick)` | any | Bricks of length `≤ m` grow at most polynomially in `m` | Thm. 5.2 | [`isEFinite_iff_poly_brick`](../EFiniteCharacterizations/Stability/PolynomialBrickGrowth.lean) |
| `(no-gen-brick)` | any | No generic brick in `Mod Λ` | Thm. 7.8 | [`isEFinite_iff_no_generic_right_brick`](../EFiniteCharacterizations/RingEpimorphisms/GenericEpicTarget.lean) |
| `(no-gen-grain)` | any | No generic grain in `Mod Λ` | Thm. 7.8 | [`isEFinite_iff_no_genericGrain`](../EFiniteCharacterizations/LargeModules/GenericGrainCriterion.lean) |
| `(thick-gen)` | any | Every thick subcategory of `K^{[-1,0]}(proj Λ)` has a presilting generator | Prop. 7.5, Thm. 7.8 | [`isEFinite_iff_boundedProjectiveThickGeneration`](../EFiniteCharacterizations/Silting/ThickSubcategories/BoundedProjectiveHomotopy.lean) |
| `(univ-loc)` | any | Every universal localization of `Λ` is finite-dimensional | Thm. 7.8 | [`isEFinite_iff_rightUniversalLocalizationsFinite`](../EFiniteCharacterizations/RingEpimorphisms/GroundLocalization.lean) |
| `(ring-epi)` | any | Every ring epimorphism `Λ → Γ` to a simple Artinian ring has `dim_k Γ < ∞` | Thm. 7.8 | [`equivalences_arbitraryField`](../EFiniteCharacterizations/Characterizations/Equivalences.lean), [`no_generic_right_brick_iff_finite_ring_epimorphisms`](../EFiniteCharacterizations/LargeModules/GenericBrick.lean) |
| `(dim-brick)` | infinite | Only finitely many bricks of each dimension vector `d ∈ ℕ^n` | Cor. 5.4 | [`isEFinite_iff_dim_brick`](../EFiniteCharacterizations/Characterizations/FixedClassFiniteness.lean) |
| `(dim-stab)` | infinite | Only finitely many `θ`-stable bricks of each dimension vector `d ∈ ℕ^n` | Cor. 5.4 | [`isEFinite_iff_dim_stab`](../EFiniteCharacterizations/Characterizations/FixedClassFiniteness.lean) |
| `(moduli-pt)` | `k = k̄` | Every King moduli space `M_θ^{ss}(Λ, d)` has at most one closed point | Thm. 6.1 | [`isEFinite_iff_kingClosedPoints`](../EFiniteCharacterizations/Geometry/GeometricCriteria.lean) |
| `(open-brick)` | `k = k̄` | Every brick has a Zariski-open `GL(d)`-orbit in `rep(Λ, d)` | Thm. 6.1 | [`equivalences_openLoci`](../EFiniteCharacterizations/Geometry/BasicPresentation.lean) |
| `(open-wide)` | `k = k̄` | Every wide subcategory defines a Zariski-open locus in `rep(Λ, d)` | Thm. 6.1 | [`equivalences_openLoci`](../EFiniteCharacterizations/Geometry/BasicPresentation.lean) |

The per-algebra equivalence among the seven brick-finiteness conjectures `(i)`–`(vii)`
stated after Theorem A is proved in
[`seven_pointwise_implications`](../EFiniteCharacterizations/Characterizations/BrickFiniteness.lean),
and the equivalence of brick-continuity with the existence of a generic brick in
[`brickContinuous_iff_exists_generic_right_brick`](../EFiniteCharacterizations/Characterizations/BrickFiniteness.lean).

---

## Complete statement-by-statement correspondence

Line numbers refer to `main.tex` of the [November 25 manuscript](MANUSCRIPT.md). All 44
numbered theorems, propositions, lemmas, and corollaries are proved; numbered
conjectures, remarks, and worked examples are included for completeness.

| No. | Kind | TeX label | Line | Status and notes | Lean declarations |
| --- | --- | --- | ---: | --- | --- |
| 1.1 | conjecture | `conj:demonet` | 142 | expository (open in rank `≥ 3`; settled for `n ≤ 2` by Theorem B and linked to `(ii)`–`(vii)` in `seven_pointwise_implications`) | [`seven_pointwise_implications`](../EFiniteCharacterizations/Characterizations/BrickFiniteness.lean) |
| Thm A | theorem | `intro:main` | 162 | covered (compared in `Challenge.arbitraryField`, `infiniteField`, `algebraicallyClosedField`) | [`equivalences_arbitraryField`](../EFiniteCharacterizations/Characterizations/Equivalences.lean), [`equivalences_infiniteField`](../EFiniteCharacterizations/Characterizations/Equivalences.lean), [`equivalences_algebraicallyClosedField`](../EFiniteCharacterizations/Characterizations/Equivalences.lean), [`proveArbitraryField`](../EFiniteCharacterizations/MainTheorems.lean), [`proveInfiniteField`](../EFiniteCharacterizations/MainTheorems.lean), [`proveAlgebraicallyClosedField`](../EFiniteCharacterizations/MainTheorems.lean) |
| Thm B | theorem | `intro:rank-two` | 227 | covered (`= Theorem 8.4`; compared in `Challenge.rankTwo`) | [`rankTwoEquivalences`](../EFiniteCharacterizations/Silting/Fans/RankTwoTauTilting.lean), [`proveRankTwo`](../EFiniteCharacterizations/MainTheorems.lean) |
| Cor C | corollary | `cor:intro-weyman` | 233 | covered (Weyman's conjecture, formulated with `(dim-brick)`; compared in `Challenge.brickDiscreteMultiplicityFree`) | [`brick_discrete_iff_multiplicityFree`](../EFiniteCharacterizations/Geometry/ComponentMultiplicity.lean), [`proveBrickDiscreteMultiplicityFree`](../EFiniteCharacterizations/MainTheorems.lean) |
| 2.1 | lemma | `lem:fan-lattice` | 379 | covered: (1) lattice saturation and cone interior; (2) uniqueness of presilting complexes of a given class; (3) `Σ(Λᵒᵖ) = -Σ(Λ)` | [`mem_gVectorCone_iff_exists_in_add`](../EFiniteCharacterizations/Silting/Fans/ConeSaturation.lean), [`class_mem_intrinsicInterior_gVectorCone`](../EFiniteCharacterizations/Silting/Fans/ConeGeneratorInterior.lean), [`nonempty_homotopyIso_of_isPresilting_of_class_eq`](../EFiniteCharacterizations/Presentations/RigidPowers.lean), [`image_neg_star_fanSupport`](../EFiniteCharacterizations/Silting/Fans/OppositeFan.lean) |
| 2.2 | lemma | `lem:perpendicular` | 432 | covered (`τ`-perpendicular equivalence `J(U) ≃ mod Γ_U`, rank `n - r`, and cone-interior numerical torsion pairs) | [`basic_perpendicular_reduction`](../EFiniteCharacterizations/Silting/Reduction/PerpendicularSimpleCount.lean), [`cone_interior_torsion_identities`](../EFiniteCharacterizations/Stability/ConeTorsionPairs.lean) |
| 2.3 | proposition | `prop:covered-indep` | 456 | covered (rational and integral linear independence of stable brick classes at weights in `C°(U)`) | [`rationally_independent_stable_classes_in_cone`](../EFiniteCharacterizations/Stability/ConeTorsionPairs.lean), [`linearIndependent_stableClasses_eulerWeight`](../EFiniteCharacterizations/Stability/StableSeparationWeights.lean) |
| 2.4 | lemma | `lem:silting-signs` | 492 | covered | [`silting_interior_signs`](../EFiniteCharacterizations/Stability/ConeTorsionPairs.lean) |
| 2.5 | proposition | `prop:known-baseline` | 503 | covered (fixed-weight real chamber equivalences and determinantal semistability over `k̄`) | [`fixedWeightTorsionCriteria`](../EFiniteCharacterizations/Stability/ChamberRankTests.lean), [`semistable_iff_exists_inverting_multiple`](../EFiniteCharacterizations/Stability/SemistableDeterminant.lean) |
| 2.6 | lemma | `lem:rank-lemma` | 513 | covered | [`map_ker_le_range_of_maximal_geometric_rank`](../EFiniteCharacterizations/LinearAlgebra/GeometricRank.lean) |
| 2.7 | proposition | `prop:mp-witness` | 523 | covered (minimal-image bricks at `g ∉ Σ(Λ)`, corrected stability weight, and determinantal occurrence locus) | [`exists_hom_of_class_outside_fan`](../EFiniteCharacterizations/Stability/MissingWeightWitnesses.lean), [`minimal_image_stable_at_corrected_class`](../EFiniteCharacterizations/Stability/MissingWeightWitnesses.lean), [`exists_occurrence_polynomial`](../EFiniteCharacterizations/Stability/MissingWeightWitnesses.lean), [`exists_infinite_stable_classes_of_outside_fan`](../EFiniteCharacterizations/Stability/MissingWeightWitnesses.lean) |
| 2.8 | proposition | `prop:stable-witnesses` | 564 | covered (stable-brick families over arbitrary and infinite fields, and equal-class stable brick pairs) | [`exists_infinite_stableClassesOfEndolength_allFields`](../EFiniteCharacterizations/ScalarExtension/GroundFieldWitnesses.lean), [`exists_infinite_stable_fixed_class_and_endolength`](../EFiniteCharacterizations/Stability/MissingWeightWitnesses.lean), [`exists_equal_class_polytope_stable_pair`](../EFiniteCharacterizations/Stability/MissingWeightWitnesses.lean) |
| 2.9 | lemma | `lem:rigid-terms` | 581 | covered | [`exists_representative_on_terms`](../EFiniteCharacterizations/Presentations/RigidTerms.lean), [`exists_rational_pencil_automorphisms`](../EFiniteCharacterizations/Presentations/RigidTerms.lean) |
| 2.10 | lemma | `lem:pencil` | 591 | covered | [`pencil_hom_finrank_le`](../EFiniteCharacterizations/Presentations/PencilEuler.lean) |
| 3.1 | theorem | `thm:extraction` | 619 | covered | [`exists_rationally_dependent_stable_semibrick`](../EFiniteCharacterizations/Stability/RationalExtraction.lean), [`rationally_independent_and_jointly_stable_of_equalClassHom`](../EFiniteCharacterizations/Stability/RationalExtraction.lean) |
| 3.2 | theorem | `thm:core` | 683 | covered (`(E-fin)`, `(K₀-Hom)`, `(comp-tors)`, `(num-disj)`, `(fin-sbrick)`, `(n-sbrick)`) | [`isEFinite_iff_equalClassHom`](../EFiniteCharacterizations/Characterizations/HomCharacterizations.lean), [`isEFinite_iff_generatedTorsionClass_functoriallyFinite`](../EFiniteCharacterizations/Subcategories/CompactTorsionEquivalences.lean), [`isEFinite_iff_numericallyDisjointTorsionPairs`](../EFiniteCharacterizations/Characterizations/HomCharacterizations.lean), [`isEFinite_iff_finite_semibricks`](../EFiniteCharacterizations/Characterizations/HomCharacterizations.lean), [`isEFinite_iff_unique_fullSize_semibrick`](../EFiniteCharacterizations/Characterizations/HomCharacterizations.lean) |
| 3.3 | corollary | `cor:stable-brick` | 730 | covered | [`exists_projective_weight_stable_of_isEFinite`](../EFiniteCharacterizations/Characterizations/FixedClassFiniteness.lean) |
| 3.4 | corollary | `cor:exact-restriction` | 739 | covered (proved for every surjective `k`-algebra homomorphism, hence for all algebra quotients) | [`isEFinite_of_exact_embedding`](../EFiniteCharacterizations/Subcategories/ExactRestriction.lean), [`isEFinite_of_surjective`](../EFiniteCharacterizations/Subcategories/ExactRestriction.lean) |
| 4.1 | theorem | `thm:mon-dim` | 752 | covered | [`isEFinite_iff_injective_torsionMonoid`](../EFiniteCharacterizations/GrothendieckGroups/TorsionMonoidEmbedding.lean), [`isEFinite_iff_injective_weakTorsionMonoid`](../EFiniteCharacterizations/GrothendieckGroups/TorsionMonoidEmbedding.lean) |
| 4.2 | proposition | `thm:K0-tors` | 778 | covered | [`intrinsicGroup_on_compositionSupport`](../EFiniteCharacterizations/GrothendieckGroups/TorsionGrothendieckGroups.lean) |
| 4.3 | corollary | `cor:monoid-cancellation` | 795 | covered | [`isEFinite_iff_torsionMonoids_cancellative`](../EFiniteCharacterizations/GrothendieckGroups/MonoidCancellation.lean), [`isEFinite_iff_torsionFreeMonoids_cancellative`](../EFiniteCharacterizations/GrothendieckGroups/MonoidCancellation.lean) |
| 4.4 | remark | `rem:monoid-cancellation` | 802 | expository | — |
| 5.1 | theorem | `thm:wide` | 818 | covered (`W = J(U)` realization, `(wide)`, `(wide₁)`, `(brick-label)`) | [`exists_presilting_perpendicular_of_wide`](../EFiniteCharacterizations/Subcategories/WidePerpendicular.lean), [`isEFinite_iff_brickLabels`](../EFiniteCharacterizations/Subcategories/BrickLabels.lean) |
| 5.2 | theorem | `thm:walls` | 846 | covered (`(poly-brick)`, explicit `2(n - 1)(m + 1)^{n(n - 1)}` bound, and `(endo-stab)`) | [`isEFinite_iff_poly_brick`](../EFiniteCharacterizations/Stability/PolynomialBrickGrowth.lean), [`right_brick_count_le_of_isEFinite`](../EFiniteCharacterizations/Stability/SharpBrickGrowth.lean), [`isEFinite_iff_endo_stab`](../EFiniteCharacterizations/ScalarExtension/GroundFieldWitnesses.lean) |
| 5.3 | proposition | `prop:norm-polytope` | 883 | covered | [`normalizedSubmodulePolytope_vertices`](../EFiniteCharacterizations/Stability/NormalizedPolytopes.lean), [`normalizedSubmodulePolytope_count`](../EFiniteCharacterizations/Stability/NormalizedPolytopes.lean) |
| 5.4 | corollary | `cor:dimension-stability` | 908 | covered (both forward implications over any field and equivalences over infinite fields) | [`dimensionVectorFiniteness`](../EFiniteCharacterizations/Characterizations/BrickDimension.lean), [`isEFinite_iff_dim_brick`](../EFiniteCharacterizations/Characterizations/FixedClassFiniteness.lean), [`isEFinite_iff_dim_stab`](../EFiniteCharacterizations/Characterizations/FixedClassFiniteness.lean) |
| 5.5 | corollary | `cor:stable-bricks` | 917 | covered | [`exists_infinite_stable_of_infinite_bricks`](../EFiniteCharacterizations/Characterizations/BrickDimension.lean) |
| 6.1 | theorem | `thm:geometry` | 936 | covered (different route for `(moduli-pt)`: direct extension splitting in `Proj` instead of King's polystable classification) | [`equivalences_algebraicallyClosedField`](../EFiniteCharacterizations/Characterizations/Equivalences.lean), [`isEFinite_iff_kingClosedPoints`](../EFiniteCharacterizations/Geometry/GeometricCriteria.lean) |
| 6.2 | remark | `rem:brick-orbits` | 960 | expository | — |
| 7.1 | lemma | `lem:bimodule-trace` | 1000 | covered | [`invertedOn_summand_of_divisionSemistable`](../EFiniteCharacterizations/LargeModules/GenericBrickExclusion.lean) |
| 7.2 | lemma | `lem:tors-rad` | 1025 | covered (realized by the compact torsion class generated by the direct sum of the specified torsion subobjects, inside `T`) | [`exists_torsionRadical_subclass`](../EFiniteCharacterizations/Subcategories/TorsionRadical.lean) |
| 7.3 | lemma | `lem:field-generic` | 1032 | covered | [`no_generic_right_brick_of_isEFinite`](../EFiniteCharacterizations/LargeModules/GenericBrickExclusion.lean) |
| 7.4 | lemma | `lem:presilting-summand` | 1088 | covered | [`isInAdd_of_mem_thick`](../EFiniteCharacterizations/Silting/ThickSubcategories/PresiltingSummand.lean) |
| 7.5 | proposition | `prop:thick-generation` | 1100 | covered | [`exists_maximum_basic_thick_generator`](../EFiniteCharacterizations/Silting/ThickSubcategories/BoundedProjectiveHomotopy.lean) |
| 7.6 | proposition | `prop:grain` | 1159 | covered (different route: division ring built via Malcev–Neumann well-ordered series on a bi-ordered free group instead of Cohn's universal skew field) | [`exists_generic_grain_kernel_of_missing_weight`](../EFiniteCharacterizations/Stability/ChamberRankTests.lean), [`exists_division_injective_boundary`](../EFiniteCharacterizations/LargeModules/GenericGrainCriterion.lean) |
| 7.7 | lemma | `lem:exact-ab` | 1202 | covered | [`functoriallyFinite_of_full_exact_embedding`](../EFiniteCharacterizations/Subcategories/ExactAbelianApproximations.lean) |
| 7.8 | theorem | `thm:large` | 1213 | covered (also includes a direct rank-induction proof of `(E-fin) ⇒ (univ-loc)` and the residually finite-dimensional epimorphism criterion) | [`equivalences_arbitraryField`](../EFiniteCharacterizations/Characterizations/Equivalences.lean), [`rightUniversalLocalizationsFinite_of_isEFinite`](../EFiniteCharacterizations/RingEpimorphisms/UniversalLocalization.lean), [`isEFinite_iff_residuallyFinite_ring_epimorphisms`](../EFiniteCharacterizations/RingEpimorphisms/ResidualLocalization.lean) |
| 7.9 | corollary | `cor:artin-target` | 1246 | covered (`Tor₁^R(B, B)` defined from the canonical free presentation of the restricted regular module; the commutative Artinian base ring of `B` need not be `k`) | [`isEFinite_of_artin_epi_targets`](../EFiniteCharacterizations/RingEpimorphisms/ArtinTargets.lean), [`tauTiltingFinite_of_artin_epi_targets`](../EFiniteCharacterizations/RingEpimorphisms/ArtinTargets.lean) |
| 8.1 | lemma | `lem:mediant` | 1266 | covered | [`shiftedHomFinrank_mediant_bounds`](../EFiniteCharacterizations/Presentations/StableRigidComparison.lean) |
| 8.2 | lemma | `lem:sector` | 1295 | covered | [`exists_sector_cover_of_mediants_in_fan`](../EFiniteCharacterizations/Silting/Fans/ConeSaturation.lean) |
| 8.3 | proposition | `cor:stern-brocot` | 1302 | covered | [`sternBrocot_plane_test_and_count`](../EFiniteCharacterizations/Silting/Fans/SternBrocot.lean) |
| 8.4 | theorem | `thm:rank-two` | 1323 | covered (different route for `(E-fin) ⇒ brick-finite`: bounds bricks directly from the finite sector cover without invoking DIJ/Asai) | [`rankTwoEquivalences`](../EFiniteCharacterizations/Silting/Fans/RankTwoTauTilting.lean), [`isEFinite_iff_brickFinite_right_of_rank_le_two`](../EFiniteCharacterizations/Silting/Fans/RankTwoBricks.lean) |
| 8.5 | remark | `rem:sector-prop` | 1331 | expository (planar sector cover in arbitrary rank is `exists_presilting_sector_cover` in `SectorSubdivision.lean`) | [`exists_presilting_sector_cover`](../EFiniteCharacterizations/Silting/Fans/SectorSubdivision.lean) |
| 8.6 | example | `ex:kron-fan` | 1340 | expository | — |
| 8.7 | example | `ex:loop-subdivision` | 1375 | expository | — |
| 8.8 | example | `ex:omega-three` | 1420 | expository | — |
| A.1 | example | `ex:fq-kronecker` | 1469 | expository | — |
| A.2 | lemma | `lem:frob-dict` | 1475 | covered | [`absolute_frobenius_correspondence`](../EFiniteCharacterizations/ScalarExtension/AbsoluteFrobeniusCorrespondence.lean), [`isSemistable_extendObj_of_algebraic`](../EFiniteCharacterizations/ScalarExtension/AlgebraicSemistability.lean) |
| A.3 | proposition | `prop:fq-count` | 1493 | covered | [`exists_stable_bricks_of_each_degree`](../EFiniteCharacterizations/ScalarExtension/SharpFiniteFieldCount.lean) |
| A.4 | lemma | `lem:open-sep` | 1528 | covered | [`finite_of_hom_ext_separation`](../EFiniteCharacterizations/Stability/OpenSeparation.lean) |
| A.5 | lemma | `lem:field-wide` | 1559 | covered | [`exists_stable_brick_without_filtration_approximations`](../EFiniteCharacterizations/Subcategories/FieldWideWitness.lean) |
| A.6 | lemma | `lem:field-localization` | 1578 | covered | [`exists_infinite_residual_localization`](../EFiniteCharacterizations/RingEpimorphisms/ResidualLocalization.lean) |

---

## Cited inputs proved in the library

Because Mathlib is the only external dependency, every external mathematical theorem
used along the Lean proof routes is formalized inside `EFiniteCharacterizations/`:

- **Two-term silting, Bongartz completion, and `τ`-perpendicular reduction**
  (Adachi–Iyama–Reiten; Jasso; Demonet–Iyama–Reading–Reiten–Thomas): proved over an
  arbitrary field in [`Silting/Reduction/`](../EFiniteCharacterizations/Silting/Reduction).
- **Determinantal criterion for semistability and GIT semi-invariants**
  (King; Schofield; Derksen–Fei): proved in
  [`Stability/SemistableDeterminant.lean`](../EFiniteCharacterizations/Stability/SemistableDeterminant.lean)
  and [`Geometry/`](../EFiniteCharacterizations/Geometry).
- **Orthogonal objects in `thick(P)`** (Garcia, enlargement step of Theorem 4.14):
  proved in general triangulated categories in
  [`Silting/ThickSubcategories/PresiltingSummand.lean`](../EFiniteCharacterizations/Silting/ThickSubcategories/PresiltingSummand.lean).
- **Frobenius descent of bricks and semistability over finite fields** (after Deng–Du
  and Børve–Kaipel): proved in [`ScalarExtension/`](../EFiniteCharacterizations/ScalarExtension).
- **Division-ring coefficients with injective free tensor boundary** (replacing Cohn's
  universal skew field in Proposition 7.6): proved via Malcev–Neumann well-ordered
  series on a bi-ordered free group in [`DivisionRings/`](../EFiniteCharacterizations/DivisionRings).
- **Farkas's lemma / hyperplane separation** (used in rational extraction and real
  cone saturation): proved via Fourier–Motzkin elimination in
  [`LinearAlgebra/Farkas.lean`](../EFiniteCharacterizations/LinearAlgebra/Farkas.lean).
