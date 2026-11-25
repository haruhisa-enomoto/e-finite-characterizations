# Proof guide and comparison with the manuscript

Let `Λ` be a finite-dimensional algebra of rank `n` over a field `k`. In Lean, finite-dimensional right `Λ`-modules are modeled as finitely generated left modules over `Λᵐᵒᵖ` (`FGModuleCat Rᵐᵒᵖ`), and integral classes in `K₀(proj Λ)` are represented by two-term projective complexes `U = (P⁻¹ → P⁰)` with `g`-vector `[U] = [P⁰] - [P⁻¹]` ([`ProjectiveClasses.lean`](../../EFiniteCharacterizations/Presentations/ProjectiveClasses.lean)). A complex `U` is *presilting* when `Hom_{Kᵇ(proj Λ)}(U, U[1]) = 0`, and `Λ` is **E-finite** when the union `Σ(Λ)` of the real cones `C(U)` of two-term presilting complexes contains every integral lattice point in `K₀(proj Λ)`.

This guide explains how the Lean library proves Theorem A(I–III), Theorem B, Corollary C, and the companion body results, highlighting each place where the formalization takes a different or more self-contained route than the [November 25 manuscript](../MANUSCRIPT.md). See [`PAPER-CORRESPONDENCE.md`](../PAPER-CORRESPONDENCE.md) for the statement-by-statement index.

---

## 1. Covered weights and `τ`-perpendicular reduction (Section 2.1)

For a two-term complex `U = (P⁻¹ → u → P⁰)` with cokernel `C = H⁰(U)` and Nakayama kernel `N = ker(νu) = H⁻¹(νU)`, applying `Hom_Λ(-, X)` and Nakayama duality `D Hom_Λ(P, X) ≅ Hom_Λ(X, νP)` expresses the Euler pairing as

```text
⟨[U], [X]⟩ = dim_k Hom_Λ(C, X) - dim_k Hom_Λ(X, N).
```

When `U` is presilting and `θ` lies in the relative interior `C°(U)`, both terms carry fixed signs on subobjects and quotients, identifying the `θ`-semistable subcategory of `mod Λ` with the `τ`-perpendicular category

```text
J(U) = { X ∈ mod Λ | Hom_Λ(C, X) = 0 = Hom_Λ(X, N) }
```

and identifying the strict and weak numerical torsion pairs at `θ` with `(Fac C, C⊥)` and `(⊥N, Sub N)` ([`ConeTorsionPairs.lean`](../../EFiniteCharacterizations/Stability/ConeTorsionPairs.lean)).

To identify `J(U)` with a module category of smaller rank (Lemma 2.2), Lean constructs the basic Bongartz completion `T` of `U` ([`BasicBongartzCompletion.lean`](../../EFiniteCharacterizations/Silting/Reduction/BasicBongartzCompletion.lean)) and divides `B = H⁰(T)` by the trace of `C` in `B`. The quotient `G` is a projective generator of `J(U)` whose endomorphism ring is `Γ_U = End_Λ(B) / [C]`, so `Hom_Λ(G, -)` is an exact equivalence `J(U) ≃ mod Γ_U` ([`PerpendicularReduction.lean`](../../EFiniteCharacterizations/Silting/Reduction/PerpendicularReduction.lean)).

**Difference in the rank count (`n - r`):** Where the manuscript counts complementary projective covers using `τ`-tilting bijection results, Lean proves two elementary linear-algebraic inequalities directly over any field. If `U` has `r` nonisomorphic indecomposable summands and `J(U)` has `s` simple objects up to isomorphism, separating each simple of `J(U)` by a Bongartz summand produces `r + s` linearly independent weights (`r + s ≤ n`), while completing `U` against each indecomposable projective shows that `r + s` classes span `K₀(proj Λ)` (`n ≤ r + s`), giving `s = n - r` ([`BongartzCounting.lean`](../../EFiniteCharacterizations/Silting/Reduction/BongartzCounting.lean), [`PerpendicularSimpleCount.lean`](../../EFiniteCharacterizations/Silting/Reduction/PerpendicularSimpleCount.lean)). In particular, the dimension vectors of the `θ`-stable bricks are linearly independent in `K₀(mod Λ)` ([`StableSeparationWeights.lean`](../../EFiniteCharacterizations/Stability/StableSeparationWeights.lean)).

---

## 2. Missing integral weights and Frobenius descent (Section 2.2 & Appendix A)

Suppose `g = [P⁰] - [P⁻¹] ∈ K₀(proj Λ)` lies outside `Σ(Λ)`. Then no differential `p : P⁻¹ → P⁰` is presilting, so every `p` admits a nonzero homomorphism `f : coker p → ker(νp)`. Choosing `f` whose image `B = im f` has minimal `k`-dimension forces `B` to be a brick (any nonzero noninvertible endomorphism would have a smaller nonzero image) and makes `B` stable at the corrected integral weight

```text
θ_corr(B) = (dim_k B) g - ⟨g, [B]⟩ [Λ]
```

([`MissingWeightWitnesses.lean`](../../EFiniteCharacterizations/Stability/MissingWeightWitnesses.lean)). Because `dim_k B` is bounded by `dim_k P⁰`, only finitely many corrected weights `θ_corr(B)` occur as `p` varies over `Hom_Λ(P⁻¹, P⁰)`.

- **Over an infinite field:** Each fixed brick `B` can occur as a subquotient `coker p → B ↪ ker(νp)` only on a proper determinantal hypersurface in `Hom_Λ(P⁻¹, P⁰)`. Since a vector space over an infinite field is not a finite union of proper hypersurfaces, infinitely many nonisomorphic bricks occur at a single integral weight and dimension vector (Proposition 2.7).
- **Over a finite field `k = 𝔽_q`:** Extending scalars to `𝔽_{q^s}` and applying the polynomial-locus bound produces a growing supply of geometric stable bricks, which Lean descends to `k` via the absolute Frobenius correspondence ([`AbsoluteFrobeniusCorrespondence.lean`](../../EFiniteCharacterizations/ScalarExtension/AbsoluteFrobeniusCorrespondence.lean), Lemma A.2): each `θ`-stable brick `B` over `k` splits over `k̄` into a single Frobenius orbit of `[End_Λ(B) : k]` geometric stable bricks, each of `k̄`-dimension equal to `endolength(B)`. Counting orbits yields at least `q^s / (c₀ s)` ground bricks across a fixed finite set of integral weights at bounded endolength (Proposition A.3, [`SharpFiniteFieldCount.lean`](../../EFiniteCharacterizations/ScalarExtension/SharpFiniteFieldCount.lean)). By pigeonhole on normalized submodule polytopes, every E-infinite algebra over *any* field admits two nonisomorphic bricks of the same dimension vector stable at a single integral weight (Proposition 2.8, [`GroundFieldWitnesses.lean`](../../EFiniteCharacterizations/ScalarExtension/GroundFieldWitnesses.lean)).

---

## 3. Arbitrary-field characterizations in Theorem A(I)

### 3.1 `(K₀-Hom)`, numerical disjointness, and semibricks (Section 3)
If `M` and `N` are nonzero modules with `[M] = [N]` and `Hom_Λ(M, N) = 0`, an inductive extraction on `[M]` produces a nonempty finite semibrick whose dimension vectors are linearly dependent and whose members are simultaneously stable at one integral weight (Theorem 3.1, [`RationalExtraction.lean`](../../EFiniteCharacterizations/Stability/RationalExtraction.lean)). Since stable bricks at any covered weight have linearly independent classes, `(E-fin)` implies `(K₀-Hom)`. Conversely, two nonisomorphic bricks of equal dimension vector stable at a common weight have `Hom = 0`, giving `(K₀-Hom) ⇒ (E-fin)`.

Under `(K₀-Hom)`, no torsion pair `(T, F)` can have nonzero `X ∈ T` and `Y ∈ F` of equal class (`(num-disj)`), and every finite semibrick is jointly stable at an integral weight and therefore has linearly independent classes—bounding its size by `n` (`(fin-sbrick)`) and forcing any `n`-element semibrick to be stabilized by the zero weight, whose stable bricks are the `n` simple modules (`(n-sbrick)`, [`HomCharacterizations.lean`](../../EFiniteCharacterizations/Characterizations/HomCharacterizations.lean)).

### 3.2 Compact torsion classes and fixed real weights (Sections 2.2 & 3.2)
For a singly generated torsion class `T = ⊥(M⊥)`, `(K₀-Hom)` separates submodule classes of `M` from quotient classes of generators of `T` by a linear weight; when `Λ` is E-finite, the corresponding presilting cone supplies functorial finiteness (`(comp-tors)`, [`CompactTorsionEquivalences.lean`](../../EFiniteCharacterizations/Subcategories/CompactTorsionEquivalences.lean)). More generally, Proposition 2.5(1) fixes an arbitrary *real* weight `v ∈ K₀(proj Λ)_ℝ` (even over an E-infinite algebra) and proves `v ∈ Σ(Λ)` equivalent to functorial finiteness of its numerical torsion pairs. The key step realizes simultaneous surjectivity on `Hom(-, B)` and injectivity on `Hom(-, M)` at a single ground-field differential of class `t g` by passing to a point of maximal geometric rank over `k̄` and descending along a finite field extension ([`OneSidedDeterminants.lean`](../../EFiniteCharacterizations/Stability/OneSidedDeterminants.lean), [`ChamberRankTests.lean`](../../EFiniteCharacterizations/Stability/ChamberRankTests.lean)).

### 3.3 Grothendieck monoids of torsion classes (Section 4)
Let `M(T)` be the Grothendieck monoid of a torsion class `T ⊆ mod Λ`. Assuming `(K₀-Hom)`, if `X, Y ∈ T` satisfy `[X] = [Y] ≠ 0`, there is a nonzero map `f : X → Y`; pushing out short exact sequences in `T` along `f` reduces the equality `[X]_{M(T)} = [Y]_{M(T)}` by induction on composition length (`(mon-dim)`, Theorem 4.1, [`TorsionMonoidEmbedding.lean`](../../EFiniteCharacterizations/GrothendieckGroups/TorsionMonoidEmbedding.lean)). Conversely, two nonisomorphic `θ`-stable bricks of equal dimension vector cannot become equal in `M(T_θ)` for the weak `θ`-semistable torsion class `T_θ`.

Proposition 4.2 shows that the group completion `K₀(T)` embeds into `K₀(mod Λ)` for *every* torsion or torsion-free class over any algebra ([`TorsionGrothendieckGroups.lean`](../../EFiniteCharacterizations/GrothendieckGroups/TorsionGrothendieckGroups.lean)). Consequently, `M(T) → K₀(mod Λ)` is injective if and only if `M(T)` is cancellative, and `k`-duality transfers this characterization to torsion-free classes (Corollary 4.3, [`MonoidCancellation.lean`](../../EFiniteCharacterizations/GrothendieckGroups/MonoidCancellation.lean)).

### 3.4 Wide subcategories, `Filt(B)`, and brick labels (Section 5.1)
If `Λ` is E-finite and `W ⊆ mod Λ` is wide, `sim W` is a finite semibrick jointly stable at an integral weight. Choosing a presilting cone `C(U)` of maximal dimension whose interior stabilizes `sim W` rules out any extra simple object in `J(U)` and realizes `W = J(U)`, which is functorially finite (`(wide)`, [`WidePerpendicular.lean`](../../EFiniteCharacterizations/Subcategories/WidePerpendicular.lean)). Specializing to `W = Filt(B)` for a single brick `B` chooses a codimension-one cone `C(U)` where `J(U) = Filt(B)`; its strict and weak torsion classes form a cover `T' ⊊ T` in `f-tors Λ` with `Filt(B) = T ∩ (T')⊥` (`(brick-label)`, [`BrickLabels.lean`](../../EFiniteCharacterizations/Subcategories/BrickLabels.lean)). Conversely, when `Λ` is E-infinite, Hom–Ext separation over `k̄` (Lemma A.4, [`OpenSeparation.lean`](../../EFiniteCharacterizations/Stability/OpenSeparation.lean)) descends to produce a stable brick `B` over `k` for which `Filt(B)` has neither left nor right approximations (Lemma A.5, [`FieldWideWitness.lean`](../../EFiniteCharacterizations/Subcategories/FieldWideWitness.lean)).

### 3.5 Normalized submodule polytopes and polynomial growth (Section 5.2)
For a brick `B` of endolength `r`, dividing the projective Hom coordinates `[U] ↦ dim_k Hom_Λ(P_i, U)` of submodules `U ⊆ B` by `dim_k End_Λ(B)` places every extreme point of its normalized submodule polytope in the integer grid `{0, 1, …, r}^n` (Proposition 5.3, [`NormalizedPolytopes.lean`](../../EFiniteCharacterizations/Stability/NormalizedPolytopes.lean)). Under `(E-fin)`, two bricks with the same dimension vector and normalized submodule polytope share a stabilizing weight and are isomorphic, proving `(brick-discrete)` and `(endo-stab)`. Counting realizable sign patterns of weights on classes of length `≤ m` yields the explicit bound `2(n - 1)(m + 1)^{n(n - 1)}` for `n ≥ 2` (`(poly-brick)`, Theorem 5.2, [`PolynomialBrickGrowth.lean`](../../EFiniteCharacterizations/Stability/PolynomialBrickGrowth.lean), [`SharpBrickGrowth.lean`](../../EFiniteCharacterizations/Stability/SharpBrickGrowth.lean)).

### 3.6 Generic bricks, generic grains, and thick generation (Section 7)
- **Excluding generic bricks and grains (`(E-fin) ⇒ (no-gen-brick) ⇒ (no-gen-grain)`):** Viewing a generic brick `G` as a `(Λ, Δ)`-bimodule of finite length over `Δ = End_Λ(G)`, `Δ`-dimension defines a real-valued stability weight. Under `(E-fin)`, a presilting complex realizing a `Δ`-semistable reduction weight places a nonzero `Δ`-subquotient of `G` inside the large `τ`-perpendicular category `Mod Γ_U` of smaller rank (Lemmas 7.1–7.3, [`GenericBrickExclusion.lean`](../../EFiniteCharacterizations/LargeModules/GenericBrickExclusion.lean)), ruling out `G` by induction on `n`. Since the socle of any generic grain over its local endomorphism ring is a generic brick, `(no-gen-grain)` follows.
- **Constructing generic grains without Cohn's skew field (`¬(E-fin) ⇒ ¬(no-gen-grain)`):** Where Proposition 7.6 of the paper uses Cohn's universal skew field, Lean constructs a division ring `D` over `k` directly from Malcev–Neumann well-ordered series on a bi-ordered finitely generated free group ([`DivisionRings/`](../../EFiniteCharacterizations/DivisionRings)). Using `k`-algebraically independent noncommuting coefficients in `D` to form a generic differential of injectives produces an endofinite `Λ`-module `N` realizing the numerical torsion pair at a missing integral weight `γ ∉ Σ(Λ)`; because `γ ∉ Σ(Λ)` rules out a finite cogenerator (Proposition 2.5(1)), `N` has an infinite-dimensional indecomposable summand, which is a generic grain ([`GenericGrainCriterion.lean`](../../EFiniteCharacterizations/LargeModules/GenericGrainCriterion.lean), [`ChamberRankTests.lean`](../../EFiniteCharacterizations/Stability/ChamberRankTests.lean)).
- **Presilting generation of `K^{[-1,0]}(proj Λ)` (`(thick-gen)`):** Given a thick subcategory `H ⊆ K^{[-1,0]}(proj Λ)` over an E-finite algebra, choose a basic presilting object `U ∈ H` with the maximum number of indecomposable summands. Mapping cones reduce shifted Hom dimensions against `U`, and the rational pencil together with splitting nilpotent endomorphisms embeds any two-sided Hom-orthogonal object into `add(U)`, while Garcia's triangulated lemma (Lemma 7.4, [`PresiltingSummand.lean`](../../EFiniteCharacterizations/Silting/ThickSubcategories/PresiltingSummand.lean)) handles the converse inclusion ([`BoundedProjectiveHomotopy.lean`](../../EFiniteCharacterizations/Silting/ThickSubcategories/BoundedProjectiveHomotopy.lean), [`ThickGenerationCriterion.lean`](../../EFiniteCharacterizations/Silting/ThickSubcategories/ThickGenerationCriterion.lean)).

<a id="9-finite-localization-by-the-rigid-pencil"></a>

### 3.7 Universal localizations and ring epimorphisms (Section 7.2 & Appendix A.2)
**Direct inductive route for `(E-fin) ⇒ (univ-loc)`:** While the paper deduces finite-dimensionality of universal localizations from `(thick-gen)`, Lean also proves `(E-fin) ⇒ (univ-loc)` directly by induction on the rank `n` ([`UniversalLocalization.lean`](../../EFiniteCharacterizations/RingEpimorphisms/UniversalLocalization.lean)). For any noninvertible map `σ : P⁻¹ → P⁰` in the inverted set:
1. If `[P⁰] - [P⁻¹] ≠ 0`, E-finiteness supplies a presilting differential `u` on stabilized projective terms, and specializing along the pencil from `u` to `σ` shows that any module (even infinite-dimensional) inverting `σ` also inverts `u` ([`RigidPencilInversion.lean`](../../EFiniteCharacterizations/Presentations/RigidPencilInversion.lean)), passing to the reduction algebra `Γ_u` of strictly smaller rank.
2. If `[P⁰] = [P⁻¹]`, Fitting decomposition splits off a nonzero projective summand killed by every `σ`-inverting module, passing to an idempotent quotient of smaller rank.

Conversely, at a missing integral class `g ∉ Σ(Λ)`, gluing a family of stable representations over a localized polynomial ring produces both an infinite-dimensional simple Artinian epimorphic target (`¬(ring-epi)`) and a single projective map `p` whose universal localization `Λ_p` remains infinite-dimensional even modulo the intersection of the annihilators of all its finite-dimensional modules (Lemma A.6, [`ResidualLocalization.lean`](../../EFiniteCharacterizations/RingEpimorphisms/ResidualLocalization.lean)).

**Artin targets (Corollary 7.9):** Every universal localization `f : Λ → Γ` has `Tor₁^Λ(Γ, Γ) = 0`, proved via a syzygy pushout on the canonical free presentation of `Γ` ([`LocalizationTor.lean`](../../EFiniteCharacterizations/RingEpimorphisms/LocalizationTor.lean)). If `Γ` is an Artin algebra (hence Artinian), the descending chain condition forces the intersection of its finite-dimensional representation kernels to be a single kernel, making its residual quotient finite-dimensional over `k` ([`ArtinianResidual.lean`](../../EFiniteCharacterizations/RingEpimorphisms/ArtinianResidual.lean))—contradicting Lemma A.6 when `Λ` is E-infinite ([`ArtinTargets.lean`](../../EFiniteCharacterizations/RingEpimorphisms/ArtinTargets.lean)).

---

## 4. Infinite and algebraically closed fields (Theorem A(II–III) & Corollary C)

- **Infinite fields (`A(II)`):** Over *every* field, E-finiteness implies `(dim-brick)` and `(dim-stab)` because `dim_k End_Λ(B) ≥ 1` bounds endolength at a fixed dimension vector ([`FixedClassFiniteness.lean`](../../EFiniteCharacterizations/Characterizations/FixedClassFiniteness.lean)). When `k` is infinite, Proposition 2.7 supplies the converse by producing infinitely many stable bricks at *one* dimension vector and integral weight.
- **Representation varieties and King moduli (`A(III)` & Corollary C):** Over `k = k̄`, Morita reduction equips `Λ` with a split basic presentation `C.A` ([`BasicReduction.lean`](../../EFiniteCharacterizations/Algebra/BasicReduction.lean), [`BasicPresentation.lean`](../../EFiniteCharacterizations/Geometry/BasicPresentation.lean)), and King's moduli scheme `M_θ^{ss}(Λ, d)` is constructed as `Proj` of the graded `GL(d)`-semi-invariant ring ([`KingSemiInvariants.lean`](../../EFiniteCharacterizations/Geometry/KingSemiInvariants.lean)).
  - *Difference in `(moduli-pt)`:* Instead of importing King's theorem that closed points classify polystable modules, Lean proves directly that scaling extension blocks degenerates any `θ`-semistable representation without changing values of homogeneous semi-invariants, and under `(E-fin)` linear independence of stable classes uniquely fixes the Jordan–Hölder multiplicities, leaving at most one closed point in `Proj`; conversely, determinant semi-invariants separate two nonisomorphic `θ`-stable bricks of equal dimension vector ([`KingModuli.lean`](../../EFiniteCharacterizations/Geometry/KingModuli.lean)).
  - *Open loci (`(open-brick)` and `(open-wide)`):* Voigt/Hom-dimension semicontinuity makes brick orbits open when `Ext¹(B, B) = 0` or via stability open loci, and realizing `W = J(U)` expresses `{X ∈ rep(Λ, d) | X ∈ W}` by Hom-vanishing conditions ([`GeometricCriteria.lean`](../../EFiniteCharacterizations/Geometry/GeometricCriteria.lean)).
  - *Weyman's conjecture (Corollary C):* On any irreducible component `Z ⊆ rep(Λ, d)` admitting a nonzero semi-invariant of weight `w`, a general point is `w`-semistable; degenerating to its polystable limit inside `Z` and using unique stable multiplicities under `(E-fin)` shows `dim_k SI(Z)_w ≤ 1`, while `(dim-brick) ⇔ (E-fin)` over `k̄` completes the equivalence ([`ComponentMultiplicity.lean`](../../EFiniteCharacterizations/Geometry/ComponentMultiplicity.lean)).

---

## 5. Rank at most two (Theorem B, Section 8)

When `n ≤ 2`, E-finiteness is trivial in ranks `0` and `1` ([`RankTwoBricks.lean`](../../EFiniteCharacterizations/Silting/Fans/RankTwoBricks.lean)). For `n = 2` with indecomposable projectives `P₁, P₂`, the positive and negative quadrants of `K₀(proj Λ)_ℝ ≅ ℝ²` are spanned by `([P₁], [P₂])` and `(-[P₁], -[P₂])`. Each mixed quadrant begins with an ordered boundary pair `(E, L)` of presilting complexes satisfying `Hom(E, L[1]) = 0`.

- If `e(L, E) := dim_k Hom_{Kᵇ(proj Λ)}(L, E[1]) = 0`, then `E ⊕ L` is silting and the sector is a single silting cone.
- If `e(L, E) ≥ 1`, E-finiteness provides a two-term presilting complex `Z` representing the mediant `[E] + [L]`. Lemma 8.1 ([`StableRigidComparison.lean`](../../EFiniteCharacterizations/Presentations/StableRigidComparison.lean)) compares `Z` with the cone of any nonzero map `L → E[1]` via Lemma 2.10 to prove `e(E, Z) = e(Z, L) = 0` and `e(Z, E), e(L, Z) < e(L, E)`.

Thus Stern–Brocot subdivision terminates at depth at most `e(L, E)`, covering the plane with finitely many silting cones (at most `2^x + 2^y + 2` basic silting complexes, Proposition 8.3, [`SternBrocot.lean`](../../EFiniteCharacterizations/Silting/Fans/SternBrocot.lean)).

**Difference in the final step:** Rather than citing the general `Σ(Λ) = ℝ^n ⇒ brick-finite` theorem of Asai and Demonet–Iyama–Jasso, Lean reads off both `brick-finite` and `τ-tilting finite` directly from the finite sector cover: every brick is stable on one of the finitely many boundary rays or interior faces, and every indecomposable `τ`-rigid module has its `g`-vector among the finitely many rays ([`RankTwoBricks.lean`](../../EFiniteCharacterizations/Silting/Fans/RankTwoBricks.lean), [`RankTwoTauTilting.lean`](../../EFiniteCharacterizations/Silting/Fans/RankTwoTauTilting.lean)).
