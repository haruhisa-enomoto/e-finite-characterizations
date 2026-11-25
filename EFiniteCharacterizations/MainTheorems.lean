module

public import EFiniteCharacterizations.Statement
public import EFiniteCharacterizations.Characterizations.Equivalences
public import EFiniteCharacterizations.Geometry.ComponentMultiplicity
public import EFiniteCharacterizations.Silting.Fans.RankTwoTauTilting

/-!
# Bridge from the proof library to the standalone statements

This file proves the five standalone predicates defined in
`EFiniteCharacterizations/Statement.lean` from the library:

* `proveArbitraryField` (**Theorem A(I)**): proved from `equivalences_arbitraryField`
  (`Characterizations/Equivalences.lean`), using `isEFinite_iff_twoTermThickGeneration`
  (`Silting/ThickSubcategories/ThickGenerationCriterion.lean`) for `(thick-gen)`.
* `proveInfiniteField` (**Theorem A(II)**, counterpart to `equivalences_infiniteField`):
  proved directly from `isEFinite_iff_finite_brickClassesOfClass` and
  `isEFinite_iff_finite_stableClassesOfClass` (`Characterizations/FixedClassFiniteness.lean`).
* `proveAlgebraicallyClosedField` (**Theorem A(III)**, counterpart to
  `equivalences_algebraicallyClosedField`): constructs a split basic Morita chart via
  `basicPresentation` and proves chart invariance from
  `atMostOneKingClosedPoint_of_isEFinite`, `isEFinite_iff_kingClosedPoints`, and
  `isEFinite_iff_open_vertex_loci` (`Geometry/`).
* `proveRankTwo` (**Theorem B**): proved from `rankTwoEquivalences`
  (`Silting/Fans/RankTwoTauTilting.lean`).
* `proveBrickDiscreteMultiplicityFree` (**Corollary C**, counterpart to
  `brick_discrete_iff_multiplicityFree`): combines
  `isEFinite_iff_finite_brickClassesOfClass` with
  `rank_componentWeightSpace_le_one_of_isEFinite` and `isEFinite_iff_multiplicityFree`
  (`Geometry/ComponentMultiplicity.lean`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R]

private theorem eFinite_iff : Statement.EFinite R ↔ IsEFinite R := by
  constructor
  · intro h g
    obtain ⟨P,Q,d,hd,hg⟩ := h g
    exact ⟨⟨P.val,Q.val,P.property,Q.property,d⟩,hd,hg⟩
  · intro h g
    obtain ⟨P,hd,hg⟩ := h g
    exact ⟨⟨P.source,P.projective_source⟩,⟨P.target,P.projective_target⟩,P.differential,hd,hg⟩

private theorem tauTiltingFinite_iff (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]
    [IsNoetherianRing R] : Statement.TauTiltingFinite R ↔ IsTauTiltingFinite (R := R) k := by
  unfold Statement.TauTiltingFinite IsTauTiltingFinite
  apply iff_of_eq
  apply congrArg Set.Finite
  ext s
  constructor
  · rintro ⟨M,⟨P,Q,d,hd,hM⟩,hn,hs⟩
    exact ⟨M,(isTauRigid_iff_exists_presilting_cokernel k M).2
      ⟨⟨P.val,Q.val,P.property,Q.property,d⟩,hd,hM⟩,hn,hs⟩
  · rintro ⟨M,hM,hn,hs⟩
    obtain ⟨P,hd,h⟩ := (isTauRigid_iff_exists_presilting_cokernel k M).1 hM
    exact ⟨M,⟨⟨P.source,P.projective_source⟩,⟨P.target,P.projective_target⟩,P.differential,hd,h⟩,hn,hs⟩

/-- In rank at most two, τ-tilting finiteness and brick-finiteness each characterize E-finiteness. -/
theorem proveRankTwo : Statement.RankTwo.{u} := by
  intro k R _ _ _ _ hr
  letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  obtain ⟨ht,hb⟩ := rankTwoEquivalences (R := R) k hr
  exact ⟨eFinite_iff.trans (ht.trans (tauTiltingFinite_iff k).symm), eFinite_iff.trans hb⟩


private def presentation (D : TwoTerm R) : Statement.Differential R :=
  ⟨⟨D.source,D.projective_source⟩,⟨D.target,D.projective_target⟩,D.differential⟩

private def complexOf (D : Statement.Differential R) : TwoTerm R :=
  ⟨D.source.val,D.target.val,D.source.property,D.target.property,D.d⟩

private theorem thick_iff [IsNoetherianRing R] :
    Statement.ThickGeneration R ↔ TwoTermThickGeneration R := by
  constructor
  · intro h H hH
    obtain ⟨U,hu,hU⟩ := h (H ∘ complexOf)
      ⟨hH.zero, fun A B C ↦ hH.triangles (complexOf A) (complexOf B) (complexOf C),
        fun A B ↦ hH.retracts (complexOf A) (complexOf B)⟩
    exact ⟨complexOf U,hu,fun X ↦ hU (presentation X)⟩
  · intro h H hH
    obtain ⟨U,hu,hU⟩ := h (H ∘ presentation)
      ⟨hH.1,fun A B C ↦ hH.2.1 (presentation A) (presentation B) (presentation C),
        fun A B ↦ hH.2.2 (presentation A) (presentation B)⟩
    exact ⟨presentation U,hu,fun X ↦ hU (complexOf X)⟩

private theorem inverts_iff {B : Type u} [Ring B] (S : Set (Statement.Differential R)) (f : R →+* B) :
    (∀ D ∈ S, D.inverts f) ↔ InvertsFamily (fun i : presentation ⁻¹' S ↦ i.val) f := by
  exact ⟨fun h i ↦ (i.val.isIso_induce_iff_regular f).2 (h _ i.property),
    fun h D hD ↦ ((complexOf D).isIso_induce_iff_regular f).1 (h ⟨complexOf D,hD⟩)⟩

private theorem localization_iff {B : Type u} [Ring B] (S : Set (Statement.Differential R)) (f : R →+* B) :
    Statement.Localization S f ↔ IsUniversalLocalization (fun i : presentation ⁻¹' S ↦ i.val) f := by
  exact ⟨fun h ↦ ⟨(inverts_iff S f).1 h.1, fun C _ g hg ↦ h.2 C g ((inverts_iff S g).2 hg)⟩,
    fun h ↦ ⟨(inverts_iff S f).2 h.inverts, fun C _ g hg ↦ h.desc C g ((inverts_iff S g).1 hg)⟩⟩

private theorem localizationFinite_iff (k : Type u) [Field k] [Algebra k R] :
    Statement.LocalizationFinite (k := k) R ↔ RightUniversalLocalizationsFinite k R := by
  constructor
  · intro h S B _ _ f hf
    exact h (complexOf ⁻¹' S) B f ((localization_iff _ _).2 hf)
  · intro h S B _ _ f hf
    exact h (presentation ⁻¹' S) B f ((localization_iff _ _).1 hf)

variable [IsNoetherianRing R]

private theorem filtration_eq (B : FGModuleCat.{u} R) : Statement.Filt B = FilteredBy B := by
  funext X
  apply propext
  constructor
  · intro h
    induction h with
    | zero hz => exact .zero hz
    | extend S hs e _ ih => exact .cons ⟨S.f,S.g,S.zero,hs⟩ e ih
  · intro h
    induction h with
    | zero hz => exact .zero hz
    | cons s e _ ih => exact .extend (ShortComplex.mk s.i s.p s.w) s.shortExact e ih

private theorem wide_iff (W : ObjectProperty (FGModuleCat.{u} R)) : Statement.Wide W ↔ IsWideClass W :=
  ⟨fun h ↦ ⟨h.zero_mem,h.iso_mem,h.kernel_mem,h.cokernel_mem,h.extension_mem⟩,
    fun h ↦ ⟨h.zero_mem,h.iso_mem,h.kernel_mem,h.cokernel_mem,h.extension_mem⟩⟩

private theorem labels_iff : Statement.BrickLabels R ↔ BrickLabels R := by
  constructor
  · intro h B hb
    obtain ⟨T,U,ht,e⟩ := h B hb
    exact ⟨T,U,ht,(filtration_eq B).symm.trans (funext (fun X ↦ propext (e X)))⟩
  · intro h B hb
    obtain ⟨T,U,ht,e⟩ := h B hb
    exact ⟨T,U,ht,fun X ↦ Iff.of_eq (congrFun ((filtration_eq B).trans e) X)⟩

private theorem monoid_iff :
    Statement.MonoidDimension R ↔ ∀ T : ObjectProperty (FGModuleCat.{u} R),
      T.IsClosedUnderQuotients → T.IsClosedUnderExtensions → T 0 →
      Function.Injective (GrothendieckMonoid.dimensionMap T) := by
  unfold Statement.MonoidDimension
  apply forall_congr'
  intro T
  have hr : Statement.ExactMonoidRel T = GrothendieckMonoid.Relation T := by
    funext x y
    apply propext
    constructor <;> intro h <;> cases h with
    | zero X h => exact .zero X h
    | iso X Y e => exact .iso X Y e
    | exact S h a b c => exact .exact S h a b c
  rw [hr]
  apply forall_congr'
  intro _
  apply forall_congr'
  intro he
  apply forall_congr'
  intro h₀
  rw [GrothendieckMonoid.dimensionMap_injective_iff T h₀]
  exact forall_congr' fun X ↦ forall_congr' fun Y ↦ forall_congr' fun hx ↦ forall_congr' fun hy ↦
    forall_congr' fun _ ↦ (addConGen (GrothendieckMonoid.Relation T)).eq.symm

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

private theorem stable_iff (P Q : Statement.Proj R) (X : FGModuleCat.{u} R) :
    Statement.Stable k P Q X ↔
      (projectiveClassWeight k (ProjectiveClass.of Q - ProjectiveClass.of P)).IsStable X := by
  letI := P.property
  letI := Q.property
  have eval (Y : FGModuleCat.{u} R) :
      (projectiveClassWeight k (ProjectiveClass.of Q - ProjectiveClass.of P)).eval Y =
      Statement.weight k P Q Y := by
    rw [map_sub, projectiveClassWeight_of, projectiveClassWeight_of]
    change (projectiveHomWeight k Q.val).eval Y - (projectiveHomWeight k P.val).eval Y = _
    rw [projectiveHomWeight_eval,projectiveHomWeight_eval]
    rfl
  simp only [Statement.Stable,Weight.IsStable,eval]

private theorem stableClasses_eq (P Q : Statement.Proj R) (F : FGModuleCat.{u} R → Prop) :
    Statement.classes (fun X ↦ F X ∧ Statement.Stable k P Q X) =
      Statement.classes (fun X ↦ F X ∧ (projectiveClassWeight k
        (ProjectiveClass.of Q - ProjectiveClass.of P)).IsStable X) := by
  simp only [stable_iff]

/-- The two criteria for infinite ground fields, with integral weights represented by differences of projectives. -/
theorem proveInfiniteField : Statement.InfiniteField.{u} := by
  intro k A _ _ _ _ _
  letI := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  letI := IsArtinianRing.of_finite k Aᵐᵒᵖ
  refine ⟨eFinite_iff.trans (isEFinite_iff_finite_brickClassesOfClass k), eFinite_iff.trans
    ((isEFinite_iff_finite_stableClassesOfClass k).trans ?_)⟩
  constructor
  · intro h P Q c
    rw [stableClasses_eq k P Q]
    exact h _ c
  · intro h g c
    obtain ⟨Q,P,rfl⟩ := g.exists_sub
    have hs := h P Q c
    rw [stableClasses_eq k P Q] at hs
    exact hs

/-- The seventeen module-theoretic, homotopical and ring-theoretic tests over arbitrary fields. -/
theorem proveArbitraryField : Statement.ArbitraryField.{u} := by
  intro k A _ _ _ _
  letI := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  letI := IsArtinianRing.of_finite k Aᵐᵒᵖ
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀,h₁₁,h₁₂,h₁₃,h₁₄,_,h₁₆,h₁₇⟩ :=
    equivalences_arbitraryField k A
  refine ⟨eFinite_iff.trans h₁, eFinite_iff.trans (h₂.trans monoid_iff.symm),
    eFinite_iff.trans h₃, eFinite_iff.trans h₄, eFinite_iff.trans (h₅.trans ?_),
    eFinite_iff.trans (h₆.trans ?_), eFinite_iff.trans (h₇.trans labels_iff.symm),
    eFinite_iff.trans h₈, eFinite_iff.trans h₉, eFinite_iff.trans h₁₀,
    eFinite_iff.trans (h₁₁.trans ?_), eFinite_iff.trans h₁₂, eFinite_iff.trans (h₁₃.trans ?_),
    eFinite_iff.trans (h₁₄.trans ?_), eFinite_iff.trans ((isEFinite_iff_twoTermThickGeneration k).trans
      thick_iff.symm), eFinite_iff.trans (h₁₆.trans (localizationFinite_iff k).symm),eFinite_iff.trans h₁₇⟩
  · exact forall_congr' fun W ↦ imp_congr_left (wide_iff W).symm
  · simp only [filtration_eq]
    rfl
  · constructor
    · intro h P Q r hr
      rw [stableClasses_eq k P Q]
      exact h _ r hr
    · intro h g r hr
      obtain ⟨Q,P,rfl⟩ := g.exists_sub
      have hs := h P Q r hr
      rw [stableClasses_eq k P Q] at hs
      exact hs
  · apply not_congr
    apply exists_congr
    intro M
    exact ⟨fun h ↦ ⟨h.infinite,h.invertible,h.endofinite⟩,fun ⟨a,b,c⟩ ↦ ⟨a,b,c⟩⟩
  · apply not_congr
    apply exists_congr
    intro M
    exact ⟨fun h ↦ ⟨h.infinite,h.indecomposable,h.endofinite,h.splits⟩,fun ⟨a,b,c,d⟩ ↦ ⟨a,b,c,d⟩⟩


section Geometry

variable {K A : Type u} [Field K] [IsAlgClosed K] [Ring A] [Algebra K A] [Module.Finite K A]

private def chartOf (P : BasicPresentation K A) : Statement.Chart K A :=
  { A := P.Carrier, n := P.n, vertex := P.vertices.vertex, complete := P.vertices.complete,
    index := P.vertices.simpleIndex, dimension := P.vertices.simple_dimension, equivalence := P.equivalence }

private def verticesOf (C : Statement.Chart K A) :
    VertexRepresentation.SplitBasicVertices K C.A (ULift.{u} (Fin C.n)) :=
  ⟨C.vertex,C.complete,C.index,C.dimension⟩

private theorem chartKing (C : Statement.Chart K A) (h : IsEFinite Aᵐᵒᵖ) : C.KingCondition := by
  letI := IsNoetherianRing.of_finite K Aᵐᵒᵖ
  letI := IsArtinianRing.of_finite K Aᵐᵒᵖ
  letI := IsNoetherianRing.of_finite K C.A
  letI := IsArtinianRing.of_finite K C.A
  let P := verticesOf C
  have he := (isEFinite_iff_of_module_equivalence K K C.equivalence).1 h
  intro w d
  let g := ∑ i, w i • ProjectiveClass.of (P.vertexProjective i)
  have closed := P.atMostOneKingClosedPoint_of_isEFinite C.basis g (d := d) he
  unfold VertexRepresentation.SplitBasicVertices.atMostOneKingClosedPoint
    VertexRepresentation.SplitBasicVertices.kingModuli at closed
  rw [show P.characterExponents g = w from P.characterExponents_vertex_sum w] at closed
  exact closed

private theorem chartOpen (C : Statement.Chart K A) :
    (IsEFinite Aᵐᵒᵖ ↔ C.BrickOrbits) ∧ (IsEFinite Aᵐᵒᵖ ↔ C.WideLoci) := by
  letI := IsNoetherianRing.of_finite K C.A
  obtain ⟨hb,hw⟩ := isEFinite_iff_open_vertex_loci C.equivalence (verticesOf C) C.basis
  exact ⟨hb,hw.trans (forall_congr' fun d ↦ forall_congr' fun W ↦ imp_congr_left (wide_iff W).symm)⟩

/-- Over an algebraically closed field, all three geometric criteria are independent of the basic presentation. -/
theorem proveAlgebraicallyClosedField : Statement.AlgebraicallyClosedField.{u} := by
  intro k A _ _ _ _ _
  let P := basicPresentation k A
  let C := chartOf P
  letI := IsNoetherianRing.of_finite k P.Carrier
  refine ⟨⟨C⟩,eFinite_iff.trans ⟨fun h D ↦ chartKing D h, ?_⟩,
    eFinite_iff.trans ⟨fun h D ↦ (chartOpen D).1.mp h,fun h ↦ (chartOpen C).1.mpr (h C)⟩,
    eFinite_iff.trans ⟨fun h D ↦ (chartOpen D).2.mp h,fun h ↦ (chartOpen C).2.mpr (h C)⟩⟩
  intro h
  apply (isEFinite_iff_kingClosedPoints k A).2
  intro g d
  exact h C (P.vertices.characterExponents g) d

/-- **Corollary C (Weyman's conjecture):** Schur-representation-finiteness `(dim-brick)` is
equivalent over an algebraically closed field to multiplicity-freeness on every irreducible
component in every split basic Morita chart. -/
theorem proveBrickDiscreteMultiplicityFree : Statement.BrickDiscreteMultiplicityFree.{u} := by
  intro k A _ _ _ _ _
  letI := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  letI := IsArtinianRing.of_finite k Aᵐᵒᵖ
  refine (isEFinite_iff_finite_brickClassesOfClass (R := Aᵐᵒᵖ) k).symm.trans ⟨?_,?_⟩
  · intro h C d Z hZ w
    letI := IsNoetherianRing.of_finite k C.A
    letI := IsArtinianRing.of_finite k C.A
    have he := (isEFinite_iff_of_module_equivalence k k C.equivalence).1 h
    exact (verticesOf C).rank_componentWeightSpace_le_one_of_isEFinite C.basis he hZ w
  · intro h
    exact (isEFinite_iff_multiplicityFree k A).2 (h (chartOf (basicPresentation k A)))

end Geometry
end EFiniteCharacterizations
