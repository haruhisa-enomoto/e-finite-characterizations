module

public import EFiniteCharacterizations.Silting.ThickSubcategories.ThickPencil
public import EFiniteCharacterizations.Presentations.CokernelGenerators
public import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Bongartz completion in the two-term homotopy category -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations.TwoTerm

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [Ring R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
private theorem unit_zero : IsZero (FGModuleCat.of R PUnit.{u+1}) :=
  (FGModuleCat.isZero_iff_subsingleton _).2 (inferInstanceAs (Subsingleton PUnit))

private noncomputable def termSequence (P : TwoTerm R) :
    ShortComplex (Arrow (FGModuleCat.{u} R)) :=
  ShortComplex.mk
    (Arrow.homMk (f := Arrow.mk (0 : FGModuleCat.of R PUnit ⟶ P.target)) (g := P.asArrow)
      0 (𝟙 _) (by simp [asArrow]))
    (Arrow.homMk (g := Arrow.mk (0 : P.source ⟶ FGModuleCat.of R PUnit)) (𝟙 _) 0 (by simp [asArrow]))
    (by apply Arrow.hom_ext <;> simp)

/-- The triangle of a two-term complex and its two individual terms. -/
theorem exists_terms_triangle (P : TwoTerm R) :
    letI := P.projective_target
    letI := P.projective_source
    ∃ (a : (inDegreeZero P.target).homotopyObject ⟶ P.homotopyObject)
      (b : P.homotopyObject ⟶ (inDegreeMinusOne ⟨P.source, P.projective_source⟩).homotopyObject)
      (δ : (inDegreeMinusOne ⟨P.source, P.projective_source⟩).homotopyObject ⟶ (inDegreeZero P.target).homotopyObject⟦(1 : ℤ)⟧),
      Triangle.mk a b δ ∈ distTriang _ := by
  let S := termSequence P
  have σ₁ : (S.map Arrow.leftFunc).Splitting :=
    ⟨0, 𝟙 _, unit_zero.eq_of_src _ _, Category.id_comp _, by change 0 ≫ 0 + 𝟙 _ ≫ 𝟙 _ = _; simp⟩
  have σ₀ : (S.map Arrow.rightFunc).Splitting :=
    ⟨𝟙 _, 0, Category.id_comp _, unit_zero.eq_of_src _ _, by change 𝟙 _ ≫ 𝟙 _ + 0 ≫ 0 = _; simp⟩
  exact ⟨_, _, _, CochainComplex.trianglehOfDegreewiseSplit_distinguished _
    (doubleSplitting S σ₁ σ₀)⟩

noncomputable def inDegreeMinusOneIso (G : FGModuleCat.{u} R) [Module.Projective R G] :
    (inDegreeMinusOne ⟨G, inferInstance⟩).homotopyObject ≅ (inDegreeZero G).homotopyObject⟦(1 : ℤ)⟧ := by
  apply Classical.choice
  let S : FiniteProjective R := ⟨G, inferInstance⟩
  obtain ⟨a,b,δ,ht⟩ := exists_terms_triangle (contractible S)
  let T := Triangle.mk a b δ
  have : IsIso δ := (Triangle.isZero₂_iff_isIso₃ T ht).1 (isZero_contractible S)
  exact ⟨asIso δ⟩

/-- If a thick closure contains both terms as degree-zero stalks, it contains
the complex of any differential between those terms. -/
theorem inThick_of_terms (U X : TwoTerm R)
    (hs : letI := X.projective_source; InThick U (inDegreeZero X.source))
    (ht : letI := X.projective_target; InThick U (inDegreeZero X.target)) : InThick U X := by
  have := X.projective_source
  have := X.projective_target
  let D := (ObjectProperty.singleton U.homotopyObject).triangEnvelope
  obtain ⟨a,b,δ,hT⟩ := exists_terms_triangle X
  have hm : D (inDegreeMinusOne ⟨X.source, X.projective_source⟩).homotopyObject :=
    D.prop_of_iso (inDegreeMinusOneIso X.source).symm (D.le_shift (1 : ℤ) _ hs)
  exact D.ext_of_isTriangulatedClosed₂ (Triangle.mk a b δ) hT ht hm

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

omit [IsNoetherianRing R] in
private theorem rightExtensions_orthogonal {U X B : TwoTerm R} (hb : RightExtensions U X B)
    (Y : TwoTerm R) (hU : U.shiftedHomFinrank k Y = 0) (hX : X.shiftedHomFinrank k Y = 0) :
    B.shiftedHomFinrank k Y = 0 := by
  have (A D : FGModuleCat.{u} R) : Module.Finite k (A ⟶ D) := finiteModuleHom_isFinite k A D
  induction hb with
  | start => exact hX
  | next h w ih =>
    have h := LinearMap.finrank_le_finrank_of_surjective
      (blockCokernelProjection_surjective k _ U.differential w Y.differential
        ((shiftedHomFinrank_eq_zero_iff k _ Y).1 ih))
    exact Nat.eq_zero_of_le_zero (h.trans hU.le)

omit [IsNoetherianRing R] in
private theorem stalk_orthogonal (G : FGModuleCat.{u} R) [Module.Projective R G] (Y : TwoTerm R) :
    (inDegreeZero G).shiftedHomFinrank k Y = 0 := by
  apply (shiftedHomFinrank_eq_zero_iff k _ Y).2
  intro f
  exact ⟨0, unit_zero.eq_of_src _ _⟩

include k in
/-- Completing U at a finite projective G gives a presilting complex containing U,
generating the stalk of G, and preserving every right orthogonality of U. -/
theorem exists_bongartz_inThick (U : TwoTerm R) (hu : U.IsPresilting)
    (G : FGModuleCat.{u} R) [Module.Projective R G] :
    ∃ B : TwoTerm R, let T := U.directSum B
      T.IsPresilting ∧ InThick T (inDegreeZero G) ∧
        ∀ Y : TwoTerm R, Function.Surjective (homotopyBoundary U Y) →
          Function.Surjective (homotopyBoundary T Y) := by
  obtain ⟨B, hUB, hb⟩ := exists_right_orthogonal k U hu _ (inDegreeZero G) rfl
  let T := U.directSum B
  have hB (Y : TwoTerm R) (hY : U.shiftedHomFinrank k Y = 0) :=
    rightExtensions_orthogonal k hb Y hY (stalk_orthogonal k G Y)
  have hBU := hB U ((shiftedHomFinrank_eq_zero_iff k U U).2 hu)
  have hBB := (shiftedHomFinrank_eq_zero_iff k B B).1 (hB B hUB)
  let F := doubleFunctor (C := FGModuleCat.{u} R) ⋙ HomotopyCategory.quotient _ _
  have hUT : InThick T U := inThick_of_isInAdd _ _ (IsInAdd.of_retraction _ _
    ((show Retract U.asArrow T.asArrow from ⟨_, _, inlDirectSum_fstDirectSum U B⟩).map F).retract)
  have hBT : InThick T B := inThick_of_isInAdd _ _ (IsInAdd.of_retraction _ _
    ((show Retract B.asArrow T.asArrow from ⟨_, _, inrDirectSum_sndDirectSum U B⟩).map F).retract)
  refine ⟨B, (isPresilting_directSum_iff k U B).2 ⟨hu, hBB, hUB, hBU⟩,
    (hb.sameMembership.iff_of_twoOutOfThree (twoOutOfThree_inThick T) hUT).2 hBT, ?_⟩
  intro Y hY
  have hz := (shiftedHomFinrank_eq_zero_iff k U Y).2 hY
  apply (shiftedHomFinrank_eq_zero_iff k T Y).1
  rw [shiftedHomFinrank_directSum_source, hz, hB Y hz, add_zero]


private def stalkArrow : FGModuleCat.{u} R ⥤ Arrow (FGModuleCat.{u} R) where
  obj X := Arrow.mk (0 : FGModuleCat.of R PUnit ⟶ X)
  map f := Arrow.homMk 0 f (by simp)
  map_id _ := Arrow.hom_ext _ _ (unit_zero.eq_of_src _ _) rfl
  map_comp _ _ := Arrow.hom_ext _ _ (unit_zero.eq_of_src _ _) rfl

private instance : (stalkArrow (R := R)).Additive where
  map_add := by intro X Y f g; exact Arrow.hom_ext _ _ (unit_zero.eq_of_src _ _) rfl

omit [IsNoetherianRing R] [Module.Finite k R] in
include k in
private theorem isInAdd_regular (P : FGModuleCat.{u} R) [Module.Projective R P] :
    IsInAdd P (FGModuleCat.of R R) := by
  obtain ⟨n,f,hf⟩ := Module.Finite.exists_fin' R P
  obtain ⟨g,hg⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  let a (i : Fin n) : P ⟶ FGModuleCat.of R R := FGModuleCat.ofHom ((LinearMap.proj i).comp g)
  let b (i : Fin n) : FGModuleCat.of R R ⟶ P := FGModuleCat.ofHom (f.comp (LinearMap.single R (fun _ : Fin n ↦ R) i))
  refine ⟨List.ofFn (fun i ↦ (a i,b i)), ?_⟩
  rw [List.map_ofFn, Fin.sum_ofFn]
  apply (finiteModuleHomLinearEquiv k P P).injective
  rw [map_sum]
  ext x
  rw [LinearMap.sum_apply]
  change (∑ i : Fin n, f (Pi.single i (g x i))) = x
  rw [← map_sum]
  have eq : ∑ i : Fin n, Pi.single i (g x i) = g x := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [eq]
  exact DFunLike.congr_fun hg x

include k in
/-- A finite projective stalk belongs to the thick closure of any two-term
complex that generates the regular stalk. -/
theorem inThick_stalk (T : TwoTerm R) (hr : InThick T (inDegreeZero (FGModuleCat.of R R)))
    (P : FGModuleCat.{u} R) [Module.Projective R P] : InThick T (inDegreeZero P) := by
  let G := stalkArrow (R := R) ⋙ doubleFunctor ⋙ HomotopyCategory.quotient _ _
  have hx := inThick_of_isInAdd (inDegreeZero (FGModuleCat.of R R)) (inDegreeZero P)
    ((isInAdd_regular k P).map G)
  unfold InThick at hr hx ⊢
  exact (ObjectProperty.triangEnvelope_le_iff _ (Q := (ObjectProperty.singleton T.homotopyObject).triangEnvelope)).2
    (ObjectProperty.singleton_le_iff.2 hr) _ hx

include k in
/-- The Bongartz completion is a silting generator on two-term projectives
and preserves the positive right orthogonality of the original complex. -/
theorem exists_bongartz_generator (U : TwoTerm R) (hu : U.IsPresilting) :
    ∃ B : TwoTerm R, let T := U.directSum B
      T.IsPresilting ∧ (∀ X : TwoTerm R, InThick T X) ∧
      ∀ Y : TwoTerm R, Function.Surjective (homotopyBoundary U Y) →
        Function.Surjective (homotopyBoundary T Y) := by
  obtain ⟨B,hT,hr,horth⟩ := exists_bongartz_inThick k U hu (FGModuleCat.of R R)
  refine ⟨B,hT,?_,horth⟩
  intro X
  have := X.projective_source
  have := X.projective_target
  exact inThick_of_terms _ X (inThick_stalk k _ hr _) (inThick_stalk k _ hr _)

end EFiniteCharacterizations.TwoTerm
