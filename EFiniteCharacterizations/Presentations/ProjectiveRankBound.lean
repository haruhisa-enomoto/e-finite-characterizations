module

public import EFiniteCharacterizations.Modules.CompositionFactors
public import EFiniteCharacterizations.Modules.IndecomposableProjectives
public import EFiniteCharacterizations.Silting.Fans.RealProjectiveSpace
public import Mathlib.Data.Set.Card

/-! # Bounding projective rank by the number of simple modules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R]

private theorem projective_of_retract {X Y : FGModuleCat.{u} R} [Module.Projective R X]
    (a : Y ⟶ X) (b : X ⟶ Y) (h : a ≫ b = 𝟙 Y) : Module.Projective R Y :=
  Module.Projective.of_split a.hom.hom b.hom.hom (congrArg (fun f : Y ⟶ Y ↦ f.hom.hom) h)

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

theorem FGModuleCat.finrank_biprod (P Q : FGModuleCat.{u} R) :
    Module.finrank k ((P ⊞ Q : FGModuleCat.{u} R).obj : Type u) =
      Module.finrank k (P.obj : Type u) + Module.finrank k (Q.obj : Type u) := by
  have : Module.Finite R P := P.property
  have : Module.Finite R Q := Q.property
  have : Module.Finite k P := Module.Finite.trans R _
  have : Module.Finite k Q := Module.Finite.trans R _
  let e := (FGModuleCat.forgetBiprodIso P Q).trans (ModuleCat.biprodIsoProd P.obj Q.obj)
  exact (e.toLinearEquiv.restrictScalars k).finrank_eq.trans Module.finrank_prod

variable [IsNoetherianRing R]

include k in
/-- Every finite projective class is generated under addition by the classes
of indecomposable projectives. -/
theorem ProjectiveClass.of_induction_on (P : FiniteProjective R) {motive : ProjectiveClass R → Prop}
    (h0 : motive 0) (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hind : ∀ Q : FiniteProjective R, Indecomposable Q.val → motive (of Q)) : motive (of P) := by
  classical
  generalize hn : Module.finrank k (P.val.obj : Type u) = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hz : IsZero P.val
    · rw [of_eq_of_iso P (zeroProjective R) (hz.iso zeroProjective_isZero), of_zeroProjective]
      exact h0
    by_cases hi : Indecomposable P.val
    · exact hind P hi
    have hsplit : ¬ ∀ (Y Z : FGModuleCat.{u} R), (P.val ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z :=
      fun h ↦ hi ⟨hz, h⟩
    push Not at hsplit
    obtain ⟨Y, Z, i, hY, hZ⟩ := hsplit
    let _ := P.property
    let Y' : FiniteProjective R := ⟨Y, projective_of_retract (biprod.inl ≫ i.inv)
      (i.hom ≫ biprod.fst) (by simp)⟩
    let Z' : FiniteProjective R := ⟨Z, projective_of_retract (biprod.inr ≫ i.inv)
      (i.hom ≫ biprod.snd) (by simp)⟩
    have hdim := ((FGModuleCat.isoToLinearEquiv i).restrictScalars k).finrank_eq.trans (FGModuleCat.finrank_biprod k Y Z)
    change Module.finrank k (P.val.obj : Type u) =
      Module.finrank k (Y.obj : Type u) + Module.finrank k (Z.obj : Type u) at hdim
    rw [hn] at hdim
    have hy := dimensionWeight_pos k Y hY
    have hz' := dimensionWeight_pos k Z hZ
    rw [dimensionWeight_eval, Int.natCast_pos] at hy hz'
    have hsmallY : Module.finrank k (Y'.val.obj : Type u) < n := by change Module.finrank k (Y.obj : Type u) < n; omega
    have hsmallZ : Module.finrank k (Z'.val.obj : Type u) < n := by change Module.finrank k (Z.obj : Type u) < n; omega
    have hsum : of P = of Y' + of Z' := (of_eq_of_iso P (biprod Y' Z') i).trans (of_biprod Y' Z')
    rw [hsum]
    exact hadd _ _ (ih _ hsmallY Y' rfl) (ih _ hsmallZ Z' rfl)

/-- Isomorphism classes of indecomposable finite projectives. -/
def indecomposableProjectiveClasses (R : Type u) [Ring R] : Set (ProjectiveClass.IsoClasses R) :=
  {c | ∃ P : FiniteProjective R, ProjectiveClass.isoClass P = c ∧ Indecomposable P.val}

include k in
omit [IsNoetherianRing R] in
/-- The real projective space is finite dimensional and its dimension is at
most the number of simple modules. -/
theorem realProjectiveSpace_rank_bound : Module.Finite ℝ (RealProjectiveSpace R) ∧
    Module.finrank ℝ (RealProjectiveSpace R) ≤ (simpleIsomorphismClasses R).ncard := by
  classical
  have := IsNoetherianRing.of_finite k R
  have := IsArtinianRing.of_finite k R
  let I := indecomposableProjectiveClasses R
  let J := simpleIsomorphismClasses R
  choose P hP hp using fun c : I ↦ c.property
  choose S q hs hq using fun c : I ↦ FGModuleCat.exists_simple_quotient (hp c).1
  let f : I → J := fun c ↦ ⟨toSkeleton (S c), S c, rfl, hs c⟩
  have hf : Function.Injective f := by
    intro c d h
    let e : S c ≅ S d := Skeleton.isoOfEq (congrArg Subtype.val h)
    let _ := (P c).property
    let _ := (P d).property
    have := hq c
    have := hq d
    have := hs d
    obtain ⟨i⟩ := FGModuleCat.nonempty_iso_of_common_quotient (hp c) (hp d)
      (q c ≫ e.hom) (q d) (Simple.not_isZero (S d))
    apply Subtype.ext
    exact (hP c).symm.trans ((ProjectiveClass.isoClass_eq_iff.mpr ⟨i⟩).trans (hP d))
  have : Finite J := finite_simpleIsomorphismClasses k
  have : Finite I := Finite.of_injective f hf
  let _ : Fintype I := Fintype.ofFinite I
  let _ : Fintype J := Fintype.ofFinite J
  let g := realProjectiveClass R
  let v : I → RealProjectiveSpace R := fun c ↦ g (ProjectiveClass.of (P c))
  let W := Submodule.span ℝ (Set.range v)
  have hgen (Q : FiniteProjective R) : g (ProjectiveClass.of Q) ∈ W := by
    apply ProjectiveClass.of_induction_on k Q (motive := fun a ↦ g a ∈ W)
    · rw [map_zero]; exact W.zero_mem
    · intro x y hx hy
      rw [map_add]; exact W.add_mem hx hy
    · intro T hT
      let c : I := ⟨ProjectiveClass.isoClass T, T, rfl, hT⟩
      obtain ⟨e⟩ := ProjectiveClass.isoClass_eq_iff.mp (hP c : ProjectiveClass.isoClass (P c) = ProjectiveClass.isoClass T)
      rw [← ProjectiveClass.of_eq_of_iso (P c) T e]
      exact Submodule.subset_span ⟨c, rfl⟩
  have hspan : W = ⊤ := by
    apply top_unique
    rw [← span_realProjectiveClasses R]
    exact Submodule.span_le.2 (by rintro _ ⟨Q, rfl⟩; exact hgen Q)
  have hfin : Module.Finite ℝ W := Module.Finite.span_of_finite ℝ (Set.finite_range v)
  rw [hspan] at hfin
  refine ⟨Module.Finite.equiv (Submodule.topEquiv (R := ℝ) (M := RealProjectiveSpace R)), ?_⟩
  have hd := finrank_range_le_card (R := ℝ) v
  change Module.finrank ℝ W ≤ Fintype.card I at hd
  rw [hspan, finrank_top] at hd
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  exact hd.trans (Fintype.card_le_of_injective f hf)

include k in
omit [IsNoetherianRing R] in
/-- If the algebra has at most two simple modules, E-finiteness gives a
finite cover of its real projective space by compatible presilting pairs. -/
theorem exists_presilting_cover_of_simple_rank_le_two
    (hr : (simpleIsomorphismClasses R).ncard ≤ 2) (hR : IsEFinite R) :
    ∃ s : List (TwoTerm R × TwoTerm R),
      (∀ p ∈ s, (p.1.directSum p.2).IsPresilting) ∧
      ∀ v : RealProjectiveSpace R, ∃ p ∈ s,
        v ∈ sectorBetween (realProjectiveClass R p.1.projectiveClass) (realProjectiveClass R p.2.projectiveClass) := by
  obtain ⟨hfin, hd⟩ := realProjectiveSpace_rank_bound k (R := R)
  exact TwoTerm.exists_presilting_cover_of_projective_rank_le_two k (hd.trans hr) hR

end EFiniteCharacterizations
