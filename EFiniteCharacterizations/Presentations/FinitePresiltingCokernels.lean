module

public import EFiniteCharacterizations.Presentations.CokernelGenerators
public import Mathlib.RingTheory.LocalRing.Basic

/-! # Finiteness of indecomposable presilting cokernels in rank at most two -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

namespace FGModuleCat

variable {R : Type u} [Ring R]

private def endToLinear (X : FGModuleCat.{u} R) : End X →+* Module.End R X where
  toFun f := f.hom.hom
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private theorem endToLinear_injective (X : FGModuleCat.{u} R) :
    Function.Injective (endToLinear X) :=
  fun _ _ h ↦ FGModuleCat.hom_ext h

variable [IsNoetherianRing R] [IsArtinianRing R]

theorem isLocalRing_end_of_indecomposable {X : FGModuleCat.{u} R} (hX : Indecomposable X) :
    IsLocalRing (End X) := by
  have : Nontrivial (End X) := nontrivial_of_ne 0 1 (fun h ↦ hX.1 ((IsZero.iff_id_eq_zero X).2 h.symm))
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  rcases fitting_nilpotent_or_isIso hX f with ⟨n, hn⟩ | hf
  · refine Or.inr (IsNilpotent.isUnit_one_sub ⟨n, endToLinear_injective X ?_⟩)
    rw [map_pow, map_zero]
    exact hn
  · exact Or.inl ((isUnit_iff_isIso f).2 hf)

private theorem list_exists_isUnit_of_isUnit_sum {S : Type*} [Ring S] [IsLocalRing S] (l : List S)
    (h : IsUnit l.sum) : ∃ a ∈ l, IsUnit a := by
  induction l with
  | nil => exact (not_isUnit_zero h).elim
  | cons a l ih =>
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with ha | hl
    · exact ⟨a, List.mem_cons_self, ha⟩
    · obtain ⟨b, hb, hu⟩ := ih hl
      exact ⟨b, List.mem_cons_of_mem _ hb, hu⟩

theorem exists_retraction_of_isInAdd {X Y : FGModuleCat.{u} R} (hX : Indecomposable X)
    (h : IsInAdd X Y) : ∃ (a : X ⟶ Y) (b : Y ⟶ X), a ≫ b = 𝟙 X := by
  obtain ⟨l, hl⟩ := h
  let _ := isLocalRing_end_of_indecomposable hX
  let s : List (End X) := l.map (fun p ↦ p.1 ≫ p.2)
  have hs : IsUnit s.sum := by
    have he : s.sum = 1 := hl
    rw [he]
    exact isUnit_one
  obtain ⟨d, hd, hu⟩ := list_exists_isUnit_of_isUnit_sum s hs
  obtain ⟨⟨a, b⟩, _, rfl⟩ := List.mem_map.mp hd
  have : IsIso (a ≫ b) := (isUnit_iff_isIso _).mp hu
  exact ⟨inv (a ≫ b) ≫ a, b, by simp⟩

private theorem nonempty_iso_of_retraction {X Y : FGModuleCat.{u} R} (hX : ¬ IsZero X)
    (hY : Indecomposable Y) (a : X ⟶ Y) (b : Y ⟶ X) (h : a ≫ b = 𝟙 X) :
    Nonempty (X ≅ Y) := by
  have hb : b ≠ 0 := fun hb ↦ hX ((IsZero.iff_id_eq_zero X).2 (by simpa [hb] using h.symm))
  have he : IsIso (b ≫ a) := isIso_of_quotient_eq_self hY b hb _ (by rw [Category.assoc, h, Category.comp_id])
  have hba : b ≫ a = 𝟙 Y := (cancel_mono (b ≫ a)).mp (calc
    (b ≫ a) ≫ (b ≫ a) = b ≫ ((a ≫ b) ≫ a) := by simp only [Category.assoc]
    _ = 𝟙 Y ≫ (b ≫ a) := by simp [h])
  exact ⟨⟨a, b, h, hba⟩⟩

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
/-- The indecomposable objects in the additive closure of a finite module
have finitely many isomorphism classes. -/
theorem exists_list_indecomposable_isInAdd (Y : FGModuleCat.{u} R) :
    ∃ s : List (FGModuleCat.{u} R), ∀ X : FGModuleCat.{u} R, Indecomposable X → IsInAdd X Y →
      ∃ D ∈ s, Nonempty (X ≅ D) := by
  classical
  generalize hn : Module.finrank k (Y.obj : Type u) = n
  induction n using Nat.strong_induction_on generalizing Y with
  | h n ih =>
    by_cases hz : IsZero Y
    · refine ⟨[], fun X hX hAdd ↦ ?_⟩
      obtain ⟨a, b, h⟩ := exists_retraction_of_isInAdd hX hAdd
      exact (hX.1 ((IsZero.iff_id_eq_zero X).2
        (by simpa [hz.eq_of_tgt a 0] using h.symm))).elim
    by_cases hY : Indecomposable Y
    · refine ⟨[Y], fun X hX hAdd ↦ ⟨Y, List.mem_cons_self, ?_⟩⟩
      obtain ⟨a, b, h⟩ := exists_retraction_of_isInAdd hX hAdd
      exact nonempty_iso_of_retraction hX.1 hY a b h
    have hsplit : ¬ ∀ (U V : FGModuleCat.{u} R), (Y ≅ U ⊞ V) → IsZero U ∨ IsZero V :=
      fun h ↦ hY ⟨hz, h⟩
    push Not at hsplit
    obtain ⟨U, V, e, hU, hV⟩ := hsplit
    have hd := ((FGModuleCat.isoToLinearEquiv e).restrictScalars k).finrank_eq.trans
      (FGModuleCat.finrank_biprod k U V)
    change Module.finrank k (Y.obj : Type u) =
      Module.finrank k (U.obj : Type u) + Module.finrank k (V.obj : Type u) at hd
    rw [hn] at hd
    have hu := dimensionWeight_pos k U hU
    have hv := dimensionWeight_pos k V hV
    rw [dimensionWeight_eval, Int.natCast_pos] at hu hv
    obtain ⟨s, hs⟩ := ih _ (by omega) U rfl
    obtain ⟨t, ht⟩ := ih _ (by omega) V rfl
    refine ⟨s ++ t, fun X hX hAdd ↦ ?_⟩
    obtain ⟨a, b, hab⟩ := exists_retraction_of_isInAdd hX hAdd
    let p : X ⟶ U := a ≫ e.hom ≫ biprod.fst
    let q : X ⟶ V := a ≫ e.hom ≫ biprod.snd
    let i : U ⟶ X := biprod.inl ≫ e.inv ≫ b
    let j : V ⟶ X := biprod.inr ≫ e.inv ≫ b
    have hsum : p ≫ i + q ≫ j = 𝟙 X := by
      have htotal := congrArg (fun f : U ⊞ V ⟶ U ⊞ V ↦ a ≫ e.hom ≫ f ≫ e.inv ≫ b)
        (biprod.total (X := U) (Y := V))
      simpa only [p, q, i, j, Preadditive.comp_add, Preadditive.add_comp, Category.assoc, Category.id_comp,
        Iso.hom_inv_id_assoc, hab] using htotal
    let _ := isLocalRing_end_of_indecomposable hX
    have hunit : IsUnit (End.of (p ≫ i) + End.of (q ≫ j)) := by
      have he : End.of (p ≫ i) + End.of (q ≫ j) = 1 := hsum
      rw [he]
      exact isUnit_one
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hunit with hp | hq
    · have : IsIso (p ≫ i) := (isUnit_iff_isIso _).mp hp
      obtain ⟨D, hD, hXD⟩ := hs X hX (IsInAdd.of_retraction (inv (p ≫ i) ≫ p) i (by simp))
      exact ⟨D, List.mem_append_left _ hD, hXD⟩
    · have : IsIso (q ≫ j) := (isUnit_iff_isIso _).mp hq
      obtain ⟨D, hD, hXD⟩ := ht X hX (IsInAdd.of_retraction (inv (q ≫ j) ≫ q) j (by simp))
      exact ⟨D, List.mem_append_right _ hD, hXD⟩

end FGModuleCat

namespace TwoTerm

variable {R : Type u} [Ring R]

/-- Isomorphism classes of indecomposable cokernels of presilting differentials. -/
def indecomposablePresiltingCokernelClasses [IsNoetherianRing R] : Set (Skeleton (FGModuleCat.{u} R)) :=
  {c | ∃ P : TwoTerm R, P.IsPresilting ∧ Indecomposable (cokernel P.differential) ∧
    toSkeleton (cokernel P.differential) = c}

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
theorem finite_indecomposablePresiltingCokernelClasses_of_rank_le_two
    (hr : (simpleIsomorphismClasses R).ncard ≤ 2) (hR : IsEFinite R) :
    letI := IsNoetherianRing.of_finite k R
    (indecomposablePresiltingCokernelClasses (R := R)).Finite := by
  let _ := IsNoetherianRing.of_finite k R
  let _ := IsArtinianRing.of_finite k R
  classical
  obtain ⟨l, hl⟩ := exists_finite_cokernel_generators_of_rank_le_two k hr hR
  choose s hs using FGModuleCat.exists_list_indecomposable_isInAdd (R := R) k
  let t := (l.flatMap s).map toSkeleton
  apply t.toFinset.finite_toSet.subset
  rintro c ⟨P, hP, hInd, rfl⟩
  obtain ⟨M, hM, hAdd⟩ := hl P hP
  obtain ⟨D, hD, hIso⟩ := hs M _ hInd hAdd
  have he := toSkeleton_eq_toSkeleton_iff.mpr hIso
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨D, List.mem_flatMap.mpr ⟨M, hM, hD⟩, he.symm⟩

end TwoTerm

end EFiniteCharacterizations
