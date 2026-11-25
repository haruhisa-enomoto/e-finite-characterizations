module

public import EFiniteCharacterizations.Modules.Endolength
public import EFiniteCharacterizations.ScalarExtension.FieldRestriction
public import EFiniteCharacterizations.Stability.StableHomBound

/-! # Endolength bounds for stable subobjects obtained by restriction -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.FieldExtension

noncomputable section

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R] [Module.Finite k F]

local notation "R₊" => ExtendedAlgebra k F R

/-- Postcomposition with the extension scalar action embeds the extension
field into any nonzero Hom space into a restricted module. -/
theorem finrank_le_homFinrank_restrictObj {S : FGModuleCat.{u} R} {N : FGModuleCat.{u} R₊}
    (f : S ⟶ restrictObj k F R N) (hf : f ≠ 0) :
    Module.finrank k F ≤ homFinrank k S (restrictObj k F R N) := by
  let X := restrictObj k F R N
  let v (a : F) : X ⟶ X :=
    ObjectProperty.homMk (ModuleCat.ofHom (X := X.obj) (Y := X.obj) (scalarActionMap k F R N a))
  let l : F →ₗ[k] (S ⟶ X) :=
    { toFun := fun a ↦ f ≫ v a
      map_add' := fun a b ↦ FGModuleCat.hom_ext (LinearMap.ext (fun x ↦ by
        let y : N := f.hom.hom x
        change (algebraMap F R₊ (a + b)) • y = algebraMap F R₊ a • y + algebraMap F R₊ b • y
        rw [map_add, add_smul]))
      map_smul' := fun a b ↦ FGModuleCat.hom_ext (LinearMap.ext (fun x ↦ by
        let y : N := f.hom.hom x
        change (algebraMap F R₊ (a • b)) • y =
          (algebraInclusion k F R (algebraMap k R a)) • (algebraMap F R₊ b • y)
        rw [Algebra.smul_def, map_mul, ← mul_smul, ← IsScalarTower.algebraMap_apply k F R₊,
          AlgHom.commutes])) }
  have hinj : Function.Injective l := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.2
    intro a ha
    by_contra hne
    have hm : Mono (v a) := by
      let _ := IsNoetherianRing.of_finite k R
      exact (FGModuleCat.mono_iff_injective (v a)).2 (scalarActionMap_injective k F R N hne)
    change f ≫ v a = 0 at ha
    exact hf (zero_of_comp_mono (v a) ha)
  rw [homFinrank_eq_finrank]
  let _ := finiteModuleHom_isFinite k S X
  exact LinearMap.finrank_le_finrank_of_injective hinj

variable [IsNoetherianRing R] [IsNoetherianRing (ExtendedAlgebra k F R)]

/-- An embedded stable ground module has endolength at most the extension
dimension of its semistable source of restriction. -/
theorem endolength_le_of_stable_hom_to_restrictObj (P : TwoTerm R) {S : FGModuleCat.{u} R}
    {N : FGModuleCat.{u} R₊} (hN : ((extendTwoTerm k F R P).eulerWeight F).IsSemistable N)
    (hS : (P.eulerWeight k).IsStable S) (f : S ⟶ restrictObj k F R N) (hf : f ≠ 0) :
    endolength k S ≤ Module.finrank F (N.obj : Type u) := by
  have hd := finrank_le_homFinrank_restrictObj k F R f hf
  have hs := homFinrank_mul_groundFinrank_le_of_isStable k hS _
    ((isSemistable_restrictObj_iff k F R P N).2 hN)
  have hmul := (Nat.mul_le_mul_right (Module.finrank k (S.obj : Type u)) hd).trans hs
  rw [finrank_restrictObj k F R N, Nat.mul_assoc] at hmul
  have h := Nat.le_of_mul_le_mul_left hmul (Module.finrank_pos (R := k) (M := F))
  apply Nat.div_le_of_le_mul
  exact h.trans_eq (Nat.mul_comm _ _)

/-- Stable extension modules produce ground stable witnesses with both
dimension and endolength bounds. -/
theorem exists_bounded_stable_subobject_restrictObj (P : TwoTerm R) (N : FGModuleCat.{u} R₊)
    (hN : ((extendTwoTerm k F R P).eulerWeight F).IsStable N) :
    ∃ (S : FGModuleCat.{u} R) (i : S ⟶ restrictObj k F R N),
      Mono i ∧ (P.eulerWeight k).IsStable S ∧
      Module.finrank k (S.obj : Type u) ≤ Module.finrank k F * Module.finrank F (N.obj : Type u) ∧
      endolength k S ≤ Module.finrank F (N.obj : Type u) := by
  obtain ⟨S, i, hm, hs, hd⟩ := exists_stable_subobject_restrictObj k F R P N hN
  have hi : i ≠ 0 := by
    intro hz
    apply hs.1
    apply (IsZero.iff_id_eq_zero S).2
    apply (cancel_mono i).1
    rw [Category.id_comp, hz, zero_comp]
  exact ⟨S, i, hm, hs, hd, endolength_le_of_stable_hom_to_restrictObj k F R P hN.isSemistable hs i hi⟩

end

end EFiniteCharacterizations.FieldExtension
