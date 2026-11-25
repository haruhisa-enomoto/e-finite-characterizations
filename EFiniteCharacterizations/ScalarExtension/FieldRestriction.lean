module

public import EFiniteCharacterizations.Modules.CompositionFactors
public import EFiniteCharacterizations.ScalarExtension.FieldExtensionWeights
public import EFiniteCharacterizations.Stability.StableSubobjects
public import EFiniteCharacterizations.Stability.SubmoduleWeights

/-! # Semistability under restriction of a finite ground field extension -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

noncomputable section

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R] [Module.Finite k F]

local notation "R₊" => ExtendedAlgebra k F R

/-- The extension field acts by endomorphisms of the restricted module. -/
def scalarActionMap (N : FGModuleCat.{u} R₊) (c : F) :
    Module.End R (restrictObj k F R N) where
  toFun x := (algebraMap F R₊ c) • (show N from x)
  map_add' x y := smul_add (algebraMap F R₊ c) (show N from x) (show N from y)
  map_smul' r x := by
    change algebraMap F R₊ c • (algebraInclusion k F R r • (show N from x)) =
      algebraInclusion k F R r • (algebraMap F R₊ c • (show N from x))
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

theorem scalarActionMap_injective (N : FGModuleCat.{u} R₊) {c : F} (hc : c ≠ 0) :
    Function.Injective (scalarActionMap k F R N c) := by
  intro x y h
  exact (smul_right_injective (M := (N.obj : Type u)) hc) h

/-- A submodule of the restriction that is invariant under the extension
field is a submodule over the extended algebra. -/
def ofInvariantSubmodule (N : FGModuleCat.{u} R₊) (U : Submodule R (restrictObj k F R N))
    (hU : ∀ c : F, ∀ x ∈ U, scalarActionMap k F R N c x ∈ U) : Submodule R₊ N where
  carrier := fun x ↦ (show restrictObj k F R N from x) ∈ U
  zero_mem' := U.zero_mem
  add_mem' := U.add_mem
  smul_mem' a x hx := by
    refine TensorProduct.inductionOn a ?_ ?_
    · intro c r
      have h := hU c (r • (show restrictObj k F R N from x)) (U.smul_mem r hx)
      have he :
          scalarActionMap k F R N c (r • (show restrictObj k F R N from x)) =
            (c ⊗ₜ[k] r : R₊) • x := by
        change algebraMap F R₊ c • (algebraInclusion k F R r • x) = _
        rw [← mul_smul]
        simp [algebraInclusion, Algebra.TensorProduct.tmul_mul_tmul]
      exact he ▸ h
    · intro a b ha hb
      rw [add_smul]
      exact U.add_mem ha hb

variable [IsNoetherianRing R] [IsNoetherianRing (ExtendedAlgebra k F R)]

omit [IsNoetherianRing (ExtendedAlgebra k F R)] in
theorem eval_eq_of_invariantSubmodule (N : FGModuleCat.{u} R₊)
    (U : Submodule R (restrictObj k F R N))
    (hU : ∀ c : F, ∀ x ∈ U, scalarActionMap k F R N c x ∈ U)
    [Module.Finite R₊ (ofInvariantSubmodule k F R N U hU)] (θ : Weight (FGModuleCat.{u} R)) :
    θ.eval (FGModuleCat.of R U) =
      θ.eval (restrictObj k F R (FGModuleCat.of R₊ (ofInvariantSubmodule k F R N U hU))) := by
  let V := FGModuleCat.of R₊ (ofInvariantSubmodule k F R N U hU)
  let e : U ≃ₗ[R] (restrictObj k F R V : Type u) :=
    { Equiv.refl _ with
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact θ.eval_eq_of_isIso e.toFGModuleCatIso.hom

/-- A semistable module over a finite-degree field extension remains semistable
at the original projective weight upon restriction. -/
theorem isSemistable_restrictObj_of_isSemistable (P : TwoTerm R) (N : FGModuleCat.{u} R₊)
    (hN : ((extendTwoTerm k F R P).eulerWeight F).IsSemistable N) :
    (P.eulerWeight k).IsSemistable (restrictObj k F R N) := by
  let X := restrictObj k F R N
  let θ := P.eulerWeight k
  have hz : θ.eval X = 0 := by
    change (P.eulerWeight k).eval (restrictObj k F R N) = 0
    rw [eulerWeight_eval_restrictObj k F R P N, hN.1, mul_zero]
  refine ⟨hz, ?_⟩
  have : Module.Finite k (X.obj : Type u) := Module.Finite.trans R (X.obj : Type u)
  have hfin : (Set.range (fun U : Submodule R X ↦ θ.eval (FGModuleCat.of R U))).Finite := by
    refine ((finite_classes_of_groundFinrank_le (R := R) k (Module.finrank k (X.obj : Type u))).image θ).subset ?_
    rintro z ⟨U, rfl⟩
    refine ⟨GrothendieckGroup.of (FGModuleCat.of R U), ⟨FGModuleCat.of R U, ?_, rfl⟩, rfl⟩
    exact LinearMap.finrank_le_finrank_of_injective (f := U.subtype.restrictScalars k) Subtype.val_injective
  obtain ⟨U, hmax, hlarge⟩ := θ.exists_largest_weight_maximizer hfin
  have hU (c : F) (x : X) (hx : x ∈ U) : scalarActionMap k F R N c x ∈ U := by
    by_cases hc : c = 0
    · subst c
      change algebraMap F R₊ 0 • (show N from x) ∈ U
      rw [map_zero, zero_smul]
      exact U.zero_mem
    · let f := scalarActionMap k F R N c
      let e := Submodule.equivMapOfInjective f (scalarActionMap_injective k F R N hc) U
      have hle : U.map f ≤ U := hlarge _ (θ.eval_eq_of_isIso e.toFGModuleCatIso.hom).symm
      exact hle ⟨x, hx, rfl⟩
  let V := ofInvariantSubmodule k F R N U hU
  let W := FGModuleCat.of R₊ V
  let i : W ⟶ N := ObjectProperty.homMk (ModuleCat.ofHom (Y := N.obj) V.subtype)
  have : Mono i := (FGModuleCat.mono_iff_injective i).2 Subtype.val_injective
  have hnon : θ.eval (FGModuleCat.of R U) ≤ 0 := by
    have he := eval_eq_of_invariantSubmodule k F R N U hU θ
    change θ.eval (FGModuleCat.of R U) = (P.eulerWeight k).eval (restrictObj k F R W) at he
    rw [he, eulerWeight_eval_restrictObj k F R P W]
    exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (hN.2 i)
  intro A a _
  let V' := LinearMap.range a.hom.hom
  let e := LinearEquiv.ofInjective a.hom.hom ((FGModuleCat.mono_iff_injective a).1 inferInstance)
  have he : θ.eval A = θ.eval (FGModuleCat.of R V') := θ.eval_eq_of_isIso e.toFGModuleCatIso.hom
  rw [he]
  exact (hmax V').trans hnon

/-- Semistability for an extended Euler weight is equivalent to semistability
for the original Euler weight after restriction. -/
theorem isSemistable_restrictObj_iff (P : TwoTerm R) (N : FGModuleCat.{u} R₊) :
    (P.eulerWeight k).IsSemistable (restrictObj k F R N) ↔
      ((extendTwoTerm k F R P).eulerWeight F).IsSemistable N := by
  refine ⟨?_, isSemistable_restrictObj_of_isSemistable k F R P N⟩
  intro h
  have hd : 0 < (Module.finrank k F : ℤ) := Int.natCast_pos.mpr Module.finrank_pos
  have hz := h.1
  rw [eulerWeight_eval_restrictObj k F R P N] at hz
  refine ⟨(mul_eq_zero.mp hz).resolve_left hd.ne', ?_⟩
  intro U i _
  let j : restrictObj k F R U ⟶ restrictObj k F R N := (restrict k F R).map i
  have : Mono j :=
    (FGModuleCat.mono_iff_injective j).2 ((FGModuleCat.mono_iff_injective i).1 inferInstance)
  have hn := h.2 j
  rw [eulerWeight_eval_restrictObj k F R P U] at hn
  by_contra! hp
  exact (not_lt_of_ge hn) (mul_pos hd hp)

/-- A stable module at an extended Euler weight supplies a stable subobject
at the original weight, with a dimension bound after restriction. -/
theorem exists_stable_subobject_restrictObj (P : TwoTerm R) (N : FGModuleCat.{u} R₊)
    (hN : ((extendTwoTerm k F R P).eulerWeight F).IsStable N) :
    ∃ (S : FGModuleCat.{u} R) (i : S ⟶ restrictObj k F R N),
      Mono i ∧ (P.eulerWeight k).IsStable S ∧
      Module.finrank k (S.obj : Type u) ≤ Module.finrank k F * Module.finrank F (N.obj : Type u) := by
  let X := restrictObj k F R N
  have hX := (isSemistable_restrictObj_iff k F R P N).2 hN.isSemistable
  have hnon : ¬ IsZero X := fun h ↦ hN.1 ((FGModuleCat.isZero_iff_subsingleton N).2
    ((FGModuleCat.isZero_iff_subsingleton X).1 h))
  obtain ⟨S, i, hi, hs⟩ := hX.exists_stable_subobject k hnon
  have : Module.Finite k (X.obj : Type u) := Module.Finite.trans R (X.obj : Type u)
  have hdim : Module.finrank k (S.obj : Type u) ≤ Module.finrank k (X.obj : Type u) :=
    LinearMap.finrank_le_finrank_of_injective (f := i.hom.hom.restrictScalars k)
      ((FGModuleCat.mono_iff_injective i).1 hi)
  exact ⟨S, i, hi, hs, hdim.trans_eq (finrank_restrictObj k F R N)⟩

end

end EFiniteCharacterizations.FieldExtension
