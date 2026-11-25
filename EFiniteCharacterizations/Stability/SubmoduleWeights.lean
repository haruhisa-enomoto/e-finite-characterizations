module

public import EFiniteCharacterizations.Modules.FiniteModuleMorphisms
public import EFiniteCharacterizations.Stability.Weights
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-! # The modular identity for weights of submodules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.Weight

variable {R : Type u} [Ring R] [IsNoetherianRing R]

section Quotient

variable {X : Type u} [AddCommGroup X] [Module R X] [Module.Finite R X]

/-- A weight on finite modules is additive across a submodule and its quotient. -/
theorem eval_of_submodule_quotient (θ : Weight (FGModuleCat.{u} R)) (U : Submodule R X) :
    θ.eval (FGModuleCat.of R X) = θ.eval (FGModuleCat.of R U) + θ.eval (FGModuleCat.of R (X ⧸ U)) := by
  let i := FGModuleCat.ofHom U.subtype
  let p := FGModuleCat.ofHom U.mkQ
  have hz : i ≫ p = 0 := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change U.mkQ x.val = 0
    exact (Submodule.Quotient.mk_eq_zero U).2 x.property
  let S := ShortComplex.mk i p hz
  let F := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  have he : (S.map F).Exact := by
    apply ShortComplex.Exact.moduleCat_of_range_eq_ker
    change LinearMap.range U.subtype = LinearMap.ker U.mkQ
    rw [Submodule.range_subtype, Submodule.ker_mkQ]
  have hS : S.ShortExact := ShortComplex.ShortExact.mk' ((S.exact_map_iff_of_faithful F).mp he)
    ((FGModuleCat.mono_iff_injective i).2 Subtype.val_injective)
    ((FGModuleCat.epi_iff_surjective p).2 U.mkQ_surjective)
  exact θ.eval_shortExact S hS

/-- Weights satisfy the modular identity on the submodule lattice. -/
theorem eval_sup_add_eval_inf (θ : Weight (FGModuleCat.{u} R)) (U V : Submodule R X) :
    θ.eval (FGModuleCat.of R (U ⊔ V : Submodule R X)) +
      θ.eval (FGModuleCat.of R (U ⊓ V : Submodule R X)) =
      θ.eval (FGModuleCat.of R U) + θ.eval (FGModuleCat.of R V) := by
  let I := Submodule.comap U.subtype (U ⊓ V)
  let J := Submodule.comap (U ⊔ V).subtype V
  have hI := θ.eval_of_submodule_quotient I
  have hJ := θ.eval_of_submodule_quotient J
  have eI := Submodule.comapSubtypeEquivOfLe (show U ⊓ V ≤ U from inf_le_left)
  have eJ := Submodule.comapSubtypeEquivOfLe (show V ≤ U ⊔ V from le_sup_right)
  have hI' := θ.eval_eq_of_isIso eI.toFGModuleCatIso.hom
  have hJ' := θ.eval_eq_of_isIso eJ.toFGModuleCatIso.hom
  have hQ : θ.eval (FGModuleCat.of R (U ⧸ I)) = θ.eval (FGModuleCat.of R ((U ⊔ V : Submodule R X) ⧸ J)) := by
    let e := Submodule.quotEquivOfEq I _ (Submodule.comap_inf U V U.subtype)
    exact θ.eval_eq_of_isIso (e.trans (LinearMap.quotientInfEquivSupQuotient U V)).toFGModuleCatIso.hom
  change θ.eval (FGModuleCat.of R I) = θ.eval (FGModuleCat.of R (U ⊓ V : Submodule R X)) at hI'
  change θ.eval (FGModuleCat.of R J) = θ.eval (FGModuleCat.of R V) at hJ'
  rw [hI', hQ] at hI
  rw [hJ'] at hJ
  omega

/-- If the submodule weights take finitely many values then there is a
largest submodule of maximal weight. -/
theorem exists_largest_weight_maximizer (θ : Weight (FGModuleCat.{u} R))
    (hfin : (Set.range (fun U : Submodule R X ↦ θ.eval (FGModuleCat.of R U))).Finite) :
    ∃ U : Submodule R X, (∀ V : Submodule R X, θ.eval (FGModuleCat.of R V) ≤ θ.eval (FGModuleCat.of R U)) ∧
      ∀ V : Submodule R X, θ.eval (FGModuleCat.of R V) = θ.eval (FGModuleCat.of R U) → V ≤ U := by
  classical
  let w (V : Submodule R X) := θ.eval (FGModuleCat.of R V)
  have hne : hfin.toFinset.Nonempty := ⟨w ⊥, hfin.mem_toFinset.2 ⟨⊥, rfl⟩⟩
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image hfin.toFinset id hne
  have hmax' (V : Submodule R X) : w V ≤ m := hmax (w V) (hfin.mem_toFinset.2 ⟨V, rfl⟩)
  have hm' : ∃ V : Submodule R X, w V = m := hfin.mem_toFinset.1 hm
  have hwell : WellFounded (fun U V : Submodule R X ↦ V < U) := wellFounded_gt
  obtain ⟨U, hU, hmaxU⟩ := hwell.has_min {U : Submodule R X | w U = m} hm'
  change w U = m at hU
  refine ⟨U, fun V ↦ ?_, fun V hV ↦ ?_⟩
  · change w V ≤ w U
    rw [hU]
    exact hmax' V
  have heq : w (U ⊔ V) = m := by
    have hmod : w (U ⊔ V) + w (U ⊓ V) = w U + w V := θ.eval_sup_add_eval_inf U V
    change w V = w U at hV
    have := hmax' (U ⊔ V)
    have := hmax' (U ⊓ V)
    omega
  have hn : ¬ U < U ⊔ V := hmaxU (U ⊔ V) heq
  exact le_sup_right.trans (eq_of_le_of_not_lt le_sup_left hn).ge

end Quotient

end EFiniteCharacterizations.Weight
