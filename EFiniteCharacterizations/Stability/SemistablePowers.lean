module

public import EFiniteCharacterizations.Modules.FiniteModuleMorphisms
public import EFiniteCharacterizations.Modules.ProjectiveBiproducts
public import EFiniteCharacterizations.Stability.SemistableExact

/-! # Finite powers at a semistable weight -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.Weight

variable {R : Type u} [Ring R] [IsNoetherianRing R] {θ : Weight (FGModuleCat.{u} R)}

/-- A finite power of a semistable module is semistable at the same weight. -/
theorem IsSemistable.finPower {M : FGModuleCat.{u} R} (h : θ.IsSemistable M) (n : ℕ) :
    θ.IsSemistable (FGModuleCat.of R (Fin n → M)) := by
  induction n with
  | zero =>
    let Z := FGModuleCat.of R (Fin 0 → M)
    have hZ : IsZero Z := (FGModuleCat.isZero_iff_subsingleton Z).2 (by
      change Subsingleton (Fin 0 → M)
      infer_instance)
    refine ⟨θ.eval_isZero hZ, ?_⟩
    intro U i _
    have hU : IsZero U := (IsZero.iff_id_eq_zero U).2
      ((cancel_mono i).1 (hZ.eq_of_tgt _ _))
    exact (θ.eval_isZero hU).le
  | succ n ih =>
    let N := FGModuleCat.of R (Fin n → M)
    let e : (M × (Fin n → M)) ≃ₗ[R] (Fin (n + 1) → M) :=
      { Fin.consEquiv (fun _ ↦ (M : Type u)) with
        map_add' := fun x y ↦ funext (fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i)
        map_smul' := fun a x ↦ funext (fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i) }
    let F := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
    let p : M ⊞ N ≅ FGModuleCat.of R (M × (Fin n → M)) :=
      F.preimageIso ((FGModuleCat.forgetBiprodIso M N).trans (ModuleCat.biprodIsoProd M.obj N.obj))
    exact (h.biprod ih).of_iso (p.trans e.toFGModuleCatIso)

end EFiniteCharacterizations.Weight
