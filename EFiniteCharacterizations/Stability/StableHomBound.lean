module

public import EFiniteCharacterizations.Presentations.ProjectiveHomWeight
public import EFiniteCharacterizations.Stability.SemistableExact

/-! # A dimension bound on Hom from a stable module -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

include k in
/-- The left exact Hom sequence gives a bound on the dimension of its middle space. -/
theorem homFinrank_le_add_of_mono {S X M : FGModuleCat.{u} R}
    (i : X ⟶ M) [Mono i] :
    homFinrank k S M ≤ homFinrank k S X + homFinrank k S (cokernel i) := by
  have := finiteModuleHom_isFinite k S M
  have := finiteModuleHom_isFinite k S (cokernel i)
  let a := Linear.rightComp k S i
  let b := Linear.rightComp k S (cokernel.π i)
  have ha : Function.Injective a := fun _ _ h ↦ (cancel_mono i).1 h
  have hker : LinearMap.ker b = LinearMap.range a := by
    ext f
    constructor
    · intro hf
      have hf' : f ≫ cokernel.π i = 0 := hf
      exact ⟨Abelian.monoLift i f hf', Abelian.monoLift_comp i f hf'⟩
    · rintro ⟨g, rfl⟩
      change (g ≫ i) ≫ cokernel.π i = 0
      rw [Category.assoc, cokernel.condition, comp_zero]
  have hr := b.finrank_range_add_finrank_ker
  rw [hker, LinearMap.finrank_range_of_inj ha, add_comm] at hr
  rw [homFinrank_eq_finrank, homFinrank_eq_finrank, homFinrank_eq_finrank, ← hr]
  exact Nat.add_le_add_left (Submodule.finrank_le _) _

include k in
/-- For a stable source and a semistable target at the same weight, copies
of the source detected by Hom account for at most the target's dimension. -/
theorem homFinrank_mul_groundFinrank_le_of_isStable
    {θ : Weight (FGModuleCat.{u} R)} {S : FGModuleCat.{u} R} (hS : θ.IsStable S)
    (M : FGModuleCat.{u} R) (hM : θ.IsSemistable M) :
    homFinrank k S M * Module.finrank k (S.obj : Type u) ≤
      Module.finrank k (M.obj : Type u) * homFinrank k S S := by
  classical
  generalize hm : Module.finrank k (M.obj : Type u) = d
  induction d using Nat.strong_induction_on generalizing M with
  | h d ih =>
    by_cases hnon : ∃ i : S ⟶ M, i ≠ 0
    · obtain ⟨i, hi⟩ := hnon
      let _ := Weight.mono_of_isStable_of_isSemistable hS hM i hi
      let Q := cokernel i
      have hQ := hS.isSemistable.cokernel_of_mono hM i
      let T := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
      have hT : T.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i)
        (by dsimp [T]; infer_instance) (by dsimp [T]; infer_instance)
      have hd := (dimensionWeight (R := R) k).eval_shortExact T hT
      change (dimensionWeight (R := R) k).eval M =
        (dimensionWeight (R := R) k).eval S + (dimensionWeight (R := R) k).eval Q at hd
      simp only [dimensionWeight_eval] at hd
      have hd' : d = Module.finrank k (S.obj : Type u) + Module.finrank k (Q.obj : Type u) := by
        exact_mod_cast hm.symm.trans (Int.ofNat_inj.mp (by simpa only [Nat.cast_add] using hd))
      have hpos := dimensionWeight_pos k S hS.1
      rw [dimensionWeight_eval, Int.natCast_pos] at hpos
      have hlt : Module.finrank k (Q.obj : Type u) < d := by omega
      have hrec := ih _ hlt Q hQ rfl
      calc
        homFinrank k S M * Module.finrank k (S.obj : Type u) ≤
            (homFinrank k S S + homFinrank k S Q) * Module.finrank k (S.obj : Type u) :=
          Nat.mul_le_mul_right _ (homFinrank_le_add_of_mono k (S := S) i)
        _ ≤ d * homFinrank k S S := by
          rw [Nat.add_mul, hd', Nat.add_mul, Nat.mul_comm (homFinrank k S S)]
          exact Nat.add_le_add_left hrec _
    · have hz := (homFinrank_eq_zero_iff k S M).2 (fun f ↦ not_ne_iff.mp (fun h ↦ hnon ⟨f, h⟩))
      rw [hz, Nat.zero_mul]
      exact Nat.zero_le _

end EFiniteCharacterizations
