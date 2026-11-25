module

public import EFiniteCharacterizations.RingEpimorphisms.UniversalLocalizationExistence

/-! # Infinite stable inversion charts detect infinite-dimensional localizations -/

@[expose] public section

open CategoryTheory

universe u

namespace EFiniteCharacterizations

variable {R B C : Type u} [Ring R] [Ring B] [Ring C] {I : Type*} {φ : I → TwoTerm R}

theorem IsUniversalLocalization.comp_equiv {f : R →+* B} (h : IsUniversalLocalization φ f)
    (e : B ≃+* C) : IsUniversalLocalization φ (e.toRingHom.comp f) := by
  refine ⟨?_,fun T _ p hp ↦ ?_⟩
  · apply (invertsFamily_comp_iff φ f _).2
    intro i
    apply (((φ i).induce f).isIso_induce_iff_regular _).2
    let := Module.compHom C e.toRingHom
    exact (((φ i).induce f).isIso_iff_invertedOn_all).1 (h.inverts i) (ModuleCat.of B C)
  · obtain ⟨q,hq,hu⟩ := h.desc T p hp
    refine ⟨q.comp e.symm.toRingHom,?_,fun a ha ↦ ?_⟩
    · exact RingHom.ext fun r ↦ (congrArg q (e.symm_apply_apply _)).trans (DFunLike.congr_fun hq r)
    · have he := hu (a.comp e.toRingHom) ha
      exact RingHom.ext fun c ↦ by simpa using DFunLike.congr_fun he (e.symm c)

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

theorem exists_infinite_localization_of_infinite_stable_chart [IsNoetherianRing R] (P : TwoTerm R)
    (h : (P.stableInvertingClasses k).Infinite) :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (g : R →ₐ[k] B),
      IsUniversalLocalization (fun _ : Unit ↦ P) g.toRingHom ∧ ¬ Module.Finite k B := by
  obtain ⟨B,_,_,g,hg⟩ := exists_algebra_universalLocalization k (fun _ : PUnit.{u+1} ↦ P)
  have hu : IsUniversalLocalization (fun _ : Unit ↦ P) g.toRingHom :=
    ⟨fun _ ↦ hg.inverts PUnit.unit,fun T _ f hf ↦ hg.desc T f (fun _ ↦ hf ())⟩
  exact ⟨B,inferInstance,inferInstance,g,hu,fun _ ↦ h (P.finite_stableInvertingClasses_of_finite_localization k g hu)⟩

omit [Module.Finite k R] in
/-- Finiteness for sets of right projective maps applies to a localization
indexed by the unit type. -/
theorem finite_right_singleton_localization (h : RightUniversalLocalizationsFinite k R)
    (P : TwoTerm Rᵐᵒᵖ) {B : Type u} [Ring B] [Algebra k B] (g : Rᵐᵒᵖ →ₐ[k] B)
    (hg : IsUniversalLocalization (fun _ : Unit ↦ P) g.toRingHom) : Module.Finite k B := by
  let f := (AlgHom.op g).comp (AlgEquiv.opOp k R).toAlgHom
  let e := (AlgEquiv.opOp k B).toRingEquiv
  have he : (AlgHom.op f).toRingHom = e.toRingHom.comp g.toRingHom := rfl
  have hu := hg.comp_equiv e
  have hsingle : IsUniversalLocalization (fun i : ({P} : Set (TwoTerm Rᵐᵒᵖ)) ↦ i.val)
      (AlgHom.op f).toRingHom := by
    rw [he]
    refine ⟨fun i ↦ ?_,fun T _ p hp ↦ hu.desc T p (fun _ ↦ hp ⟨P,Set.mem_singleton P⟩)⟩
    rw [Set.mem_singleton_iff.mp i.property]
    exact hu.inverts ()
  have := h {P} Bᵐᵒᵖ f hsingle
  exact Module.Finite.equiv (MulOpposite.opLinearEquiv k).symm

/-- The right-module criterion for all sets already forces finiteness of the
stable chart cut out by each individual right projective differential. -/
theorem finite_right_stable_charts_of_finite_localizations [IsNoetherianRing Rᵐᵒᵖ]
    (h : RightUniversalLocalizationsFinite k R) (P : TwoTerm Rᵐᵒᵖ) :
    (P.stableInvertingClasses k).Finite := by
  by_contra hn
  obtain ⟨B,_,_,g,hg,hB⟩ := exists_infinite_localization_of_infinite_stable_chart k P hn
  exact hB (finite_right_singleton_localization k h P g hg)

end EFiniteCharacterizations
