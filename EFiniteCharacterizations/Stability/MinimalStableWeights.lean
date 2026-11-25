module

public import EFiniteCharacterizations.Presentations.PresiltingCompletions
public import EFiniteCharacterizations.Presentations.TauRigid
public import EFiniteCharacterizations.Silting.Fans.CoveredWeights
public import EFiniteCharacterizations.Stability.SemistableExact

/-! # Removing redundant projective terms at a stable module -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R] (k : Type u) [Field k]
  [Algebra k R] [Module.Finite k R]

/-- Passing to the minimal presentation of the cokernel preserves stability
of every module stable at the original presilting weight. On quotients of
such a module the Euler evaluations both count maps from the cokernel. -/
theorem TwoTerm.minimalPresentation_stable (P : TwoTerm R) (hp : P.IsPresilting)
    (p : MinimalPresentation (cokernel P.differential)) {B : FGModuleCat.{u} R}
    (hB : (P.eulerWeight k).IsStable B) :
    p.twoTerm.IsPresilting ∧ (p.twoTerm.eulerWeight k).IsStable B := by
  let V := p.twoTerm
  have transfer (X : FGModuleCat.{u} R) (hs : Function.Surjective (P.precompose X)) :
      Function.Surjective (V.precompose X) :=
    p.surjective_precompose_of_presentation_retract (𝟙 _) (𝟙 _) (Category.id_comp _) P
      (cokernel.π _) (cokernel.condition _) (ShortComplex.exact_cokernel _) hs
  have hv : V.IsPresilting := (TwoTerm.surjective_boundary_iff_surjective_precompose V V).2
    (V.surjective_precompose_of_iso p.cokernelIso.symm (transfer _ ((TwoTerm.surjective_boundary_iff_surjective_precompose P P).1 hp)))
  have hperp := ((P.isSemistable_eulerWeight_iff_perpendicular k hp _).1 hB.isSemistable).2
  have he (X : FGModuleCat.{u} R) (q : B ⟶ X) [Epi q] :
      (V.eulerWeight k).eval X = (P.eulerWeight k).eval X := by
    have hX : Subsingleton (X ⟶ P.nakayamaKernel k) := ⟨fun f g ↦ (cancel_epi q).1 (hperp.elim _ _)⟩
    have hY := (V.surjective_precompose_iff_no_hom_nakayamaKernel k X).1
      (transfer X ((P.surjective_precompose_iff_no_hom_nakayamaKernel k X).2 hX))
    rw [V.eulerWeight_eq_perpendicular_difference k,P.eulerWeight_eq_perpendicular_difference k,
      (homFinrank_eq_zero_iff k _ _).2 (fun f ↦ hX.elim f 0),
      (homFinrank_eq_zero_iff k _ _).2 (fun f ↦ hY.elim f 0),homFinrank_eq_finrank k,homFinrank_eq_finrank k]
    simp only [Nat.cast_zero,sub_zero]
    exact_mod_cast (Linear.homCongr k p.cokernelIso (Iso.refl X)).finrank_eq
  refine ⟨hv,hB.1,(he B (𝟙 B)).trans hB.2.1,fun {U} i hi hn hproper ↦ ?_⟩
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i)
    (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
  have hv := (V.eulerWeight k).eval_shortExact S hS
  have hp := (P.eulerWeight k).eval_shortExact S hS
  dsimp only [S] at hv hp
  linarith only [hv,hp,he B (𝟙 B),he _ (cokernel.π i),hB.2.2 i hn hproper]

end EFiniteCharacterizations
