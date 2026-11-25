module

public import EFiniteCharacterizations.ScalarExtension.FieldExtensionTensorHom
public import EFiniteCharacterizations.ScalarExtension.FieldExtensionWeights
public import EFiniteCharacterizations.Presentations.ProjectiveClassSeparation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Detection of presilting and projectivity under field extension -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

noncomputable section

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R]

local notation "R₊" => ExtendedAlgebra k F R

/-- Hom over the extended field has the same dimension as Hom over the ground field. -/
theorem homFinrank_extendObj (X Y : FGModuleCat.{u} R) :
    homFinrank F (extendObj k F R X) (extendObj k F R Y) = homFinrank k X Y := by
  have := finiteModuleHom_isFinite k X Y
  let b := Module.finBasis k (X ⟶ Y)
  rw [homFinrank_eq_finrank, homFinrank_eq_finrank]
  exact (homTensorEquiv k F R X Y).finrank_eq.symm.trans
    ((Module.finrank_eq_card_basis (Algebra.TensorProduct.basis F b)).trans (Fintype.card_fin _))

/-- Isomorphic extended projective terms have equal ground projective classes. -/
theorem projectiveClass_eq_of_extendObj_iso [IsNoetherianRing R] (P Q : FiniteProjective R)
    (e : extendObj k F R P.val ≅ extendObj k F R Q.val) :
    ProjectiveClass.of P = ProjectiveClass.of Q := by
  let _ := P.property
  let _ := Q.property
  apply ProjectiveClass.eq_of_eval_eq_on_simples k
  intro S _
  rw [projectiveClassWeight_of, projectiveClassWeight_of, projectiveHomWeight_eval, projectiveHomWeight_eval]
  have h : homFinrank F (extendObj k F R P.val) (extendObj k F R S) =
      homFinrank F (extendObj k F R Q.val) (extendObj k F R S) := by
    rw [homFinrank_eq_finrank, homFinrank_eq_finrank]
    exact (Linear.homCongr F e (Iso.refl _)).finrank_eq
  rw [homFinrank_extendObj, homFinrank_extendObj] at h
  exact_mod_cast h

/-- Ground field extension preserves and reflects epimorphisms of finite modules. -/
theorem epi_extendMap_iff {M N : FGModuleCat.{u} R} (f : M ⟶ N) :
    Epi (extendMap k F R f) ↔ Epi f := by
  rw [FGModuleCat.epi_iff_surjective, FGModuleCat.epi_iff_surjective]
  let r := f.hom.hom.restrictScalars k
  change Function.Surjective (r.baseChange F) ↔ Function.Surjective r
  exact Module.FaithfullyFlat.lTensor_surjective_iff_surjective k F r

/-- Composition on the right by an extended module map is base change of
the corresponding ground Hom map. -/
theorem homTensorMap_rightComp {X Y Z : FGModuleCat.{u} R} (q : Y ⟶ Z) (a : F ⊗[k] (X ⟶ Y)) :
    homTensorMap k F R X Z ((Linear.rightComp k X q).baseChange F a) =
      homTensorMap k F R X Y a ≫ extendMap k F R q := by
  have h := ScalarCategory.comp_one_tmul (X := ⟨X⟩) (Y := ⟨Y⟩) (Z := ⟨Z⟩) a q
  change ScalarCategory.compLinear a ((1 : F) ⊗ₜ[k] q) = (Linear.rightComp k X q).baseChange F a at h
  rw [← h, homTensorMap_comp, homTensorMap_tmul, one_smul]

/-- Composition on the left by an extended module map is base change of the
corresponding ground Hom map. -/
theorem homTensorMap_leftComp {X Y Z : FGModuleCat.{u} R} (q : X ⟶ Y) (a : F ⊗[k] (Y ⟶ Z)) :
    homTensorMap k F R X Z ((Linear.leftComp k Z q).baseChange F a) =
      extendMap k F R q ≫ homTensorMap k F R Y Z a := by
  have h := ScalarCategory.one_tmul_comp (X := ⟨X⟩) (Y := ⟨Y⟩) (Z := ⟨Z⟩) q a
  change ScalarCategory.compLinear ((1 : F) ⊗ₜ[k] q) a = (Linear.leftComp k Z q).baseChange F a at h
  rw [← h, homTensorMap_comp, homTensorMap_tmul, one_smul]

/-- Field extension reflects projectivity of finite modules. -/
theorem projective_of_projective_extendObj (M : FGModuleCat.{u} R)
    [Module.Projective R₊ (extendObj k F R M)] : Module.Projective R M := by
  obtain ⟨N, hN, q, hq⟩ := FGModuleCat.exists_projective_epi M
  let _ := (epi_extendMap_iff k F R q).2 hq
  let a := Linear.rightComp k M q
  have hs : Function.Surjective (a.baseChange F) := by
    intro z
    obtain ⟨l, hl⟩ := FGModuleCat.exists_lift_of_projective (extendMap k F R q) (homTensorMap k F R M M z)
    obtain ⟨v, hv⟩ := (homTensorMap_bijective k F R M N).2 l
    refine ⟨v, (homTensorMap_bijective k F R M M).1 ?_⟩
    change homTensorMap k F R M M ((Linear.rightComp k M q).baseChange F v) = homTensorMap k F R M M z
    rw [homTensorMap_rightComp, hv, hl]
  have h := (Module.FaithfullyFlat.lTensor_surjective_iff_surjective k F a).1 hs
  obtain ⟨s, hs⟩ := h (𝟙 M)
  exact Module.Projective.of_split s.hom.hom q.hom.hom
    (congrArg (fun f : M ⟶ M ↦ f.hom.hom) hs)

/-- Presilting of a two-term differential is invariant under arbitrary field extension. -/
theorem isPresilting_extendTwoTerm_iff (P : TwoTerm R) :
    (extendTwoTerm k F R P).IsPresilting ↔ P.IsPresilting := by
  let X := P.source
  let Y := P.target
  let p : X ⟶ Y := P.differential
  let D := boundaryLinear k p p
  let D' := boundaryLinear F (extendMap k F R p) (extendMap k F R p)
  let E := (TensorProduct.prodRight k F F (X ⟶ X) (Y ⟶ Y)).trans
    ((homTensorEquiv k F R X X).prodCongr (homTensorEquiv k F R Y Y))
  let J := homTensorEquiv k F R X Y
  let _ := isScalarTower_ground_extension_hom k F R (extendObj k F R X) (extendObj k F R Y)
  have h : D'.comp E.toLinearMap = J.toLinearMap.comp (D.baseChange F) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c f
    change D' (E (c ⊗ₜ[k] f)) = J (D.baseChange F (c ⊗ₜ[k] f))
    rw [LinearMap.baseChange_tmul]
    have hE : E (c ⊗ₜ[k] f) = (c • extendMap k F R f.1, c • extendMap k F R f.2) := by
      change ((homTensorEquiv k F R X X).prodCongr (homTensorEquiv k F R Y Y))
        ((TensorProduct.prodRight k F F (X ⟶ X) (Y ⟶ Y)) (c ⊗ₜ[k] f)) = _
      rw [TensorProduct.prodRight_tmul]
      exact Prod.ext (homTensorMap_tmul k F R c f.1) (homTensorMap_tmul k F R c f.2)
    rw [hE]
    change (c • extendMap k F R f.1) ≫ extendMap k F R p -
      extendMap k F R p ≫ (c • extendMap k F R f.2) =
      homTensorMap k F R X Y (c ⊗ₜ[k] (f.1 ≫ p - p ≫ f.2))
    rw [homTensorMap_tmul, Linear.smul_comp, Linear.comp_smul, ← smul_sub]
    congr 1
    let G := extend k F R
    change G.map f.1 ≫ G.map p - G.map p ≫ G.map f.2 = G.map (f.1 ≫ p - p ≫ f.2)
    rw [G.map_sub, G.map_comp, G.map_comp]
  change Function.Surjective D' ↔ Function.Surjective D
  rw [← Module.FaithfullyFlat.lTensor_surjective_iff_surjective k F D]
  change Function.Surjective D' ↔ Function.Surjective (D.baseChange F)
  have hfun : (fun x ↦ D' (E x)) = fun x ↦ J (D.baseChange F x) :=
    funext (fun x ↦ DFunLike.congr_fun h x)
  have h₁ : Function.Surjective (fun x ↦ D' (E x)) ↔ Function.Surjective D' := by
    exact ⟨fun H ↦ Function.Surjective.of_comp H, fun H ↦ H.comp E.surjective⟩
  have h₂ : Function.Surjective (fun x ↦ J (D.baseChange F x)) ↔ Function.Surjective (D.baseChange F) := by
    exact ⟨fun H ↦ Function.Surjective.of_comp_left H J.injective, fun H ↦ J.surjective.comp H⟩
  rw [hfun] at h₁
  exact h₁.symm.trans h₂

end

end EFiniteCharacterizations.FieldExtension
