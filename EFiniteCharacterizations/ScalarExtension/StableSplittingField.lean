module

public import EFiniteCharacterizations.ScalarExtension.GaloisConstituentDimensions
public import Mathlib.FieldTheory.Finite.GaloisField

/-! # The endomorphism field splits a stable module over a finite field -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R] [Module.Finite k F] [IsNoetherianRing R] [IsNoetherianRing (ExtendedAlgebra k F R)]

local notation "A" => ExtendedAlgebra k F R

/-- If restriction is stable, the original module is stable at the extended weight. -/
theorem isStable_of_restrictObj (P : TwoTerm R) {Y : FGModuleCat.{u} A}
    (h : (P.eulerWeight k).IsStable (restrictObj k F R Y)) :
    ((extendTwoTerm k F R P).eulerWeight F).IsStable Y := by
  have nonzero (X : FGModuleCat.{u} A) : ¬ IsZero X ↔ ¬ IsZero (restrictObj k F R X) := by
    simp only [FGModuleCat.isZero_iff_subsingleton]
    rfl
  have hss := (isSemistable_restrictObj_iff k F R P Y).1 h.isSemistable
  refine ⟨(nonzero Y).2 h.1,hss.1,?_⟩
  intro U i hi hu hp
  let f : restrictObj k F R U ⟶ restrictObj k F R Y := (restrict k F R).map i
  let _ : Mono f := (FGModuleCat.mono_iff_injective f).2 ((FGModuleCat.mono_iff_injective i).1 hi)
  have hh := h.2.2 f ((nonzero U).1 hu) (fun hfi ↦ hp ((FGModuleCat.isIso_iff_bijective i).2
    ((FGModuleCat.isIso_iff_bijective f).1 hfi)))
  rw [eulerWeight_eval_restrictObj] at hh
  exact neg_of_mul_neg_right hh (by positivity)

variable {F} in
private theorem splitting_degree_eq_orbit_size [Finite k] [IsGalois k F] (P : TwoTerm R)
    (S : FGModuleCat.{u} R) (hs : (P.eulerWeight k).IsStable S) (Y : FGModuleCat.{u} A)
    (e : S ≅ restrictObj k F R Y) :
    ∃ B : Fin (Module.finrank k F) → FGModuleCat.{u} A,
      Nonempty (extendObj k F R S ≅ ⨁ B) ∧
      (∀ i, ((extendTwoTerm k F R P).eulerWeight F).IsStable (B i)) ∧ Function.Injective (toSkeleton ∘ B) ∧
      (∀ i j, ∃ (σ : Gal(F/k)) (v : restrictObj k F R (B i) ⟶ restrictObj k F R (B j)),
        IsGaloisHom k F R σ v ∧ Function.Bijective v.hom.hom) ∧
      ∀ i, Module.finrank k (S.obj : Type u) = Module.finrank k F * Module.finrank F ((B i).obj : Type u) ∧
        homFinrank k S S = Module.finrank k F * homFinrank F (B i) (B i) ∧ endolength k S = endolength F (B i) := by
  obtain ⟨n,B,_,he,hb,hd,hw,ho,hnum⟩ := finite_galois_constituent_dimensions k F R P S hs
  have hy := isStable_of_restrictObj k F R P (hs.of_iso e)
  have hne : e.hom ≠ 0 := fun hz ↦ hs.1 ((IsZero.iff_id_eq_zero S).2 (by rw [← e.hom_inv_id,hz,zero_comp]))
  obtain ⟨i,⟨a⟩⟩ := (hw Y hy).1 ⟨e.hom,hne⟩
  have hyDim := ((FGModuleCat.isoToLinearEquiv e).restrictScalars k).finrank_eq
  rw [finrank_restrictObj,((FGModuleCat.isoToLinearEquiv a).restrictScalars F).finrank_eq,(hnum i).1] at hyDim
  have hn := Nat.eq_of_mul_eq_mul_right (((hb i).isBrick.endolength_pos F).trans_le (endolength_le_groundFinrank F _)) hyDim
  subst n
  exact ⟨B,he,hb,hd,ho,hnum⟩

variable {F R} in
/-- A stable module over a finite field has a finite splitting field of degree equal to
its endomorphism dimension. Its distinct stable constituents over that field all have
scalar endomorphisms and dimension equal to the ground module's endolength. -/
theorem exists_stable_splitting_field [Finite k] (P : TwoTerm R) (S : FGModuleCat.{u} R)
    (hs : (P.eulerWeight k).IsStable S) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Module.Finite k L) (_ : IsGalois k L),
      letI := IsNoetherianRing.of_finite L (ExtendedAlgebra k L R)
      Module.finrank k L = homFinrank k S S ∧
      ∃ B : Fin (Module.finrank k L) → FGModuleCat.{u} (ExtendedAlgebra k L R),
        Nonempty (extendObj k L R S ≅ ⨁ B) ∧
        (∀ i, ((extendTwoTerm k L R P).eulerWeight L).IsStable (B i)) ∧ Function.Injective (toSkeleton ∘ B) ∧
        (∀ i j, ∃ (σ : Gal(L/k)) (v : restrictObj k L R (B i) ⟶ restrictObj k L R (B j)),
          IsGaloisHom k L R σ v ∧ Function.Bijective v.hom.hom) ∧
        ∀ i, homFinrank L (B i) (B i) = 1 ∧ endolength k S = Module.finrank L ((B i).obj : Type u) ∧
          Module.finrank k (S.obj : Type u) = Module.finrank k L * Module.finrank L ((B i).obj : Type u) := by
  classical
  let D := Module.End R (S.obj : Type u)
  let _ : DivisionRing D := hs.isBrick.endomorphismDivisionRing k
  let _ : Module.Finite k (S.obj : Type u) := Module.Finite.trans R _
  let _ : Finite (S.obj : Type u) := Module.finite_of_finite k
  let _ : Finite D := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let _ : Field D := littleWedderburn D
  have deg : Module.finrank k D = homFinrank k S S := by
    rw [homFinrank_eq_finrank,(finiteModuleHomLinearEquiv k S S).finrank_eq]
  let _ : SMulCommClass D R (S.obj : Type u) := ⟨fun d r x ↦ d.map_smul r x⟩
  let _ : Module (ExtendedAlgebra k D R) (S.obj : Type u) := TensorProduct.Algebra.module
  let _ : IsScalarTower D (ExtendedAlgebra k D R) (S.obj : Type u) := IsScalarTower.of_algebraMap_smul
    (fun d x ↦ show d • ((1 : R) • x) = d • x by rw [one_smul])
  let _ := Module.Finite.of_restrictScalars_finite k D (S.obj : Type u)
  let _ := Module.Finite.of_restrictScalars_finite D (ExtendedAlgebra k D R) (S.obj : Type u)
  let Y := FGModuleCat.of (ExtendedAlgebra k D R) (S.obj : Type u)
  let v : (S.obj : Type u) ≃ₗ[R] (restrictObj k D R Y).obj :=
    { Equiv.refl _ with map_add' := fun _ _ ↦ rfl, map_smul' := fun r x ↦
        show r • x = (1 : D) • (r • x) from (one_smul _ _).symm }
  let _ := IsNoetherianRing.of_finite D (ExtendedAlgebra k D R)
  obtain ⟨B,he,hb,hd,ho,hnum⟩ := splitting_degree_eq_orbit_size k R P S hs Y v.toFGModuleCatIso
  refine ⟨D,inferInstance,inferInstance,inferInstance,inferInstance,deg,B,he,hb,hd,ho,fun i ↦ ?_⟩
  obtain ⟨hdim,hend,hlen⟩ := hnum i
  rw [← deg] at hend
  have h1 : homFinrank D (B i) (B i) = 1 := Nat.eq_of_mul_eq_mul_left Module.finrank_pos (hend.symm.trans (Nat.mul_one _).symm)
  exact ⟨h1,by simpa only [endolength,h1,Nat.div_one] using hlen,hdim⟩

end EFiniteCharacterizations.FieldExtension
