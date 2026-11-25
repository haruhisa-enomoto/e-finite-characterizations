module

public import EFiniteCharacterizations.ScalarExtension.FiniteGaloisConstituents

/-! # Dimensions and endolengths in a finite Galois orbit of stable modules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.FieldExtension

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]

private theorem finrank_of_iso_pi {n : ℕ} {X : FGModuleCat.{u} R} (B : Fin n → FGModuleCat.{u} R)
    (e : X ≅ FGModuleCat.of R ((i : Fin n) → B i)) :
    Module.finrank k (X.obj : Type u) = ∑ i, Module.finrank k ((B i).obj : Type u) := by
  let (i : Fin n) : Module.Finite k ((B i).obj : Type u) := Module.Finite.trans R _
  let v : (FGModuleCat.of R ((i : Fin n) → B i)).obj ≃ₗ[k] ((i : Fin n) → (B i).obj) :=
    { Equiv.refl _ with map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  exact (((FGModuleCat.isoToLinearEquiv e).restrictScalars k).trans v).finrank_eq.trans
    (Module.finrank_pi_fintype ..)

private theorem homFinrank_of_iso_power {m : ℕ} {X S : FGModuleCat.{u} R}
    (e : X ≅ FGModuleCat.of R (Fin m → S)) :
    homFinrank k S X = m * homFinrank k S S := by
  let v := FGModuleCat.isoToLinearEquiv e
  let l : (S.obj →ₗ[R] X.obj) ≃ₗ[k] (Fin m → (S.obj →ₗ[R] S.obj)) :=
    { toFun := fun f i ↦ (LinearMap.proj i).comp (v.toLinearMap.comp f)
      invFun := fun g ↦ v.symm.toLinearMap.comp (LinearMap.pi g)
      left_inv := fun f ↦ LinearMap.ext (fun x ↦ v.symm_apply_apply (f x))
      right_inv := fun g ↦ funext (fun i ↦ LinearMap.ext (fun x ↦ congrFun (v.apply_symm_apply (fun j ↦ g j x)) i))
      map_add' := fun f g ↦ funext (fun i ↦ LinearMap.ext (fun x ↦ by exact congrFun (v.map_add (f x) (g x)) i))
      map_smul' := fun c f ↦ funext (fun i ↦ LinearMap.ext (fun x ↦ by
        exact congrFun (v.map_smul (algebraMap k R c) (f x)) i)) }
  let _ : Module.Finite k (S.obj : Type u) := Module.Finite.trans R _
  rw [homFinrank_eq_finrank,homFinrank_eq_finrank, (finiteModuleHomLinearEquiv k S X).finrank_eq,
    (finiteModuleHomLinearEquiv k S S).finrank_eq,l.finrank_eq,Module.finrank_pi_fintype]
  simp

omit [Module.Finite k R] in
private theorem homFinrank_of_distinct_stable_sum [IsNoetherianRing R]
    {θ : Weight (FGModuleCat.{u} R)} {n : ℕ} {X : FGModuleCat.{u} R} {B : Fin n → FGModuleCat.{u} R}
    (e : X ≅ ⨁ B) (hb : ∀ i, θ.IsStable (B i)) (hd : Function.Injective (toSkeleton ∘ B)) (i : Fin n) :
    homFinrank k X (B i) = homFinrank k (B i) (B i) := by
  classical
  have vanish {j : Fin n} (hji : j ≠ i) (f : B j ⟶ B i) : f = 0 := by
    by_contra hf
    have := Weight.isIso_of_nonzero (hb j) (hb i) f hf
    exact hji (hd (toSkeleton_eq_toSkeleton_iff.2 ⟨asIso f⟩))
  let l : (X ⟶ B i) ≃ₗ[k] (B i ⟶ B i) :=
    { toFun := fun f ↦ biproduct.ι B i ≫ e.inv ≫ f
      invFun := fun g ↦ e.hom ≫ biproduct.π B i ≫ g
      left_inv := by
        intro f
        apply (cancel_epi e.inv).1
        apply biproduct.hom_ext'
        intro j
        by_cases h : j = i
        · subst j
          simp
        · simp [h,vanish h (biproduct.ι B j ≫ e.inv ≫ f)]
      right_inv := fun g ↦ by simp
      map_add' := fun f g ↦ by simp [Preadditive.comp_add]
      map_smul' := fun c f ↦ by simp [Linear.comp_smul] }
  simpa only [homFinrank_eq_finrank] using l.finrank_eq

variable (F R : Type u) [Field F] [Algebra k F] [Ring R] [Algebra k R] [Module.Finite k R]
  [Module.Finite k F] [IsGalois k F] [IsNoetherianRing R] [IsNoetherianRing (ExtendedAlgebra k F R)]

local notation "A" => ExtendedAlgebra k F R

/-- In the multiplicity-free orbit over a finite extension, the module dimension and
endomorphism dimension of each constituent are obtained by dividing the corresponding
ground dimensions by the size of the orbit. In particular endolength is preserved. -/
theorem finite_galois_constituent_dimensions [Finite k] (P : TwoTerm R) (S : FGModuleCat.{u} R)
    (hs : (P.eulerWeight k).IsStable S) :
    ∃ (n : ℕ) (B : Fin n → FGModuleCat.{u} A), 0 < n ∧ Nonempty (extendObj k F R S ≅ ⨁ B) ∧
      (∀ i, ((extendTwoTerm k F R P).eulerWeight F).IsStable (B i)) ∧
      Function.Injective (toSkeleton ∘ B) ∧
      (∀ Y : FGModuleCat.{u} A, ((extendTwoTerm k F R P).eulerWeight F).IsStable Y →
        ((∃ f : S ⟶ restrictObj k F R Y, f ≠ 0) ↔ ∃ i, Nonempty (Y ≅ B i))) ∧
      (∀ i j, ∃ (σ : Gal(F/k)) (v : restrictObj k F R (B i) ⟶ restrictObj k F R (B j)),
        IsGaloisHom k F R σ v ∧ Function.Bijective v.hom.hom) ∧
      ∀ i, Module.finrank k (S.obj : Type u) = n * Module.finrank F ((B i).obj : Type u) ∧
        homFinrank k S S = n * homFinrank F (B i) (B i) ∧ endolength k S = endolength F (B i) := by
  classical
  obtain ⟨n,B,⟨e⟩,hb,hd,hw,horbit⟩ := finite_galois_constituents k F R P S hs
  let G := forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)
  let _ : PreservesBiproduct B G := preservesBiproduct_of_preservesCoproduct G
  let ep : (⨁ B) ≅ FGModuleCat.of A ((i : Fin n) → B i) :=
    G.preimageIso ((G.mapBiproduct B).trans (ModuleCat.biproductIsoPi fun i ↦ (B i).obj))
  have hsum := (finrank_extendObj k F R S).symm.trans (finrank_of_iso_pi F B (e.trans ep))
  have hpos := hs.isBrick.endolength_pos k
  have hn : 0 < n := by
    by_contra! hz
    obtain rfl : n = 0 := Nat.le_zero.mp hz
    simp at hsum
    exact (Nat.ne_of_gt hpos) (by simp [endolength,hsum])
  refine ⟨n,B,hn,⟨e⟩,hb,hd,hw,horbit,fun i ↦ ?_⟩
  have same (j : Fin n) : Module.finrank F ((B j).obj : Type u) = Module.finrank F ((B i).obj : Type u) := by
    obtain ⟨_,v,_,hv⟩ := horbit j i
    have eq := ((LinearEquiv.ofBijective v.hom.hom hv).restrictScalars k).finrank_eq
    rw [finrank_restrictObj,finrank_restrictObj] at eq
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos eq
  have hdim : Module.finrank k (S.obj : Type u) = n * Module.finrank F ((B i).obj : Type u) := by
    simpa [same] using hsum
  obtain ⟨f,hf⟩ := (hw (B i) (hb i)).2 ⟨i,⟨Iso.refl _⟩⟩
  obtain ⟨m,hm,_,⟨p⟩⟩ := restrict_stable_is_power k F P hs (hb i) f hf
  have hres := finrank_of_iso_pi k (fun _ : Fin m ↦ S) p
  rw [finrank_restrictObj] at hres
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,hdim,← Nat.mul_assoc] at hres
  have hbi := ((hb i).isBrick.endolength_pos F).trans_le (endolength_le_groundFinrank F _)
  have hdegree : Module.finrank k F = m * n := Nat.eq_of_mul_eq_mul_right hbi hres
  have hh := (homFinrank_of_iso_power k p).symm.trans (homFinrank_restrictObj k F R S (B i))
  rw [homFinrank_of_distinct_stable_sum F e hb hd i,hdegree,Nat.mul_assoc] at hh
  have hend := Nat.eq_of_mul_eq_mul_left hm hh
  exact ⟨hdim,hend,by rw [endolength,endolength,hdim,hend,Nat.mul_div_mul_left _ _ hn]⟩

end EFiniteCharacterizations.FieldExtension
