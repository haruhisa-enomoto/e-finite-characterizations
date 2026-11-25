module

public import EFiniteCharacterizations.ScalarExtension.SeparableStableExtension
public import EFiniteCharacterizations.ScalarExtension.FiniteGaloisCorrespondence
public import EFiniteCharacterizations.ScalarExtension.FieldExtensionTensorHom
public import Mathlib.RingTheory.LittleWedderburn

/-! # Multiplicity-free stable constituents after finite Galois extension -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra TensorProduct

universe u
namespace EFiniteCharacterizations.FieldExtension

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R] [Module.Finite k R]
local notation "A" => ExtendedAlgebra k F R

/-- The endomorphism algebra of an extended ground brick over a finite
ground field remains commutative after any scalar extension. -/
theorem extended_brick_endomorphisms_commute [Finite k] (S : FGModuleCat.{u} R) (hs : IsBrick S)
    (f g : extendObj k F R S ⟶ extendObj k F R S) : f ≫ g = g ≫ f := by
  let D := Module.End R (S.obj : Type u)
  let _ : DivisionRing D := hs.endomorphismDivisionRing k
  let _ : Module.Finite k (S.obj : Type u) := Module.Finite.trans R _
  let _ : Finite (S.obj : Type u) := Module.finite_of_finite k
  let _ : Finite D := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let _ : Field D := littleWedderburn D
  have comm (a b : S ⟶ S) : a ≫ b = b ≫ a :=
    FGModuleCat.hom_ext (show (b.hom.hom : D) * a.hom.hom = a.hom.hom * b.hom.hom from mul_comm ..)
  obtain ⟨x,rfl⟩ := (homTensorMap_bijective k F R S S).2 f
  obtain ⟨y,rfl⟩ := (homTensorMap_bijective k F R S S).2 g
  revert y
  refine TensorProduct.inductionOn x ?_ ?_
  · intro c a y
    refine TensorProduct.inductionOn y ?_ ?_
    · intro d b
      simp only [homTensorMap_tmul,Linear.smul_comp,Linear.comp_smul,smul_smul]
      have h := (extend k F R).congr_map (comm a b)
      rw [mul_comm d c]
      exact congrArg (fun z ↦ (c*d) • z) (((extend k F R).map_comp a b).symm.trans
        (h.trans ((extend k F R).map_comp b a)))
    · intro y z hy hz
      simp only [map_add,Preadditive.add_comp,Preadditive.comp_add,hy,hz]
  · intro x w hx hw y
    simp only [map_add,Preadditive.add_comp,Preadditive.comp_add,hx,hw]

private theorem distinct_summands_of_commuting_endomorphisms {D : Type u} [Ring D] {n : ℕ}
    {X : FGModuleCat.{u} D} {B : Fin n → FGModuleCat.{u} D} (e : X ≅ ⨁ B)
    (hn : ∀ i, ¬ IsZero (B i)) (comm : ∀ a b : X ⟶ X, a ≫ b = b ≫ a) :
    Function.Injective (toSkeleton ∘ B) := by
  classical
  have cc (a b : (⨁ B) ⟶ (⨁ B)) : a ≫ b = b ≫ a := by
    have h := comm (e.hom ≫ a ≫ e.inv) (e.hom ≫ b ≫ e.inv)
    simpa using congrArg (fun v ↦ e.inv ≫ v ≫ e.hom) h
  intro i j he
  by_contra hij
  obtain ⟨a⟩ := toSkeleton_eq_toSkeleton_iff.1 he
  let p := biproduct.π B i ≫ biproduct.ι B i
  let t := biproduct.π B i ≫ a.hom ≫ biproduct.ι B j
  have h := congrArg (fun v ↦ biproduct.ι B i ≫ v ≫ biproduct.π B j) (cc p t)
  have hz : a.hom = 0 := by simpa [p,t,hij,Ne.symm hij] using h
  exact hn i ((IsZero.iff_id_eq_zero _).2 (by rw [← a.hom_inv_id,hz,zero_comp]))

variable [Module.Finite k F] [IsGalois k F] [IsNoetherianRing R] [IsNoetherianRing (ExtendedAlgebra k F R)]

/-- A stable module over a finite ground field extends to a multiplicity-free
sum of stable modules forming one Galois orbit. The summands are exactly the
stable extension modules whose restrictions admit a nonzero map from S. -/
theorem finite_galois_constituents [Finite k] (P : TwoTerm R) (S : FGModuleCat.{u} R)
    (hs : (P.eulerWeight k).IsStable S) :
    ∃ (n : ℕ) (B : Fin n → FGModuleCat.{u} A), Nonempty (extendObj k F R S ≅ ⨁ B) ∧
      (∀ i, ((extendTwoTerm k F R P).eulerWeight F).IsStable (B i)) ∧ Function.Injective (toSkeleton ∘ B) ∧
      (∀ Y : FGModuleCat.{u} A, ((extendTwoTerm k F R P).eulerWeight F).IsStable Y →
        ((∃ f : S ⟶ restrictObj k F R Y, f ≠ 0) ↔ ∃ i, Nonempty (Y ≅ B i))) ∧
      ∀ i j, ∃ (σ : Gal(F/k)) (v : restrictObj k F R (B i) ⟶ restrictObj k F R (B j)),
        IsGaloisHom k F R σ v ∧ Function.Bijective v.hom.hom := by
  classical
  obtain ⟨n,B,hB,⟨e⟩⟩ := extend_stable_is_sum_of_stables k F R P hs
  let G := forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)
  let _ : PreservesBiproduct B G := preservesBiproduct_of_preservesCoproduct G
  let ep : (⨁ B) ≅ FGModuleCat.of A ((i : Fin n) → B i) :=
    G.preimageIso ((G.mapBiproduct B).trans (ModuleCat.biproductIsoPi fun i ↦ (B i).obj))
  let d := e.trans ep.symm
  have witness (i : Fin n) : ∃ f : S ⟶ restrictObj k F R (B i), f ≠ 0 := by
    let p := d.hom ≫ biproduct.π B i
    have hp : p ≠ 0 := by
      intro hz
      apply (hB i).1
      apply (IsZero.iff_id_eq_zero _).2
      simpa [p] using (congrArg ((biproduct.ι B i ≫ d.inv) ≫ ·) hz)
    let a := homLinearEquiv k F R S (B i)
    exact ⟨a p,fun h ↦ hp (a.injective (h.trans a.map_zero.symm))⟩
  refine ⟨n,B,⟨d⟩,hB,distinct_summands_of_commuting_endomorphisms d (fun i ↦ (hB i).1)
    (extended_brick_endomorphisms_commute k F R S hs.isBrick),?_,?_⟩
  · intro Y hY
    constructor
    · rintro ⟨f,hf⟩
      let l := (homLinearEquiv k F R S Y).symm
      let q := d.inv ≫ l f
      obtain ⟨i,hi⟩ : ∃ i, biproduct.ι B i ≫ q ≠ 0 := by
        by_contra! h
        have hz : q = 0 := biproduct.hom_ext' _ _ (fun i ↦ (h i).trans comp_zero.symm)
        have hlf : l f = 0 := (cancel_epi d.inv).1 (hz.trans comp_zero.symm)
        exact hf (l.injective (hlf.trans l.map_zero.symm))
      have := Weight.isIso_of_nonzero (hB i) hY _ hi
      exact ⟨i,⟨(asIso (biproduct.ι B i ≫ q)).symm⟩⟩
    · rintro ⟨i,⟨ei⟩⟩
      obtain ⟨f,hf⟩ := witness i
      let iso := (restrict k F R).mapIso ei.symm
      exact ⟨f ≫ iso.hom,fun h ↦ hf ((cancel_mono iso.hom).1 (h.trans zero_comp.symm))⟩
  · intro i j
    obtain ⟨f,hf⟩ := witness i
    obtain ⟨g,hg⟩ := witness j
    exact (same_ground_class_iff_galois_conjugate k F R P (hB i) (hB j) hs hs f hf g hg).1 ⟨Iso.refl S⟩

end EFiniteCharacterizations.FieldExtension
