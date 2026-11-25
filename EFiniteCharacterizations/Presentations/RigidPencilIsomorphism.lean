module

public import EFiniteCharacterizations.Presentations.RigidPencil
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! # Generic isomorphism of a rigid differential and its pencil -/

@[expose] public section

open CategoryTheory Matrix
open scoped TensorProduct

namespace EFiniteCharacterizations

variable {k : Type*} [Field k] {C : Type*} [Category C] [Preadditive C] [Linear k C]

private theorem isIso_of_leftComp_det_ne_zero {X : C} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k (X ⟶ X)) (a : X ⟶ X)
    (h : (LinearMap.toMatrix b b (Linear.leftComp k X a)).det ≠ 0) : IsIso a := by
  have : Module.Finite k (X ⟶ X) := Module.Finite.of_basis b
  have hinj : Function.Injective (Linear.leftComp k X a) := by
    intro g g' hg
    apply b.equivFun.injective
    apply Matrix.mulVec_injective_of_det_ne_zero h
    change LinearMap.toMatrix b b (Linear.leftComp k X a) *ᵥ (b.repr g : ι → k) =
      LinearMap.toMatrix b b (Linear.leftComp k X a) *ᵥ (b.repr g' : ι → k)
    rw [LinearMap.toMatrix_mulVec_repr, LinearMap.toMatrix_mulVec_repr, hg]
  obtain ⟨g, hg⟩ := LinearMap.injective_iff_surjective.mp hinj (𝟙 X)
  change a ≫ g = 𝟙 X at hg
  refine ⟨⟨g, hg, hinj ?_⟩⟩
  change a ≫ g ≫ a = a ≫ 𝟙 X
  rw [← Category.assoc, hg, Category.id_comp, Category.comp_id]

/-- Invertibility after specialization is ensured by avoiding the zeros of
the determinant of left composition. -/
theorem exists_det_guard_of_polynomialEval_eq_id (X : C) [Module.Finite k (X ⟶ X)]
    (a : (ScalarCategory.mk X : ScalarCategory k (Polynomial k) C) ⟶ ScalarCategory.mk X)
    (ha : polynomialEval (0 : k) a = 𝟙 X) :
    ∃ d : Polynomial k, d.eval 0 = 1 ∧
      ∀ {F : Type*} [Field F] [Algebra k F] (e : Polynomial k →ₐ[k] F), e d ≠ 0 →
        IsIso ((ScalarCategory.changeScalars e).map a) := by
  classical
  let P : ScalarCategory k (Polynomial k) C := ⟨X⟩
  let b := Module.finBasis k (X ⟶ X)
  let bP : Module.Basis _ (Polynomial k) (P ⟶ P) := b.baseChange _
  let M := LinearMap.toMatrix bP bP (Linear.leftComp (Polynomial k) P a)
  have h₀ : M.map (Polynomial.evalRingHom 0) = 1 := by
    rw [← LinearMap.toMatrix_id b]
    ext i j
    rw [Matrix.map_apply]
    change (Polynomial.evalRingHom 0) (LinearMap.toMatrix bP bP _ i j) = _
    rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    change Polynomial.eval 0 ((b.baseChange (Polynomial k)).repr (a ≫ bP j) i) = b.repr (b j) i
    rw [← polynomialEval_coord b]
    change b.repr (polynomialEval 0 (ScalarCategory.compLinear a (bP j))) i = b.repr (b j) i
    rw [ScalarCategory.compLinear, polynomialEval_baseChangeBilinear, ha]
    change b.repr (𝟙 X ≫ polynomialEval 0 ((b.baseChange (Polynomial k)) j)) i = b.repr (b j) i
    rw [Module.Basis.baseChange_apply, polynomialEval_tmul]
    simp
  refine ⟨M.det, ?_, ?_⟩
  · change (Polynomial.evalRingHom (0 : k)) M.det = 1
    rw [RingHom.map_det]
    change (M.map (Polynomial.evalRingHom 0)).det = 1
    rw [h₀, Matrix.det_one]
  intro F _ _ e hdet
  let G := ScalarCategory.changeScalars (C := C) e
  let bF : Module.Basis _ F (G.obj P ⟶ G.obj P) := b.baseChange _
  have hm : LinearMap.toMatrix bF bF (Linear.leftComp F (G.obj P) (G.map a)) = M.map e := by
    ext i j
    rw [Matrix.map_apply]
    change _ = e (LinearMap.toMatrix bP bP _ i j)
    rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    change bF.repr (G.map a ≫ bF j) i = e (bP.repr (a ≫ bP j) i)
    have hb : G.map (bP j) = bF j := by
      change TensorProduct.map e.toLinearMap LinearMap.id ((b.baseChange (Polynomial k)) j) =
        (b.baseChange F) j
      simp
    calc
      bF.repr (G.map a ≫ bF j) i = bF.repr (G.map (a ≫ bP j)) i := by rw [G.map_comp, hb]
      _ = e (bP.repr (a ≫ bP j) i) := baseChange_coord_map b e _ i
  apply isIso_of_leftComp_det_ne_zero bF
  rw [hm]
  have hmap : e M.det = (M.map e).det := e.toRingHom.map_det M
  rw [← hmap]
  exact hdet

/-- An endomorphism over the polynomial Hom spaces with identity specialization
becomes invertible after an injective coefficient map into a field. -/
theorem isIso_changeScalars_of_polynomialEval_eq_id {F : Type*} [Field F] [Algebra k F]
    (e : Polynomial k →ₐ[k] F) (he : Function.Injective e) (X : C) [Module.Finite k (X ⟶ X)]
    (a : (ScalarCategory.mk X : ScalarCategory k (Polynomial k) C) ⟶ ScalarCategory.mk X)
    (ha : polynomialEval (0 : k) a = 𝟙 X) : IsIso ((ScalarCategory.changeScalars e).map a) := by
  obtain ⟨d, hd, h⟩ := exists_det_guard_of_polynomialEval_eq_id X a ha
  apply h e
  intro hz
  have hzero := he (hz.trans (map_zero e).symm)
  rw [hzero, Polynomial.eval_zero] at hd
  exact zero_ne_one hd

variable (k)

universe w

/-- One polynomial controls where the pencil is isomorphic to its rigid member. -/
theorem exists_pencil_iso_polynomial {X Y : C} (u σ : X ⟶ Y)
    [Module.Finite k (X ⟶ X)] [Module.Finite k (Y ⟶ Y)] [Module.Finite k (X ⟶ Y)]
    (h : Function.Surjective (boundaryLinear k u u)) :
    ∃ d : Polynomial k, d.eval 0 = 1 ∧
      ∀ {F : Type w} [Field F] [Algebra k F] (e : Polynomial k →ₐ[k] F), e d ≠ 0 →
        let G := ScalarCategory.changeScalars (C := C) e
        let X' : ScalarCategory k (Polynomial k) C := ⟨X⟩
        let Y' : ScalarCategory k (Polynomial k) C := ⟨Y⟩
        ∃ (a : G.obj X' ≅ G.obj X') (b : G.obj Y' ≅ G.obj Y'),
          a.hom ≫ G.map (show X' ⟶ Y' from 1 ⊗ₜ[k] u) =
            G.map (differentialPencil k u σ) ≫ b.hom := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_polynomial_chain_map k u σ h
  obtain ⟨d₁, hd₁, h₁⟩ := exists_det_guard_of_polynomialEval_eq_id X a ha
  obtain ⟨d₂, hd₂, h₂⟩ := exists_det_guard_of_polynomialEval_eq_id Y b hb
  refine ⟨d₁ * d₂, by rw [Polynomial.eval_mul, hd₁, hd₂, one_mul], ?_⟩
  intro F _ _ e he
  rw [map_mul] at he
  let G := ScalarCategory.changeScalars (C := C) e
  have ha' : IsIso (G.map a) := h₁ e (left_ne_zero_of_mul he)
  have hb' : IsIso (G.map b) := h₂ e (right_ne_zero_of_mul he)
  refine ⟨@asIso _ _ _ _ (G.map a) ha', @asIso _ _ _ _ (G.map b) hb', ?_⟩
  let uP : (ScalarCategory.mk X : ScalarCategory k (Polynomial k) C) ⟶ ScalarCategory.mk Y := 1 ⊗ₜ[k] u
  change G.map a ≫ G.map uP = G.map (differentialPencil k u σ) ≫ G.map b
  have hmap := congrArg (fun f : (ScalarCategory.mk X : ScalarCategory k (Polynomial k) C) ⟶
    ScalarCategory.mk Y ↦ G.map f) (show a ≫ uP = _ from hab)
  simpa only [G.map_comp] using hmap

/-- Over any field in which the pencil parameter is transcendental, a pencil
through a rigid differential is isomorphic to that differential. -/
theorem exists_generic_pencil_iso {X Y : C} (u σ : X ⟶ Y)
    [Module.Finite k (X ⟶ X)] [Module.Finite k (Y ⟶ Y)] [Module.Finite k (X ⟶ Y)]
    {F : Type*} [Field F] [Algebra k F] (e : Polynomial k →ₐ[k] F) (he : Function.Injective e)
    (h : Function.Surjective (boundaryLinear k u u)) :
    let G := ScalarCategory.changeScalars (C := C) e
    let X' : ScalarCategory k (Polynomial k) C := ⟨X⟩
    let Y' : ScalarCategory k (Polynomial k) C := ⟨Y⟩
    ∃ (a : G.obj X' ≅ G.obj X') (b : G.obj Y' ≅ G.obj Y'),
      a.hom ≫ G.map (show X' ⟶ Y' from 1 ⊗ₜ[k] u) =
        G.map (differentialPencil k u σ) ≫ b.hom := by
  obtain ⟨d, hd, hiso⟩ := exists_pencil_iso_polynomial k u σ h
  apply hiso e
  intro hz
  have hzero := he (hz.trans (map_zero e).symm)
  rw [hzero, Polynomial.eval_zero] at hd
  exact zero_ne_one hd

/-- An affine pencil is isomorphic to its rigid member outside the zero set of
a polynomial with constant coefficient one. -/
theorem exists_affine_iso_polynomial {X Y : C} (u σ : X ⟶ Y)
    [Module.Finite k (X ⟶ X)] [Module.Finite k (Y ⟶ Y)] [Module.Finite k (X ⟶ Y)]
    (h : Function.Surjective (boundaryLinear k u u)) :
    ∃ d : Polynomial k, d.eval 0 = 1 ∧
      ∀ {F : Type w} [Field F] [Algebra k F] (e : Polynomial k →ₐ[k] F), e d ≠ 0 →
        let G : C ⥤ ScalarCategory k F C := ScalarCategory.of
        ∃ (a : G.obj X ≅ G.obj X) (b : G.obj Y ≅ G.obj Y),
          a.hom ≫ G.map u = (G.map u + (e Polynomial.X) • G.map (σ - u)) ≫ b.hom := by
  obtain ⟨d, hd, hiso⟩ := exists_pencil_iso_polynomial k u σ h
  refine ⟨d, hd, ?_⟩
  intro F _ _ e he
  let G : C ⥤ ScalarCategory k F C := ScalarCategory.of
  let H := ScalarCategory.changeScalars (C := C) e
  let X' : ScalarCategory k (Polynomial k) C := ⟨X⟩
  let Y' : ScalarCategory k (Polynomial k) C := ⟨Y⟩
  let u' : X' ⟶ Y' := 1 ⊗ₜ[k] u
  obtain ⟨a, b, hab⟩ := hiso e he
  have ha : H.map u' = G.map u := by
    change (e 1 : F) ⊗ₜ[k] u = (1 : F) ⊗ₜ[k] u
    rw [map_one]
  have hp : H.map (differentialPencil k u σ) = G.map u + (e Polynomial.X) • G.map (σ - u) := by
    change TensorProduct.map e.toLinearMap LinearMap.id
      ((1 : Polynomial k) ⊗ₜ[k] u + (Polynomial.X : Polynomial k) •
        ((1 : Polynomial k) ⊗ₜ[k] (σ - u))) =
      (1 : F) ⊗ₜ[k] u + (e Polynomial.X) • ((1 : F) ⊗ₜ[k] (σ - u))
    simp [TensorProduct.smul_tmul']
  refine ⟨a, b, ?_⟩
  change a.hom ≫ H.map u' = H.map (differentialPencil k u σ) ≫ b.hom at hab
  exact (congrArg (fun f : H.obj X' ⟶ H.obj Y' ↦ a.hom ≫ f) ha).symm.trans
    (hab.trans (congrArg (fun f : H.obj X' ⟶ H.obj Y' ↦ f ≫ b.hom) hp))

/-- An affine pencil after scalar extension is isomorphic to its rigid
member at zero when the parameter is transcendental. -/
theorem exists_generic_affine_iso {X Y : C} (u σ : X ⟶ Y)
    [Module.Finite k (X ⟶ X)] [Module.Finite k (Y ⟶ Y)] [Module.Finite k (X ⟶ Y)]
    {F : Type*} [Field F] [Algebra k F] (e : Polynomial k →ₐ[k] F) (he : Function.Injective e)
    (h : Function.Surjective (boundaryLinear k u u)) :
    let G : C ⥤ ScalarCategory k F C := ScalarCategory.of
    ∃ (a : G.obj X ≅ G.obj X) (b : G.obj Y ≅ G.obj Y),
      a.hom ≫ G.map u = (G.map u + (e Polynomial.X) • G.map (σ - u)) ≫ b.hom := by
  obtain ⟨d, hd, hiso⟩ := exists_affine_iso_polynomial k u σ h
  apply hiso e
  intro hz
  have hzero := he (hz.trans (map_zero e).symm)
  rw [hzero, Polynomial.eval_zero] at hd
  exact zero_ne_one hd

end EFiniteCharacterizations
