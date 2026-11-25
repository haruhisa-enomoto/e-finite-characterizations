module

public import EFiniteCharacterizations.LinearAlgebra.ScalarTowerCategory
public import EFiniteCharacterizations.Presentations.RigidPair

/-! # Comparing rigid differentials to their finite-field Frobenius conjugates -/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace EFiniteCharacterizations

variable {k F : Type u} [Field k] [Fintype k] [Field F] [Finite F] [Algebra k F]
  {C : Type*} [Category C] [Preadditive C] [Linear k C]

local instance : Module.Finite k F := Module.Finite.of_finite

omit [Fintype k] [Finite F] in
/-- Enlarging the coefficient field preserves rigidity on the scalar-extended terms. -/
theorem boundaryLinear_changeScalars_surjective_iff {L : Type u} [Field L] [Algebra k L]
    (e : F →ₐ[k] L) {X Y : ScalarCategory k F C} (p : X ⟶ Y) :
    let G := ScalarCategory.changeScalars (C := C) e
    Function.Surjective (boundaryLinear L (G.map p) (G.map p)) ↔
      Function.Surjective (boundaryLinear F p p) := by
  let _ : Algebra F L := e.toRingHom.toAlgebra
  let _ : IsScalarTower k F L := IsScalarTower.of_algebraMap_eq (fun x ↦ (e.commutes x).symm)
  let H := ScalarCategory.flatten (k := k) (F := F) (L := L) (C := C)
  let I : ScalarCategory k F C ⥤ ScalarCategory F L (ScalarCategory k F C) := ScalarCategory.of
  let G := ScalarCategory.changeScalars (C := C) e
  have he : IsScalarTower.toAlgHom k F L = e := AlgHom.ext fun _ ↦ rfl
  have hp : H.map (I.map p) = G.map p := by
    have h := ScalarCategory.flatten_of_map (L := L) p
    rw [he] at h
    exact h
  have h := (boundaryLinear_map_surjective_iff L L H (I.map p) (I.map p)).trans
    (boundaryLinear_scalarExtension_surjective_iff F L p p)
  change Function.Surjective (boundaryLinear L (G.map p) (G.map p)) ↔ _
  rw [← hp]
  exact h

/-- Extending coefficients commutes with the Frobenius on each field. -/
theorem changeScalars_frobenius_commutes {L : Type u} [Field L] [Finite L] [Algebra k L]
    (e : F →ₐ[k] L) {X Y : ScalarCategory k F C} (p : X ⟶ Y) :
    let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k F
    let φ := FiniteField.frobeniusAlgEquivOfAlgebraic k L
    let S := ScalarCategory.changeScalars (C := C) σ.toAlgHom
    let G := ScalarCategory.changeScalars (C := C) e
    let T := ScalarCategory.changeScalars (C := C) φ.toAlgHom
    G.map (S.map p) = T.map (G.map p) := by
  intro σ φ S G T
  have hc (x : F) : e (σ x) = φ (e x) := by
    change e (x ^ Fintype.card k) = (e x) ^ Fintype.card k
    exact map_pow e x _
  let E := TensorProduct.map e.toLinearMap (LinearMap.id : (X.obj ⟶ Y.obj) →ₗ[k] _)
  let P := TensorProduct.map σ.toLinearMap (LinearMap.id : (X.obj ⟶ Y.obj) →ₗ[k] _)
  let Q := TensorProduct.map φ.toLinearMap (LinearMap.id : (X.obj ⟶ Y.obj) →ₗ[k] _)
  change E (P p) = Q (E p)
  refine TensorProduct.inductionOn (motive := fun d ↦ E (P d) = Q (E d)) p ?_ ?_
  · intro c f
    simp only [E, P, Q, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      AlgEquiv.toLinearMap_apply, hc]
  · intro f g hf hg
    simp only [map_add, hf, hg]

/-- After a finite extension, a rigid differential on scalar-extended terms
is isomorphic to its Frobenius conjugate. -/
theorem exists_frobenius_iso_square_of_rigid {X Y : ScalarCategory k F C}
    [Module.Finite k (X.obj ⟶ X.obj)] [Module.Finite k (Y.obj ⟶ Y.obj)]
    [Module.Finite k (X.obj ⟶ Y.obj)]
    (p : X ⟶ Y) (hp : Function.Surjective (boundaryLinear F p p)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : Algebra k L) (_ : IsScalarTower k F L),
      ∃ (_ : Finite L),
        let G := ScalarCategory.changeScalars (C := C) (IsScalarTower.toAlgHom k F L)
        let φ := FiniteField.frobeniusAlgEquivOfAlgebraic k L
        let T := ScalarCategory.changeScalars (C := C) φ.toAlgHom
        ∃ (a : G.obj X ≅ G.obj X) (b : G.obj Y ≅ G.obj Y),
          a.hom ≫ G.map p = T.map (G.map p) ≫ b.hom := by
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k F
  let S := ScalarCategory.changeScalars (C := C) σ.toAlgHom
  let q : X ⟶ Y := S.map p
  have hq : Function.Surjective (boundaryLinear F q q) :=
    (boundaryLinear_map_surjective_iff F F S p p).2 hp
  let _ : Module.Finite F (X ⟶ X) := inferInstanceAs (Module.Finite F (F ⊗[k] (X.obj ⟶ X.obj)))
  let _ : Module.Finite F (Y ⟶ Y) := inferInstanceAs (Module.Finite F (F ⊗[k] (Y.obj ⟶ Y.obj)))
  let _ : Module.Finite F (X ⟶ Y) := inferInstanceAs (Module.Finite F (F ⊗[k] (X.obj ⟶ Y.obj)))
  obtain ⟨L, _, _, hL, a, b, h⟩ := exists_finite_field_iso_square_of_rigid_pair F q p hq hp
  let _ : Algebra k L := ((algebraMap F L).comp (algebraMap k F)).toAlgebra
  let _ : IsScalarTower k F L := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let H := ScalarCategory.flatten (k := k) (F := F) (L := L) (C := C)
  let G := ScalarCategory.changeScalars (C := C) (IsScalarTower.toAlgHom k F L)
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic k L
  let T := ScalarCategory.changeScalars (C := C) φ.toAlgHom
  let I : ScalarCategory k F C ⥤ ScalarCategory F L (ScalarCategory k F C) := ScalarCategory.of
  have hG (r : X ⟶ Y) : H.map (I.map r) = G.map r :=
    ScalarCategory.flatten_of_map r
  have hφ : G.map q = T.map (G.map p) := changeScalars_frobenius_commutes (IsScalarTower.toAlgHom k F L) p
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, hL, H.mapIso a, H.mapIso b, ?_⟩
  let U := H.obj (I.obj X)
  let V := H.obj (I.obj Y)
  have hi : (G.map p : U ⟶ V) = H.map (I.map p) := (hG p).symm
  have hj : (H.map (I.map q) : U ⟶ V) = T.map (G.map p) := (hG q).trans hφ
  refine (congrArg (fun r : U ⟶ V ↦ H.map a.hom ≫ r) hi).trans ?_
  refine (H.map_comp a.hom (I.map p)).symm.trans ?_
  refine (congrArg (fun r : I.obj X ⟶ I.obj Y ↦ H.map r) h).trans ?_
  refine (H.map_comp (I.map q) b.hom).trans ?_
  exact congrArg (fun r : U ⟶ V ↦ r ≫ H.map b.hom) hj

end EFiniteCharacterizations
