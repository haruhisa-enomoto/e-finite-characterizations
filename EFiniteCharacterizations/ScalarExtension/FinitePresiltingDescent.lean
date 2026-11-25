module

public import EFiniteCharacterizations.LinearAlgebra.SemilinearIteration
public import EFiniteCharacterizations.ScalarExtension.FieldExtensionSemilinear
public import EFiniteCharacterizations.ScalarExtension.FiniteFrobeniusComparison
public import EFiniteCharacterizations.ScalarExtension.PresiltingDescent

/-! # Persistence of missing presilting classes over finite fields -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

private theorem exists_period {W : Type*} [AddCommGroup W] [Finite W] (a : W ≃+ W) :
    let t : AddMonoid.End W := a.toAddMonoidHom
    ∃ n : ℕ, 0 < n ∧ t ^ n = 1 := by
  let _ : Finite (AddMonoid.End W) :=
    Finite.of_injective (fun f : AddMonoid.End W ↦ (f : W → W)) DFunLike.coe_injective
  let u : (AddMonoid.End W)ˣ := ⟨a.toAddMonoidHom, a.symm.toAddMonoidHom,
    AddMonoidHom.ext a.apply_symm_apply, AddMonoidHom.ext a.symm_apply_apply⟩
  exact u.isUnit.isOfFinOrder.exists_pow_eq_one

variable {k F R : Type u} [Field k] [Fintype k] [Field F] [Finite F] [Algebra k F]
  [Ring R] [Algebra k R] [Module.Finite k R]

local instance : Module.Finite k F := Module.Finite.of_finite

omit [Fintype k] in
private theorem finite_extendObj (M : FGModuleCat.{u} R) : Finite (extendObj k F R M : Type u) := by
  let _ : Module.Finite F (extendObj k F R M : Type u) :=
    Module.Finite.trans (ExtendedAlgebra k F R) _
  let b := Module.finBasis F (extendObj k F R M : Type u)
  exact Finite.of_injective b.equivFun b.equivFun.injective

/-- A rigid differential on extended terms that is isomorphic to its
Frobenius conjugate descends after adjoining enough scalars for the
semilinear maps to satisfy the cyclic descent equation. -/
theorem exists_presilting_class_of_frobenius_square
    {X Y : ScalarCategory k F (FGModuleCat.{u} R)}
    (hX : Module.Projective R X.obj) (hY : Module.Projective R Y.obj)
    (p : X ⟶ Y) (hp : Function.Surjective (boundaryLinear F p p)) (a : X ≅ X) (b : Y ≅ Y)
    (h : a.hom ≫ p =
      (ScalarCategory.changeScalars (FiniteField.frobeniusAlgEquivOfAlgebraic k F).toAlgHom).map p ≫ b.hom) :
    ∃ P : TwoTerm R, P.IsPresilting ∧
      P.projectiveClass = ProjectiveClass.of ⟨Y.obj, hY⟩ - ProjectiveClass.of ⟨X.obj, hX⟩ := by
  let G := extendScalarCategory k F R
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k F
  let aF := semilinearEquiv σ (G.mapIso a)
  let bF := semilinearEquiv σ (G.mapIso b)
  let _ := finite_extendObj (k := k) (F := F) X.obj
  let _ := finite_extendObj (k := k) (F := F) Y.obj
  obtain ⟨m, hm, hma⟩ := exists_period aF
  obtain ⟨n, hn, hnb⟩ := exists_period bF
  obtain ⟨L, _, _, hL, hdegree, _⟩ := exists_finiteFieldExtension F (m * n) (Nat.mul_pos hm hn)
  let _ : Algebra k L := ((algebraMap F L).comp (algebraMap k F)).toAlgebra
  let _ : IsScalarTower k F L := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let _ : Module.Finite k L := Module.Finite.of_finite
  let e := IsScalarTower.toAlgHom k F L
  let H := extendScalarCategory k L R
  let J := ScalarCategory.changeScalars (C := FGModuleCat.{u} R) e
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic k L
  let aL := semilinearEquiv φ (H.mapIso (J.mapIso a))
  let bL := semilinearEquiv φ (H.mapIso (J.mapIso b))
  let a₀ : AddMonoid.End (G.obj X) := aF.toAddMonoidHom
  let b₀ : AddMonoid.End (G.obj Y) := bF.toAddMonoidHom
  let a₁ : AddMonoid.End (H.obj (J.obj X)) := aL.toAddMonoidHom
  let b₁ : AddMonoid.End (H.obj (J.obj Y)) := bL.toAddMonoidHom
  change a₀ ^ m = 1 at hma
  change b₀ ^ n = 1 at hnb
  have hφ : orderOf φ = Module.finrank k F * (m * n) := by
    change orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic k L) = _
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, ← Module.finrank_mul_finrank k F L, hdegree]
  have hpos : orderOf φ ≠ 0 := by
    rw [hφ]
    exact (Nat.mul_pos Module.finrank_pos (Nat.mul_pos hm hn)).ne'
  have haF : a₀ ^ orderOf φ = 1 := by
    rw [hφ, show Module.finrank k F * (m * n) = m * (Module.finrank k F * n) by ac_rfl, pow_mul, hma, one_pow]
  have hbF : b₀ ^ orderOf φ = 1 := by
    rw [hφ, show Module.finrank k F * (m * n) = n * (Module.finrank k F * m) by ac_rfl, pow_mul, hnb, one_pow]
  have hσφ (c : F) : e (σ c) = φ (e c) := map_pow e c _
  have haL : a₁ ^ orderOf φ = 1 :=
    semilinear_pow_eq_one_of_compatible φ a₀ a₁
      (semilinearEquiv_tensor_smul φ (H.mapIso (J.mapIso a)))
      (semilinearEquiv_coefficientMap e σ φ hσφ a) haF (pow_orderOf_eq_one φ)
  have hbL : b₁ ^ orderOf φ = 1 :=
    semilinear_pow_eq_one_of_compatible φ b₀ b₁
      (semilinearEquiv_tensor_smul φ (H.mapIso (J.mapIso b)))
      (semilinearEquiv_coefficientMap e σ φ hσφ b) hbF (pow_orderOf_eq_one φ)
  have hgen (γ : Gal(L/k)) : ∃ t : ℕ, φ ^ t = γ := by
    obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k L).2 γ
    exact ⟨i.val, hi⟩
  obtain ⟨ρ, hρ⟩ := DescentAction.exists_of_generator φ hgen a₁ haL hpos
    (semilinearEquiv_field_smul φ (H.mapIso (J.mapIso a)))
    (semilinearEquiv_algebra_smul φ (H.mapIso (J.mapIso a)))
  obtain ⟨τ, hτ⟩ := DescentAction.exists_of_generator φ hgen b₁ hbL hpos
    (semilinearEquiv_field_smul φ (H.mapIso (J.mapIso b)))
    (semilinearEquiv_algebra_smul φ (H.mapIso (J.mapIso b)))
  let q := J.map p
  let S := ScalarCategory.changeScalars (C := FGModuleCat.{u} R) σ.toAlgHom
  let T := ScalarCategory.changeScalars (C := FGModuleCat.{u} R) φ.toAlgHom
  have hq : (J.mapIso a).hom ≫ q = T.map q ≫ (J.mapIso b).hom := by
    refine (J.map_comp a.hom p).symm.trans ?_
    refine (congrArg (fun z : X ⟶ Y ↦ J.map z) h).trans ?_
    refine (J.map_comp (S.map p) b.hom).trans ?_
    exact congrArg (fun z : J.obj X ⟶ J.obj Y ↦ z ≫ J.map b.hom)
      (changeScalars_frobenius_commutes e p)
  let d := H.map q
  have hd (x : H.obj (J.obj X)) : d.hom.hom (aL x) = bL (d.hom.hom x) :=
    semilinearEquiv_commutes φ q (J.mapIso a) (J.mapIso b) hq x
  have hcomm (γ : Gal(L/k)) (x : H.obj (J.obj X)) :
      d.hom.hom (ρ.action γ x) = τ.action γ (d.hom.hom x) := by
    obtain ⟨i, rfl⟩ := hgen γ
    rw [map_pow, map_pow, hρ, hτ]
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [pow_succ', pow_succ']
      change d.hom.hom (aL ((a₁ ^ i) x)) = bL ((b₁ ^ i) (d.hom.hom x))
      exact (hd _).trans (congrArg bL ih)
  let _ := hX
  let _ := hY
  let P : TwoTerm (ExtendedAlgebra k L R) := ⟨H.obj (J.obj X), H.obj (J.obj Y),
    projective_extendObj k L R X.obj, projective_extendObj k L R Y.obj, d⟩
  have hP : P.IsPresilting := by
    change Function.Surjective (boundaryLinear L (H.map q) (H.map q))
    exact (boundaryLinear_map_surjective_iff L L H q q).2
      ((boundaryLinear_changeScalars_surjective_iff e p).2 hp)
  exact exists_presilting_of_extended_terms_of_descent P hP ρ τ hcomm ⟨X.obj, hX⟩ ⟨Y.obj, hY⟩
    (Iso.refl _) (Iso.refl _)

/-- The existence of a presilting differential on scalar-extended projective
terms forces the original projective class to have a presilting representative. -/
theorem exists_presilting_class_of_finite_extension (P : TwoTerm R)
    (p : (extendTwoTerm k F R P).source ⟶ (extendTwoTerm k F R P).target)
    (hp : ({ extendTwoTerm k F R P with differential := p }).IsPresilting) :
    ∃ Q : TwoTerm R, Q.IsPresilting ∧ Q.projectiveClass = P.projectiveClass := by
  let X : ScalarCategory k F (FGModuleCat.{u} R) := ⟨P.source⟩
  let Y : ScalarCategory k F (FGModuleCat.{u} R) := ⟨P.target⟩
  let G := extendScalarCategory k F R
  obtain ⟨q, hq⟩ := (homTensorEquiv k F R P.source P.target).surjective p
  let d : X ⟶ Y := q
  have hmap : G.map d = p := hq
  have hrigid : Function.Surjective (boundaryLinear F d d) := by
    apply (boundaryLinear_map_surjective_iff F F G d d).1
    rw [hmap]
    exact hp
  let _ : Module.Finite k (X.obj ⟶ X.obj) := finiteModuleHom_isFinite k P.source P.source
  let _ : Module.Finite k (Y.obj ⟶ Y.obj) := finiteModuleHom_isFinite k P.target P.target
  let _ : Module.Finite k (X.obj ⟶ Y.obj) := finiteModuleHom_isFinite k P.source P.target
  obtain ⟨L, _, _, _, _, _, a, b, hab⟩ := exists_frobenius_iso_square_of_rigid d hrigid
  let e := IsScalarTower.toAlgHom k F L
  let H := ScalarCategory.changeScalars (C := FGModuleCat.{u} R) e
  exact exists_presilting_class_of_frobenius_square P.projective_source P.projective_target
    (H.map d) ((boundaryLinear_changeScalars_surjective_iff e d).2 hrigid) a b hab

end EFiniteCharacterizations.FieldExtension
