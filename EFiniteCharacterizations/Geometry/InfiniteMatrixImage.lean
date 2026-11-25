module

public import EFiniteCharacterizations.Geometry.GenericLocalizationFamily

/-! # Infinite ground dimension of the prime matrix image -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

private theorem simple_lift_of_surjective_action {F A D : Type u}
    [Field F] [Ring A] [Algebra F A] [Module.Finite F A]
    [Ring D] [Algebra F D] [Module.Finite F D]
    (t : A →ₐ[F] D) (X : FGModuleCat.{u} A) [Nontrivial X]
    (α : D →ₐ[F] Module.End F (X.obj : Type u)) (hα : Function.Surjective α)
    (ht : ∀ a x, α (t a) x = a • x) :
    ∃ Y : FGModuleCat.{u} D, Simple Y ∧ Nonempty ((finiteRestriction F t).obj Y ≅ X) := by
  let := Module.compHom X α.toRingHom
  let : IsScalarTower F D X := IsScalarTower.of_algebraMap_smul fun c x ↦
    congrArg (fun f : Module.End F (X.obj : Type u) ↦ f x) (α.commutes c)
  have : Module.Finite F (X.obj : Type u) := Module.Finite.trans A _
  let := Module.Finite.of_restrictScalars_finite F D X
  let Y := FGModuleCat.of D X
  have hsim : IsSimpleModule D X := by
    apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
    refine ⟨inferInstance,fun x hx y ↦ ?_⟩
    obtain ⟨e,he⟩ := (isSimpleModule_iff_toSpanSingleton_surjective
      (R := Module.End F (X.obj : Type u)) (M := (X.obj : Type u))).mp inferInstance |>.2 x hx y
    obtain ⟨d,rfl⟩ := hα e
    exact ⟨d,he⟩
  let := IsNoetherianRing.of_finite F D
  let V := forget₂ (FGModuleCat D) (ModuleCat.{u} D)
  have : Simple (V.obj Y) := (simple_iff_isSimpleModule' _).2 hsim
  let e : ((finiteRestriction F t).obj Y) ≃ₗ[A] X :=
    { toEquiv := Equiv.refl _, map_add' := fun _ _ ↦ rfl, map_smul' := ht }
  exact ⟨Y,V.simple_of_simple_obj Y,⟨(forget₂ (FGModuleCat A) (ModuleCat.{u} A)).preimageIso e.toModuleIso⟩⟩

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]

/-- An infinite fixed-dimensional family of distinct geometric simple modules
cannot factor through one finite-dimensional ground algebra. -/
theorem infinite_of_matrix_specializations {B C : Type u} [Ring B] [Algebra k B] [Ring C] [Algebra k C]
    (f : R →ₐ[k] B) (p : B →ₐ[k] C) {d : ℕ} (hd : 0 < d)
    {S : Set (Skeleton (FGModuleCat.{u} (ExtendedAlgebra k (AlgebraicClosure k) R)))} (hS : S.Infinite)
    (hfib : ∀ x : S, ∃ (M : FGModuleCat.{u} (ExtendedAlgebra k (AlgebraicClosure k) R))
      (v : Module.Basis (Fin d) (AlgebraicClosure k) (M.obj : Type u))
      (ρ : B →ₐ[k] Matrix (Fin d) (Fin d) (AlgebraicClosure k)), toSkeleton M = x.val ∧
      (∀ r, ρ (f r) = basedAction v (1 ⊗ₜ[k] r)) ∧ Submodule.span (AlgebraicClosure k) (Set.range ρ) = ⊤ ∧
      ∃ π : C →ₐ[k] Matrix (Fin d) (Fin d) (AlgebraicClosure k), ∀ b, π (p b) = ρ b) :
    ¬ Module.Finite k C := by
  classical
  intro hfin
  let F := AlgebraicClosure k
  let A := ExtendedAlgebra k F R
  let D := ExtendedAlgebra k F C
  let := IsNoetherianRing.of_finite F D
  let := IsArtinianRing.of_finite F D
  let t : A →ₐ[F] D := Algebra.TensorProduct.map (AlgHom.id F F) (p.comp f)
  let V := finiteRestriction F t
  apply hS
  apply ((finite_simpleIsomorphismClasses (R := D) F).image V.mapSkeleton.obj).subset
  intro x hx
  obtain ⟨M,v,ρ,hm,hr,hspan,π,hπ⟩ := hfib ⟨x,hx⟩
  let β : D →ₐ[F] Matrix (Fin d) (Fin d) F := Algebra.TensorProduct.lift
    (Algebra.ofId F _) π (fun c b ↦ Algebra.commutes c (π b))
  have hb (b : B) : β (1 ⊗ₜ[k] p b) = ρ b := by
    change (algebraMap F _ 1) * π (p b) = _
    rw [map_one,one_mul,hπ]
  have hsur : Function.Surjective β := by
    change Function.Surjective β.toLinearMap
    rw [← LinearMap.range_eq_top (f := β.toLinearMap)]
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro z ⟨b,hb'⟩
    exact ⟨(1 : F) ⊗ₜ[k] p b,(hb b).trans hb'⟩
  let α := (LinearMap.toMatrixAlgEquiv v).symm.toAlgHom.comp β
  have hact : β.comp t = basedAction v := by
    apply Algebra.TensorProduct.ext
    · ext
    · apply AlgHom.ext
      intro r
      exact (hb (f r)).trans (hr r)
  have ht (a : A) (x : M) : α (t a) x = a • x := by
    have ha := DFunLike.congr_fun hact a
    change β (t a) = basedAction v a at ha
    change ((LinearMap.toMatrixAlgEquiv v).symm (β (t a))) x = _
    rw [ha]
    exact LinearMap.congr_fun ((LinearMap.toMatrixAlgEquiv v).symm_apply_apply _) x
  let : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have : Nontrivial M := v.equivFun.symm.injective.nontrivial
  obtain ⟨Y,hY,⟨e⟩⟩ := simple_lift_of_surjective_action t M α
    ((LinearMap.toMatrixAlgEquiv v).symm.surjective.comp hsur) ht
  refine ⟨toSkeleton Y,⟨Y,rfl,hY⟩,?_⟩
  simpa only [Functor.mapSkeleton_obj_toSkeleton] using (congr_toSkeleton_of_iso e).trans hm

/-- A missing projective class gives an infinite-dimensional prime matrix
image of a ground universal localization. -/
theorem exists_infinite_prime_localization_image (hn : ¬ IsEFinite R) :
    ∃ (P : TwoTerm R) (B : Type u) (_ : Ring B) (_ : Algebra k B) (f : R →ₐ[k] B),
      IsUniversalLocalization (fun _ : Unit ↦ P) f.toRingHom ∧
      ∃ (d : ℕ) (_ : 0 < d) (K : Type u) (_ : Field K) (q : B →+* Matrix (Fin d) (Fin d) K),
        Submodule.span K (Set.range q) = ⊤ ∧
        (∀ a b, q a ≠ 0 → q b ≠ 0 → ∃ z, q (a*z*b) ≠ 0) ∧
        (letI := imageAlgebra (k := k) q; ¬ Module.Finite k q.range) := by
  classical
  obtain ⟨P,B,_,_,f,hf,d,hd,K,_,q,S,hS,hgeneric,hprime,hfib⟩ := exists_generic_localization_family k hn
  refine ⟨P,B,inferInstance,inferInstance,f,hf,d,hd,K,inferInstance,q,hgeneric,hprime,?_⟩
  let := imageAlgebra (k := k) q
  let p : B →ₐ[k] q.range := { __ := q.rangeRestrict, commutes' := fun _ ↦ rfl }
  exact infinite_of_matrix_specializations k f p hd hS hfib

end EFiniteCharacterizations.FieldExtension
