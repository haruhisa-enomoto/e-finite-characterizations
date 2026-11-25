module

public import EFiniteCharacterizations.RingEpimorphisms.LocalizationCharts
public import EFiniteCharacterizations.ScalarExtension.FieldExtension
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Stable inversion charts after extension of the ground field -/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace EFiniteCharacterizations

variable {R B C : Type u} [Ring R] [Ring B] [Ring C] {I : Type*}

theorem InvertsFamily.comp {φ : I → TwoTerm R} {f : R →+* B}
    (hf : InvertsFamily φ f) (q : B →+* C) : InvertsFamily φ (q.comp f) := by
  apply (invertsFamily_comp_iff φ f q).2
  intro i
  apply ((φ i).induce f |>.isIso_induce_iff_regular q).2
  let := Module.compHom C q
  exact ((φ i).induce f |>.isIso_iff_invertedOn_all).1 (hf i) (ModuleCat.of B C)

namespace FieldExtension

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Algebra k R] [Algebra k B]
variable {φ : I → TwoTerm R}

/-- The scalar extension of the ground localization surjects onto the
localization at the induced family. -/
theorem exists_surjective_extended_localization (f : R →ₐ[k] B)
    (hf : IsUniversalLocalization φ f.toRingHom) [Algebra F C]
    (g : ExtendedAlgebra k F R →ₐ[F] C)
    (hg : IsUniversalLocalization (fun i ↦ (φ i).induce (algebraInclusion k F R).toRingHom) g.toRingHom) :
    ∃ p : ExtendedAlgebra k F B →ₐ[F] C, Function.Surjective p ∧
      p.comp (Algebra.TensorProduct.map (AlgHom.id F F) f) = g := by
  let := Algebra.compHom C (algebraMap k F)
  let : IsScalarTower k F C := IsScalarTower.of_algebraMap_eq' rfl
  let a := (g.restrictScalars k).comp (algebraInclusion k F R)
  obtain ⟨b,hb,_⟩ := hf.desc C a.toRingHom ((invertsFamily_comp_iff _ _ _).2 hg.inverts)
  let β : B →ₐ[k] C :=
    { __ := b
      commutes' := fun x ↦ by
        rw [← f.commutes]
        exact (DFunLike.congr_fun hb _).trans (a.commutes x) }
  let p : ExtendedAlgebra k F B →ₐ[F] C := Algebra.TensorProduct.lift (Algebra.ofId F C) β
    (fun x y ↦ Algebra.commutes x (β y))
  let q : ExtendedAlgebra k F R →ₐ[F] ExtendedAlgebra k F B :=
    Algebra.TensorProduct.map (AlgHom.id F F) f
  have hq : InvertsFamily (fun i ↦ (φ i).induce (algebraInclusion k F R).toRingHom) q.toRingHom := by
    apply (invertsFamily_comp_iff _ _ _).1
    exact hf.inverts.comp (algebraInclusion k F B).toRingHom
  obtain ⟨s,hs,_⟩ := hg.desc _ q.toRingHom hq
  have hpq : p.comp q = g := by
    apply Algebra.TensorProduct.ext
    · ext
    · ext x
      change p (q (1 ⊗ₜ[k] x)) = g (1 ⊗ₜ[k] x)
      change (algebraMap F C 1) * b (f x) = _
      rw [map_one,one_mul]
      exact DFunLike.congr_fun hb x
  have hid : p.toRingHom.comp s = RingHom.id C := by
    apply hg.epic
    rw [RingHom.comp_assoc,hs]
    exact congrArg AlgHom.toRingHom hpq
  exact ⟨p,(fun x ↦ ⟨s x,DFunLike.congr_fun hid x⟩),hpq⟩

/-- The ground localization spans the entire geometric localization after
extending its scalar field. -/
theorem exists_spanning_ground_action (f : R →ₐ[k] B)
    (hf : IsUniversalLocalization φ f.toRingHom) [Algebra F C]
    (g : ExtendedAlgebra k F R →ₐ[F] C)
    (hg : IsUniversalLocalization (fun i ↦ (φ i).induce (algebraInclusion k F R).toRingHom) g.toRingHom) :
    letI := Algebra.compHom C (algebraMap k F)
    ∃ p : B →ₐ[k] C, (∀ r, p (f r) = g (1 ⊗ₜ[k] r)) ∧
      Submodule.span F (Set.range p) = ⊤ := by
  let := Algebra.compHom C (algebraMap k F)
  let : IsScalarTower k F C := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨q,hq,hcomp⟩ := exists_surjective_extended_localization k F f hf g hg
  let p := (q.restrictScalars k).comp (algebraInclusion k F B)
  refine ⟨p,?_,top_unique fun x _ ↦ ?_⟩
  · intro r
    exact DFunLike.congr_fun hcomp (1 ⊗ₜ[k] r)
  obtain ⟨y,rfl⟩ := hq x
  refine TensorProduct.inductionOn y ?_ ?_
  · intro a b
    have he : q (a ⊗ₜ[k] b) = a • p b := by
      change q (a ⊗ₜ[k] b) = a • q (1 ⊗ₜ[k] b)
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b,rfl⟩)
  · intro u v hu hv
    rw [map_add]
    exact Submodule.add_mem _ hu hv

/-- A finite-dimensional localization stays finite-dimensional at the induced
family after any field extension, including the algebraic closure. -/
theorem finite_extended_localization [Module.Finite k B] (f : R →ₐ[k] B)
    (hf : IsUniversalLocalization φ f.toRingHom) [Algebra F C]
    (g : ExtendedAlgebra k F R →ₐ[F] C)
    (hg : IsUniversalLocalization (fun i ↦ (φ i).induce (algebraInclusion k F R).toRingHom) g.toRingHom) :
    Module.Finite F C := by
  obtain ⟨p,hp,_⟩ := exists_surjective_extended_localization k F f hf g hg
  exact Module.Finite.of_surjective p.toLinearMap hp

/-- Infinitely many geometric stable classes inverting a single ground
differential force its ground localization to be infinite-dimensional. -/
theorem infinite_localization_of_infinite_extended_stable_chart
    [Module.Finite k R] [IsNoetherianRing (ExtendedAlgebra k F R)]
    (P : TwoTerm R) (f : R →ₐ[k] B)
    (hf : IsUniversalLocalization (fun _ : Unit ↦ P) f.toRingHom)
    (h : ((P.induce (algebraInclusion k F R).toRingHom).stableInvertingClasses F).Infinite) :
    ¬ Module.Finite k B := by
  intro hfin
  obtain ⟨C,_,_,g,hg,hC⟩ := exists_infinite_localization_of_infinite_stable_chart F _ h
  exact hC (finite_extended_localization k F f hf g hg)

end FieldExtension

end EFiniteCharacterizations
