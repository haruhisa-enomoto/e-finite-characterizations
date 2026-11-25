module

public import EFiniteCharacterizations.Modules.FiniteModuleMorphisms
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Projective covers over finite-dimensional algebras -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.FGModuleCat

variable {R : Type u} [Ring R]

/-- A projective cover is a right-minimal epimorphism from a finite projective. -/
structure ProjectiveCover (M : FGModuleCat.{u} R) where
  source : FGModuleCat.{u} R
  projective_source : Module.Projective R source
  hom : source ⟶ M
  epi_hom : Epi hom
  rightMinimal (a : source ⟶ source) : a ≫ hom = hom → IsIso a

/-- A finite module is a quotient of a finite free module. -/
theorem exists_projective_epi (M : FGModuleCat.{u} R) :
    ∃ (P : FGModuleCat.{u} R) (_ : Module.Projective R P) (p : P ⟶ M), Epi p := by
  have := M.property
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact ⟨FGModuleCat.of R (Fin n → R), inferInstance, FGModuleCat.ofHom f, (epi_iff_surjective _).2 hf⟩

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R] [IsNoetherianRing R]

include k in
/-- Choosing a projective epimorphism of least ground dimension gives a
cover, since the stable image of an endomorphism over its target is a
projective summand still surjecting onto the target. -/
theorem nonempty_projectiveCover (M : FGModuleCat.{u} R) :
    Nonempty (ProjectiveCover M) := by
  classical
  let S (n : ℕ) := ∃ (P : FGModuleCat.{u} R) (_ : Module.Projective R P) (p : P ⟶ M),
    Epi p ∧ Module.finrank k (P.obj : Type u) = n
  have hS : ∃ n, S n := by
    obtain ⟨P, hP, p, hp⟩ := exists_projective_epi M
    exact ⟨_, P, hP, p, hp, rfl⟩
  obtain ⟨P, hP, p, hp, hpdim⟩ := Nat.find_spec hS
  refine ⟨⟨P, hP, p, hp, fun a ha ↦ ?_⟩⟩
  by_contra hnot
  let _ := IsArtinianRing.of_finite k R
  let _ : Module.Finite R P := P.property
  let _ : Module.Finite k P := Module.Finite.trans R P
  let a' : Module.End R P := a.hom.hom
  let p' : P →ₗ[R] M := p.hom.hom
  have ha' : p'.comp a' = p' := congrArg (fun f : P ⟶ M ↦ f.hom.hom) ha
  have hpow (n : ℕ) : p'.comp (a' ^ n) = p' := by
    induction n with
    | zero => simp [Module.End.one_eq_id]
    | succ n ih => rw [pow_succ', Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha', ih]
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp a'.eventually_isCompl_ker_pow_range_pow
  let A := LinearMap.ker (a' ^ (n + 1))
  let B := LinearMap.range (a' ^ (n + 1))
  let e := A.prodEquivOfIsCompl B (hn _ (Nat.le_succ n))
  let r : P →ₗ[R] B := (LinearMap.snd R A B).comp e.symm.toLinearMap
  have hsplit : r.comp B.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    have he : e (0, x) = x.val := by
      change (0 : P) + x.val = x.val
      exact zero_add _
    change (e.symm x.val).2 = x
    rw [← he, e.symm_apply_apply]
  let Q := FGModuleCat.of R B
  have hQ : Module.Projective R Q := Module.Projective.of_split B.subtype r hsplit
  let q : Q ⟶ M := FGModuleCat.ofHom (p'.comp B.subtype)
  have hq : Epi q := (epi_iff_surjective q).2 (by
    intro m
    obtain ⟨v, hv⟩ := ((epi_iff_surjective p).1 hp) m
    exact ⟨⟨(a' ^ (n + 1)) v, LinearMap.mem_range_self _ _⟩,
      (congrArg (fun f : P →ₗ[R] M ↦ f v) (hpow (n + 1))).trans hv⟩)
  have hB : B ≠ ⊤ := by
    intro h
    have hs : Function.Surjective a' := Module.End.surjective_of_iterate_surjective (by omega)
      (LinearMap.range_eq_top.mp h)
    have hi : Function.Injective (a'.restrictScalars k) := LinearMap.injective_iff_surjective.2 hs
    exact hnot ((isIso_iff_bijective a).2 ⟨hi, hs⟩)
  have hlt : Module.finrank k (Q.obj : Type u) < Module.finrank k (P.obj : Type u) := by
    have h := Submodule.finrank_lt (s := B.restrictScalars k)
      (fun h ↦ hB ((Submodule.restrictScalars_eq_top_iff k R P).1 h))
    exact h
  exact (not_lt_of_ge (Nat.find_min' hS (show S (Module.finrank k (Q.obj : Type u)) from
    ⟨Q, hQ, q, hq, rfl⟩))) (hlt.trans_eq hpdim)

end EFiniteCharacterizations.FGModuleCat
