module

public import EFiniteCharacterizations.Characterizations.FixedClassFiniteness
public import Mathlib.RingTheory.Flat.Localization

/-!
# Extraction of jointly stable dependent semibricks

Theorem 3.1 (`thm:extraction`) of the manuscript:

* `exists_rationally_dependent_stable_semibrick`: from any pair of nonzero modules
  `M, N` with `[M] = [N]` and `Hom(M, N) = 0`, one extracts a nonempty finite
  semibrick whose dimension vectors are linearly dependent and whose members are
  simultaneously stable at one integral weight.
* `rationally_independent_and_jointly_stable_of_equalClassHom`: consequently, under
  `(K₀-Hom)`, every finite semibrick has linearly independent dimension vectors and
  admits a single integral weight at which all its members are stable.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct nonZeroDivisors

universe u

namespace EFiniteCharacterizations

/-- Rationalization preserves and reflects independence of an integral family. -/
theorem rationalClass_independent_iff {G : Type*} [AddCommGroup G] {ι : Type*} (v : ι → G) :
    LinearIndependent ℚ (fun i ↦ (1 : ℚ) ⊗ₜ[ℤ] v i) ↔ LinearIndependent ℤ v := by
  have : Module.Flat ℤ ℚ := IsLocalization.flat ℚ ℤ⁰
  exact ⟨fun h ↦ LinearIndependent.of_comp (TensorProduct.mk ℤ ℚ G 1) (h.restrict_scalars' ℤ),
    Module.Flat.linearIndependent_one_tmul⟩

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

/-- A nonzero equal-class pair with vanishing Hom yields a semibrick stable at
one integral projective weight and dependent in the rational Grothendieck group. -/
theorem exists_rationally_dependent_stable_semibrick {M N : FGModuleCat.{u} R}
    (hm : ¬ IsZero M) (hc : GrothendieckGroup.of M = GrothendieckGroup.of N)
    (hh : ∀ f : M ⟶ N, f = 0) :
    ∃ (s : Finset (Skeleton (FGModuleCat.{u} R))) (g : ProjectiveClass R),
      IsSemibrick (C := FGModuleCat.{u} R) ↑s ∧
      (s : Set _) ⊆ stableClasses (C := FGModuleCat.{u} R) (projectiveClassWeight k g) ∧
      ¬ LinearIndependent ℚ (fun x : s ↦ (1 : ℚ) ⊗ₜ[ℤ] GrothendieckGroup.of ((fromSkeleton _).obj x.val)) := by
  have hn : ¬ EqualClassHom (FGModuleCat.{u} R) := by
    intro h
    obtain ⟨f, hf⟩ := h M N hc (FGModuleCat.class_ne_zero hm)
    exact hf (hh f)
  obtain ⟨s, g, hs, hd⟩ := FamilyExtraction.exists_jointly_stable_dependent_semibrick k hn
  exact ⟨s, g, (isSemibrick_stableClasses (C := FGModuleCat.{u} R) _).subset hs, hs,
    fun hi ↦ hd ((rationalClass_independent_iff _).mp hi)⟩

/-- Under equal-class Hom every finite semibrick is simultaneously stable at
an integral weight and its classes are rationally independent. -/
theorem rationally_independent_and_jointly_stable_of_equalClassHom
    (h : EqualClassHom (FGModuleCat.{u} R)) (s : Finset (Skeleton (FGModuleCat.{u} R)))
    (hs : IsSemibrick (C := FGModuleCat.{u} R) ↑s) :
    LinearIndependent ℚ (fun x : s ↦ (1 : ℚ) ⊗ₜ[ℤ] GrothendieckGroup.of ((fromSkeleton _).obj x.val)) ∧
    ∃ g : ProjectiveClass R, (s : Set _) ⊆ stableClasses (C := FGModuleCat.{u} R) (projectiveClassWeight k g) :=
  ⟨(rationalClass_independent_iff _).mpr (FamilyExtraction.independent_semibrick_of_equalClassHom h s hs),
    FamilyExtraction.exists_joint_weight_of_equalClassHom k h s hs⟩

/-- In particular, each brick admits an integral stabilizing weight. -/
theorem exists_projective_weight_stable_of_equalClassHom (h : EqualClassHom (FGModuleCat.{u} R))
    {B : FGModuleCat.{u} R} (hb : IsBrick B) :
    ∃ g : ProjectiveClass R, (projectiveClassWeight k g).IsStable B :=
  exists_projective_weight_stable_of_isEFinite k ((isEFinite_iff_equalClassHom k).mpr h) hb

end EFiniteCharacterizations
