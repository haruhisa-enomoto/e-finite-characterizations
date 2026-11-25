module

public import EFiniteCharacterizations.Characterizations.ModuleCriteria

/-!
# Consequences for brick-finiteness conjectures and brick-continuity

Section 1 of the manuscript deduces from Theorem A(I) that seven open problems
asking for sufficient conditions for brick-finiteness become equivalent for each
individual finite-dimensional `k`-algebra:

1. Demonet's lattice point conjecture (`(E-fin) ⇒ brick-finite`);
2. Enomoto's finite semibrick conjecture (`(fin-sbrick) ⇒ brick-finite`);
3. Mousavand–Paquette's `n`-semibrick question (`(n-sbrick) ⇒ brick-finite`);
4. the second brick-Brauer–Thrall conjecture (`(brick-discrete) ⇒ brick-finite`);
5. Mousavand–Paquette's generic brick conjecture (`(no-gen-brick) ⇒ brick-finite`);
6. Pfeifer's stable Brauer–Thrall II′ conjecture (`(endo-stab) ⇒ brick-finite`);
7. Angeleri Hügel–Sentieri's wide subcategory question (`(wide) ⇒ brick-finite`).

This file proves this per-algebra equivalence (`seven_pointwise_implications`), the
contrapositive equivalence between brick-continuity and the existence of a generic
brick (`brickContinuous_iff_exists_generic_right_brick`), and exponential brick growth
by `k`-dimension for E-infinite algebras over finite fields.
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

/-- Over an arbitrary field, `Rᵐᵒᵖ` is brick-continuous (has infinitely many bricks of some
endolength `r ≥ 1`) if and only if `Mod Rᵐᵒᵖ` admits a generic brick. -/
theorem brickContinuous_iff_exists_generic_right_brick :
    (∃ r : ℕ, 0 < r ∧ (brickClassesOfEndolength (R := Rᵐᵒᵖ) k r).Infinite) ↔
      ∃ M : ModuleCat.{u} Rᵐᵒᵖ, IsGenericBrick k M := by
  classical
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hd,_,_,_,_,hg,_,_⟩ := moduleCriteria k R
  simpa only [not_forall, exists_prop, Classical.not_imp, not_not, Set.Infinite] using
    (hd.symm.trans hg).not

/-- For each finite-dimensional `k`-algebra, the seven implications `(i)`–`(vii)` from
`(E-fin)`, `(fin-sbrick)`, `(n-sbrick)`, `(brick-discrete)`, `(no-gen-brick)`, `(endo-stab)`,
and `(wide)` to brick-finiteness are pairwise equivalent. -/
theorem seven_pointwise_implications :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    let C := FGModuleCat.{u} Rᵐᵒᵖ
    let conclusion := (brickClasses (C := C)).Finite
    let demonet := IsEFinite Rᵐᵒᵖ → conclusion
    (demonet ↔ ((∀ s : Set (Skeleton C), IsSemibrick s → s.Finite) → conclusion)) ∧
    (demonet ↔ ((∀ s : Set (Skeleton C), IsSemibrick s → s.Finite →
      s.ncard = (simpleIsomorphismClasses Rᵐᵒᵖ).ncard → s = simpleIsomorphismClasses Rᵐᵒᵖ) → conclusion)) ∧
    (demonet ↔ ((∀ r : ℕ, 0 < r → (brickClassesOfEndolength (R := Rᵐᵒᵖ) k r).Finite) → conclusion)) ∧
    (demonet ↔ ((¬ ∃ M : ModuleCat.{u} Rᵐᵒᵖ, IsGenericBrick k M) → conclusion)) ∧
    (demonet ↔ ((∀ (g : ProjectiveClass Rᵐᵒᵖ) (r : ℕ), 0 < r →
      (stableClassesOfEndolength k (projectiveClassWeight k g) r).Finite) → conclusion)) ∧
    (demonet ↔ ((∀ W : ObjectProperty C, IsWideClass W → FunctoriallyFinite W) → conclusion)) := by
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  obtain ⟨_,_,_,_,_,_,_,w,_,n,s,d,t,_,_,_,g,_,_⟩ := moduleCriteria k R
  exact ⟨imp_congr s Iff.rfl, imp_congr n Iff.rfl, imp_congr d Iff.rfl,
    imp_congr g Iff.rfl, imp_congr t Iff.rfl, imp_congr w Iff.rfl⟩

/-- Over a finite field, an E-infinite algebra has exponentially many nonisomorphic bricks of
`k`-dimension at most `m`. -/
theorem finiteField_exponential_bricks_by_dimension [Finite k] (h : ¬ IsEFinite Rᵐᵒᵖ) :
    ∃ (c : ℝ) (m₀ : ℕ), 0 < c ∧ ∀ m ≥ m₀,
      ∃ s : Finset (Skeleton (FGModuleCat.{u} Rᵐᵒᵖ)), Real.exp (c * m) ≤ s.card ∧
        ∀ x ∈ s, ∃ M : FGModuleCat.{u} Rᵐᵒᵖ, toSkeleton M = x ∧ IsBrick M ∧
          Module.finrank k (M.obj : Type u) ≤ m := by
  let := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let := IsArtinianRing.of_finite k Rᵐᵒᵖ
  obtain ⟨P, hp⟩ := FieldExtension.exists_missing_terms k h
  obtain ⟨_, c, m₀, hc, hg⟩ := FieldExtension.exists_exponential_ground_witnesses k P hp
  refine ⟨c, m₀, hc, fun m hm ↦ ?_⟩
  obtain ⟨s, hs, hmem⟩ := hg m hm
  refine ⟨s, hs, fun x hx ↦ ?_⟩
  obtain ⟨M, _, he, _, hst, hl, _⟩ := hmem x hx
  exact ⟨M, he, hst.isBrick, hl⟩

end EFiniteCharacterizations
