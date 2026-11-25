module

public import EFiniteCharacterizations.Modules.FiniteAlgebra
public import EFiniteCharacterizations.Presentations.TauRigid

/-! # Finiteness of basic tau-tilting modules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R]

/-- The module is a direct sum of `n` pairwise nonisomorphic indecomposables. -/
def HasBasicDecomposition (n : ℕ) (M : FGModuleCat.{u} R) : Prop :=
  ∃ X : Fin n → FGModuleCat.{u} R, (∀ i, Indecomposable (X i)) ∧
    Function.Injective (toSkeleton ∘ X) ∧ Nonempty ((⨁ X) ≅ M)

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R] [IsNoetherianRing R]

/-- The isomorphism classes of basic tau-rigid modules with `n` summands. -/
def basicTauRigidClasses (n : ℕ) : Set (Skeleton (FGModuleCat.{u} R)) :=
  {c | ∃ M : FGModuleCat.{u} R, IsTauRigid k M ∧ HasBasicDecomposition n M ∧ toSkeleton M = c}

/-- Tau-tilting finiteness is finiteness of the basic tau-rigid modules with
as many indecomposable summands as there are simple modules. -/
def IsTauTiltingFinite : Prop :=
  (basicTauRigidClasses (R := R) k (simpleIsomorphismClasses R).ncard).Finite

/-- In any fixed number of summands, finitely many indecomposable tau-rigid
modules give finitely many basic tau-rigid modules. -/
theorem finite_basicTauRigidClasses_of_finite_indecomposable (n : ℕ)
    (h : (indecomposableTauRigidClasses (R := R) k).Finite) :
    (basicTauRigidClasses (R := R) k n).Finite := by
  let D := indecomposableTauRigidClasses (R := R) k
  have : Finite D := h
  let Xs (x : Fin n → D) (j : Fin n) := (fromSkeleton (FGModuleCat.{u} R)).obj (x j).val
  let F (x : Fin n → D) : Skeleton (FGModuleCat.{u} R) :=
    toSkeleton (⨁ Xs x)
  refine (Set.finite_range F).subset ?_
  rintro c ⟨M, hM, ⟨X, hX, _, ⟨e⟩⟩, rfl⟩
  have hτ (j : Fin n) : IsTauRigid k (X j) :=
    IsTauRigid.of_retract k hM (biproduct.ι X j ≫ e.hom) (e.inv ≫ biproduct.π X j)
      (by simp)
  let x (j : Fin n) : D := ⟨toSkeleton (X j), X j, hX j, hτ j, rfl⟩
  let f : (⨁ Xs x) ≅ (⨁ X) := biproduct.mapIso (fun j ↦ fromSkeletonToSkeletonIso (X j))
  exact ⟨x, toSkeleton_eq_toSkeleton_iff.mpr ⟨f.trans e⟩⟩

omit [IsNoetherianRing R] in
/-- The forward tau-tilting implication of the rank-at-most-two theorem. -/
theorem isTauTiltingFinite_of_isEFinite_of_rank_le_two
    (hr : (simpleIsomorphismClasses R).ncard ≤ 2) (hR : IsEFinite R) :
    letI := IsNoetherianRing.of_finite k R
    IsTauTiltingFinite (R := R) k := by
  let _ := IsNoetherianRing.of_finite k R
  exact finite_basicTauRigidClasses_of_finite_indecomposable k _
    (finite_indecomposableTauRigidClasses_of_rank_le_two k hr hR)

omit [IsNoetherianRing R] in
/-- The forward tau-tilting implication for right modules, as stated in Theorem B. -/
theorem isTauTiltingFinite_right_of_isEFinite_of_rank_le_two
    (hr : (simpleIsomorphismClasses Rᵐᵒᵖ).ncard ≤ 2) (hR : IsEFinite Rᵐᵒᵖ) :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    IsTauTiltingFinite (R := Rᵐᵒᵖ) k :=
  isTauTiltingFinite_of_isEFinite_of_rank_le_two k hr hR

end EFiniteCharacterizations
