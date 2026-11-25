module

public import EFiniteCharacterizations.Silting.Fans.FourQuadrants
public import EFiniteCharacterizations.Presentations.RepresentProjectiveClass

/-! # The real span of projective classes and the rank-two cover -/

@[expose] public section

open scoped TensorProduct

universe u

namespace EFiniteCharacterizations

/-- The real vector space of projective classes. -/
abbrev RealProjectiveSpace (R : Type u) [Ring R] := ℝ ⊗[ℤ] ProjectiveClass R

/-- Regard an integral projective class as a vector in the real space. -/
def realProjectiveClass (R : Type u) [Ring R] : ProjectiveClass R →+ RealProjectiveSpace R :=
  (TensorProduct.mk ℤ ℝ (ProjectiveClass R) 1).toAddMonoidHom

theorem span_realProjectiveClasses (R : Type u) [Ring R] :
    Submodule.span ℝ (Set.range (realProjectiveClass R ∘ ProjectiveClass.of)) = ⊤ := by
  let W := Submodule.span ℝ (Set.range (realProjectiveClass R ∘ ProjectiveClass.of))
  have scalar_mem (c : ℝ) (P : FiniteProjective R) : c ⊗ₜ[ℤ] ProjectiveClass.of P ∈ W := by
    have he : c ⊗ₜ[ℤ] ProjectiveClass.of P = c • realProjectiveClass R (ProjectiveClass.of P) := by
      change _ = c • ((1 : ℝ) ⊗ₜ[ℤ] ProjectiveClass.of P)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [he]
    exact W.smul_mem c (Submodule.subset_span ⟨P, rfl⟩)
  apply Submodule.eq_top_iff'.mpr
  intro x
  refine TensorProduct.inductionOn x ?_ ?_
  · intro r c
    obtain ⟨P, Q, rfl⟩ := ProjectiveClass.exists_sub c
    rw [TensorProduct.tmul_sub]
    exact W.sub_mem (scalar_mem r P) (scalar_mem r Q)
  · intro a b ha hb
    exact W.add_mem ha hb

private theorem exists_pair_covering_fin {α : Type*} [Nonempty α] {n : ℕ} (hn : n ≤ 2)
    (f : Fin n → α) : ∃ a b : α, ∀ i, f i = a ∨ f i = b := by
  cases n with
  | zero =>
    obtain ⟨a⟩ := ‹Nonempty α›
    exact ⟨a, a, fun i ↦ Fin.elim0 i⟩
  | succ n =>
    cases n with
    | zero =>
      refine ⟨f 0, f 0, fun i ↦ Or.inl (congrArg f (Fin.ext ?_))⟩
      have hi := i.isLt
      change i.val = 0
      omega
    | succ n =>
      have hn' : n = 0 := by omega
      subst n
      refine ⟨f 0, f 1, fun i ↦ ?_⟩
      have hi := i.isLt
      rcases (show i.val = 0 ∨ i.val = 1 by omega) with h | h
      · exact Or.inl (congrArg f (Fin.ext h))
      · exact Or.inr (congrArg f (Fin.ext h))

/-- If the real space has dimension at most two, it is spanned by the
classes of two finite projectives. A zero projective may fill an unused slot. -/
theorem exists_two_projectiveClasses_spanning (R : Type u) [Ring R]
    [Module.Finite ℝ (RealProjectiveSpace R)] (h : Module.finrank ℝ (RealProjectiveSpace R) ≤ 2) :
    ∃ P Q : FiniteProjective R, ∀ v : RealProjectiveSpace R, ∃ a b : ℝ,
      a • realProjectiveClass R (ProjectiveClass.of P) + b • realProjectiveClass R (ProjectiveClass.of Q) = v := by
  classical
  let s := Set.range (realProjectiveClass R ∘ ProjectiveClass.of)
  have hs : ⊤ ≤ Submodule.span ℝ s := (span_realProjectiveClasses R).ge
  let t := (linearIndepOn_empty ℝ (id : RealProjectiveSpace R → RealProjectiveSpace R)).extend (Set.empty_subset s)
  let b₀ : Module.Basis t ℝ (RealProjectiveSpace R) := Module.Basis.ofSpan hs
  have : Finite t := Module.Finite.finite_basis b₀
  let _ : Fintype t := Fintype.ofFinite t
  let b := b₀.reindex (Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b₀).symm)
  have hP (i : Fin (Module.finrank ℝ (RealProjectiveSpace R))) :
      ∃ P : FiniteProjective R, realProjectiveClass R (ProjectiveClass.of P) = b i := by
    have hi : b i ∈ Set.range b₀ := by
      rw [← Module.Basis.range_reindex]
      exact ⟨i, rfl⟩
    exact Module.Basis.ofSpan_subset hs hi
  choose P hP using hP
  have : Nonempty (FiniteProjective R) := ⟨ProjectiveClass.zeroProjective R⟩
  obtain ⟨X, Y, hXY⟩ := exists_pair_covering_fin h P
  refine ⟨X, Y, fun v ↦ Submodule.mem_span_pair.mp ?_⟩
  have hsub : Set.range b ⊆ {realProjectiveClass R (ProjectiveClass.of X),
      realProjectiveClass R (ProjectiveClass.of Y)} := by
    rintro _ ⟨i, rfl⟩
    rw [← hP]
    rcases hXY i with hi | hi <;> simp [hi]
  have hv : v ∈ Submodule.span ℝ (Set.range b) := by rw [b.span_eq]; trivial
  exact Submodule.span_mono hsub hv

namespace TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]

include k in
/-- E-finiteness in real projective rank at most two gives a finite cover
by sectors of presilting pairs. -/
theorem exists_presilting_cover_of_projective_rank_le_two [Module.Finite ℝ (RealProjectiveSpace R)]
    (hrank : Module.finrank ℝ (RealProjectiveSpace R) ≤ 2) (hR : IsEFinite R) :
    ∃ s : List (TwoTerm R × TwoTerm R),
      (∀ p ∈ s, (p.1.directSum p.2).IsPresilting) ∧
      ∀ v : RealProjectiveSpace R, ∃ p ∈ s,
        v ∈ sectorBetween (realProjectiveClass R p.1.projectiveClass) (realProjectiveClass R p.2.projectiveClass) := by
  obtain ⟨P, Q, h⟩ := exists_two_projectiveClasses_spanning R hrank
  exact exists_presilting_plane_cover k hR (realProjectiveClass R) P Q h

end TwoTerm

end EFiniteCharacterizations
