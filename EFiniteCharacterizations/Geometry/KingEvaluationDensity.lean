module

public import EFiniteCharacterizations.Geometry.KingEvaluation

/-! # Density of homogeneous evaluation in the King scheme -/

@[expose] public section

open DirectSum
universe u
namespace EFiniteCharacterizations.VertexRepresentation

variable {k R I J : Type u} [Field k] [Ring R] [Algebra k R]
    [Fintype I] [DecidableEq I] [Fintype J]
    (b : Module.Basis J k R) (d : I → ℕ) (e : I → R) (w : I → ℤ)

local notation "A" => KingPiece b d e w
local notation "D" => kingGrading b d e w

def kingEvaluationPoints : Set (ProjectiveSpectrum D) :=
  {p | ∃ (x : VertexRepresentation (k := k) d e), ∃ h, kingPoint b w x h = p}

/-- Each relevant prime omits a positive-degree form. Multiplying by this
form detects every homogeneous component of an element on the evaluation locus. -/
theorem dense_kingEvaluationPoints : Dense (kingEvaluationPoints b d e w) := by
  classical
  intro q
  rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure, ProjectiveSpectrum.mem_zeroLocus]
  intro a ha
  apply (q.asHomogeneousIdeal.isHomogeneous.mem_iff D).2
  intro i
  obtain ⟨f,hf⟩ := (DirectSum.decompose D a i).property
  rw [← hf]
  obtain ⟨j,hj,g,hg⟩ : ∃ (j : ℕ) (_ : 0 < j) (g : A j), DirectSum.of A j g ∉ q.asHomogeneousIdeal.toIdeal := by
    by_contra! hall
    apply q.not_irrelevant_le
    change (HomogeneousIdeal.irrelevant D).toIdeal ≤ _
    rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
    rintro _ ⟨_,⟨j,rfl⟩,_,⟨hj,rfl⟩,g,rfl⟩
    exact hall j hj g
  have hz : GradedMonoid.GMul.mul f g = (0 : A (i+j)) := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change f.val.val x * g.val.val x = 0
    by_cases h : g.val.val x = 0
    · simp [h]
    let p := kingPoint b w x ⟨j,hj,g,h⟩
    have hp : p ∈ kingEvaluationPoints b d e w := ⟨x,_,rfl⟩
    have hm := (ProjectiveSpectrum.mem_vanishingIdeal _ a).1 ha p hp
    have he := (p.asHomogeneousIdeal.isHomogeneous.mem_iff D).1 hm i
    rw [← hf] at he
    change kingEvaluation b w x (DirectSum.of A i f) = 0 at he
    rw [kingEvaluation_of] at he
    have hfx : f.val.val x = 0 := by simpa using congrArg (fun p : Polynomial k ↦ p.coeff i) he
    simp [hfx]
  have hm : DirectSum.of A i f * DirectSum.of A j g ∈ q.asHomogeneousIdeal.toIdeal := by
    rw [DirectSum.of_mul_of,hz,map_zero]
    exact q.asHomogeneousIdeal.toIdeal.zero_mem
  exact (q.isPrime.mem_or_mem hm).resolve_right hg

/-- Since evaluation points are closed and dense, at most one of them exists
exactly when the scheme has at most one closed point. -/
theorem subsingleton_closedPoints_iff_kingEvaluationPoints :
    Set.Subsingleton {p : ProjectiveSpectrum D | IsClosed ({p} : Set (ProjectiveSpectrum D))} ↔
      (kingEvaluationPoints b d e w).Subsingleton := by
  let S := kingEvaluationPoints b d e w
  have hclosed (p) (hp : p ∈ S) : IsClosed ({p} : Set (ProjectiveSpectrum D)) := by
    obtain ⟨x,h,rfl⟩ := hp
    exact isClosed_kingPoint b w x h
  refine ⟨fun h ↦ h.anti (fun p hp ↦ hclosed p hp),fun h ↦ ?_⟩
  have hc : IsClosed S := by
    rcases Set.subsingleton_iff_eq_empty_or_singleton.mp (show S.Subsingleton from h) with he | ⟨p,he⟩
    · rw [he]; exact isClosed_empty
    · have hp : p ∈ S := he.symm ▸ Set.mem_singleton p
      rw [he]; exact hclosed p hp
  have he := (dense_kingEvaluationPoints b d e w).closure_eq
  change closure S = Set.univ at he
  rw [hc.closure_eq] at he
  exact (show S.Subsingleton from h).anti (by rw [he]; exact Set.subset_univ _)

/-- Two evaluations on the same chart give distinct closed points whenever
the ratio of two forms of the same degree takes distinct values. -/
theorem not_subsingleton_closedPoints_of_ratio
    (x y : VertexRepresentation (k := k) d e) {m : ℕ} (hm : 0 < m)
    (f g : A m) (hx : g.val.val x ≠ 0) (hy : g.val.val y ≠ 0)
    (hsep : f.val.val x * g.val.val y ≠ f.val.val y * g.val.val x) :
    ¬ Set.Subsingleton {p : ProjectiveSpectrum D | IsClosed ({p} : Set (ProjectiveSpectrum D))} := by
  intro h
  let px := kingPoint b w x ⟨m, hm, g, hx⟩
  let py := kingPoint b w y ⟨m, hm, g, hy⟩
  have he : px = py := h (isClosed_kingPoint b w x _) (isClosed_kingPoint b w y _)
  let a : A m := (g.val.val x) • f - (f.val.val x) • g
  have ha : DirectSum.of A m a ∈ px.asHomogeneousIdeal.toIdeal := by
    change kingEvaluation b w x (DirectSum.of A m a) = 0
    rw [kingEvaluation_of]
    change Polynomial.monomial m (g.val.val x * f.val.val x - f.val.val x * g.val.val x) = 0
    simp [mul_comm]
  rw [he] at ha
  change kingEvaluation b w y (DirectSum.of A m a) = 0 at ha
  rw [kingEvaluation_of] at ha
  have hz := congrArg (fun p : Polynomial k ↦ p.coeff m) ha
  simp only [Polynomial.coeff_monomial_same, Polynomial.coeff_zero] at hz
  change g.val.val x * f.val.val y - f.val.val x * g.val.val y = 0 at hz
  exact hsep ((sub_eq_zero.mp hz).symm.trans (mul_comm _ _))

namespace SplitBasicVertices

variable [Module.Finite k R] [IsNoetherianRing R] (P : SplitBasicVertices k R I)

/-- The closed-point clause at a fixed dimension vector and projective weight
can be tested on homogeneous evaluations of actual representations. -/
theorem atMostOneKingClosedPoint_iff_evaluationPoints (g : ProjectiveClass R) :
    P.atMostOneKingClosedPoint b d g ↔
      (kingEvaluationPoints b d P.vertex (P.characterExponents g)).Subsingleton :=
  subsingleton_closedPoints_iff_kingEvaluationPoints b d P.vertex (P.characterExponents g)

end SplitBasicVertices

end EFiniteCharacterizations.VertexRepresentation
