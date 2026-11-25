module

public import EFiniteCharacterizations.Geometry.KingSemiInvariants

/-! # Evaluation at a representation in the King projective spectrum -/

@[expose] public section

open scoped DirectSum
open DirectSum
universe u
namespace EFiniteCharacterizations.VertexRepresentation

variable {k R I J : Type u} [Field k] [Ring R] [Algebra k R]
    [Fintype I] [DecidableEq I] [Fintype J]
    (b : Module.Basis J k R) {d : I → ℕ} {e : I → R} (w : I → ℤ)
    (x : VertexRepresentation (k := k) d e)

local notation "A" => KingPiece b d e w
local notation "D" => kingGrading b d e w

noncomputable def evalPiece (m : ℕ) : A m →+ Polynomial k where
  toFun f := Polynomial.monomial m (f.val.val x)
  map_zero' := by simp
  map_add' f g := (Polynomial.monomial m).map_add _ _

/-- Evaluation retains the degree as a polynomial monomial. -/
noncomputable def kingEvaluation : KingSemiInvariantRing b d e w →+* Polynomial k :=
  DirectSum.toSemiring (evalPiece b w x)
    (by change Polynomial.monomial 0 1 = 1; simp)
    (fun {i j} f g ↦ by
      change Polynomial.monomial (i+j) (f.val.val x * g.val.val x) = _
      exact (Polynomial.monomial_mul_monomial _ _ _ _).symm)

theorem kingEvaluation_of (i : ℕ) (f : A i) :
    kingEvaluation b w x (DirectSum.of A i f) = Polynomial.monomial i (f.val.val x) :=
  DirectSum.toSemiring_of _ _ _ i f

theorem kingEvaluation_component (a : KingSemiInvariantRing b d e w) (i : ℕ) :
    kingEvaluation b w x (DirectSum.decompose D a i).val =
      Polynomial.monomial i ((kingEvaluation b w x a).coeff i) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of j f =>
    have hm : DirectSum.of A j f ∈ D j := ⟨f,rfl⟩
    by_cases h : j = i
    · subst j
      rw [decompose_of_mem_same D hm, kingEvaluation_of, Polynomial.coeff_monomial_same]
    · rw [decompose_of_mem_ne D hm h, map_zero, kingEvaluation_of, Polynomial.coeff_monomial,
        ite_eq_right h, map_zero]
  | add a c ha hc =>
    rw [decompose_add, (kingEvaluation b w x).map_add a c, Polynomial.coeff_add, (Polynomial.monomial i).map_add]
    change kingEvaluation b w x ((DirectSum.decompose D a i).val + (DirectSum.decompose D c i).val) = _
    rw [(kingEvaluation b w x).map_add,ha,hc]

/-- The homogeneous prime consisting of the forms vanishing at x. -/
noncomputable def kingEvaluationIdeal : HomogeneousIdeal D :=
  ⟨RingHom.ker (kingEvaluation b w x), fun i _ ha ↦ by
    change kingEvaluation b w x _ = 0
    rw [kingEvaluation_component, (RingHom.mem_ker.mp ha)]
    simp⟩

/-- A positive-degree form nonzero at x makes the evaluation prime relevant. -/
noncomputable def kingPoint (h : ∃ (m : ℕ) (_ : 0 < m) (f : A m), f.val.val x ≠ 0) :
    ProjectiveSpectrum D where
  asHomogeneousIdeal := kingEvaluationIdeal b w x
  isPrime := RingHom.ker_isPrime _
  not_irrelevant_le hi := by
    obtain ⟨m,hm,f,hf⟩ := h
    have he := hi (HomogeneousIdeal.mem_irrelevant_of_mem D hm (show DirectSum.of A m f ∈ D m from ⟨f,rfl⟩))
    change kingEvaluation b w x (DirectSum.of A m f) = 0 at he
    rw [kingEvaluation_of] at he
    exact hf (by simpa using congrArg (fun p : Polynomial k ↦ p.coeff m) he)

/-- Changing vertex bases leaves the homogeneous evaluation ideal unchanged. -/
theorem kingEvaluationIdeal_smul (G : BaseChange k d) :
    kingEvaluationIdeal b w (G • x) = kingEvaluationIdeal b w x := by
  apply HomogeneousIdeal.toIdeal_injective
  ext a
  rw [(kingEvaluationIdeal b w (G • x)).isHomogeneous.mem_iff D,
      (kingEvaluationIdeal b w x).isHomogeneous.mem_iff D]
  apply forall_congr'
  intro i
  obtain ⟨f,hf⟩ := (DirectSum.decompose D a i).property
  rw [← hf]
  change kingEvaluation b w (G • x) (DirectSum.of A i f) = 0 ↔
    kingEvaluation b w x (DirectSum.of A i f) = 0
  rw [kingEvaluation_of,kingEvaluation_of]
  have law := f.property G⁻¹ x
  rw [inv_inv] at law
  have mon (c : k) : Polynomial.monomial i c = 0 ↔ c = 0 :=
    ⟨fun hh ↦ by simpa using congrArg (fun p : Polynomial k ↦ p.coeff i) hh,
      fun hh ↦ by rw [hh,map_zero]⟩
  rw [mon,mon,law]
  simp

private noncomputable def constantForm (c : k) : A 0 :=
  ⟨algebraMap k (coordinateAlgebra b d e) c, fun _ _ ↦ by simp⟩

/-- The evaluation point is closed. Any relevant homogeneous prime containing
the evaluation kernel omits a positive-degree form. Comparing powers of that
form with any other form of nonzero value forces the latter to be omitted too. -/
theorem isClosed_kingPoint (h : ∃ (m : ℕ) (_ : 0 < m) (f : A m), f.val.val x ≠ 0) :
    IsClosed ({kingPoint b w x h} : Set (ProjectiveSpectrum D)) := by
  let p := kingPoint b w x h
  apply isClosed_of_closure_subset
  intro q hq
  have hpq := (ProjectiveSpectrum.le_iff_mem_closure D p q).2 hq
  have hle : p.asHomogeneousIdeal.toIdeal ≤ q.asHomogeneousIdeal.toIdeal := hpq
  have hex : ∃ (j : ℕ) (_ : 0 < j) (g : A j), DirectSum.of A j g ∉ q.asHomogeneousIdeal.toIdeal := by
    by_contra! hall
    apply q.not_irrelevant_le
    change (HomogeneousIdeal.irrelevant D).toIdeal ≤ q.asHomogeneousIdeal.toIdeal
    rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
    rintro _ ⟨_,⟨j,rfl⟩,_,⟨hj,rfl⟩,g,rfl⟩
    exact hall j hj g
  obtain ⟨j,hj,g,hg⟩ := hex
  let G := DirectSum.of A j g
  have hrev : q.asHomogeneousIdeal.toIdeal ≤ p.asHomogeneousIdeal.toIdeal := by
    intro a ha
    apply (p.asHomogeneousIdeal.isHomogeneous.mem_iff D).2
    intro i
    obtain ⟨f,hf⟩ := (DirectSum.decompose D a i).property
    rw [← hf]
    have hm := (q.asHomogeneousIdeal.isHomogeneous.mem_iff D).1 ha i
    rw [← hf] at hm
    change kingEvaluation b w x (DirectSum.of A i f) = 0
    rw [kingEvaluation_of]
    by_contra hn
    have hv : f.val.val x ≠ 0 := fun h₀ ↦ hn (by rw [h₀,map_zero])
    let c := (g.val.val x) ^ i / (f.val.val x) ^ j
    let C := DirectSum.of A 0 (constantForm b w (d := d) (e := e) c)
    let F := DirectSum.of A i f
    have he : G ^ i - C * F ^ j ∈ p.asHomogeneousIdeal.toIdeal := by
      change kingEvaluation b w x (G ^ i - C * F ^ j) = 0
      simp only [G,C,F,map_sub,map_pow,map_mul,kingEvaluation_of]
      change (Polynomial.monomial j (g.val.val x)) ^ i -
        Polynomial.monomial 0 c * (Polynomial.monomial i (f.val.val x)) ^ j = 0
      simp [Polynomial.monomial_pow,c,hv,Nat.mul_comm]
    have hm' : C * F ^ j ∈ q.asHomogeneousIdeal.toIdeal :=
      q.asHomogeneousIdeal.toIdeal.mul_mem_left C (q.asHomogeneousIdeal.toIdeal.pow_mem_of_mem hm j hj)
    have hg' : G ^ i ∈ q.asHomogeneousIdeal.toIdeal := by
      simpa only [sub_add_cancel] using q.asHomogeneousIdeal.toIdeal.add_mem (hle he) hm'
    exact hg (q.isPrime.mem_of_pow_mem _ hg')
  exact Set.mem_singleton_iff.mpr (le_antisymm (show q ≤ p from hrev) hpq)

end EFiniteCharacterizations.VertexRepresentation
