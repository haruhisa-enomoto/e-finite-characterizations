module

public import EFiniteCharacterizations.Geometry.KingDeterminants

/-! # Regular functions on a principal King chart -/

@[expose] public section

universe u
namespace EFiniteCharacterizations.VertexRepresentation

variable {k R I J : Type u} [Field k] [Ring R] [Algebra k R]
    [Fintype I] [DecidableEq I] [Fintype J]
    {b : Module.Basis J k R} {d : I → ℕ} {e : I → R} {w : I → ℤ}

local notation "X" => VertexRepresentation (k := k) d e
local notation "A" => coordinateAlgebra b d e

/-- Functions represented on the chart by a polynomial divided by a power
of its defining form. Values outside the chart are immaterial. -/
def chartFunctions (g : KingPiece b d e w 1) : Subalgebra k (X → k) where
  carrier := {v | ∃ (n : ℕ) (p : A), ∀ x, g.val.val x ≠ 0 → p.val x = g.val.val x ^ n * v x}
  algebraMap_mem' c := ⟨0, algebraMap k A c, fun x _ ↦ by simp⟩
  mul_mem' := by
    rintro f v ⟨n,p,hp⟩ ⟨m,q,hq⟩
    refine ⟨n+m,p*q,fun x hx ↦ ?_⟩
    change p.val x * q.val x = _ ^ (n+m) * (f x * v x)
    rw [hp x hx,hq x hx,pow_add]; ring
  add_mem' := by
    rintro f v ⟨n,p,hp⟩ ⟨m,q,hq⟩
    refine ⟨n+m,g.val^m*p + g.val^n*q,fun x hx ↦ ?_⟩
    change g.val.val x ^ m * p.val x + g.val.val x ^ n * q.val x =
      _ ^ (n+m) * (f x + v x)
    rw [hp x hx,hq x hx,pow_add]; ring

omit [Fintype J] in
theorem regular_mem_chartFunctions (g : KingPiece b d e w 1) (p : A) :
    p.val ∈ chartFunctions g := ⟨0,p,fun _ _ ↦ by simp⟩

omit [Fintype J] in
theorem inv_mem_chartFunctions (g : KingPiece b d e w 1) :
    (fun x ↦ (g.val.val x)⁻¹) ∈ chartFunctions g := ⟨1,1,fun x hx ↦ by simp [hx]⟩

omit [Fintype J] in
/-- The entries of an inverse presentation matrix are regular on its
determinant chart. -/
theorem inverse_entry_mem_chartFunctions {N : Type*} [Fintype N] [DecidableEq N]
    (g : KingPiece b d e w 1) (M : Matrix N N A) (hg : M.det = g.val) (i j : N) :
    (fun x ↦ (M.map (fun p ↦ p.val x))⁻¹ i j) ∈ chartFunctions g := by
  refine ⟨1,M.adjugate i j,fun x hx ↦ ?_⟩
  let ev := (Pi.evalRingHom (fun _ : X ↦ k) x).comp (coordinateAlgebra b d e).val.toRingHom
  have hd : (M.map ev).det = g.val.val x := (ev.map_det M).symm.trans (congrArg ev hg)
  have ha := congrArg (fun B : Matrix N N k ↦ B i j) (ev.map_adjugate M)
  change ev (M.adjugate i j) = g.val.val x ^ 1 * ((M.map ev)⁻¹ i j)
  change ev (M.adjugate i j) = (M.map ev).adjugate i j at ha
  rw [ha,Matrix.inv_def,hd]
  simp [Ring.inverse_eq_inv, hx]

omit [Fintype J] in
/-- Two points separated on an invariant chart are separated by a ratio of homogeneous forms. -/
theorem exists_separating_forms_of_chartFunction (g : KingPiece b d e w 1)
    {v : X → k} (hv : v ∈ chartFunctions g)
    (hinv : ∀ (G : BaseChange k d) x, g.val.val x ≠ 0 → v (G⁻¹ • x) = v x)
    {x y : X} (hx : g.val.val x ≠ 0) (hy : g.val.val y ≠ 0) (hxy : v x ≠ v y) :
    ∃ (m : ℕ), 0 < m ∧ ∃ f q : KingPiece b d e w m,
      q.val.val x ≠ 0 ∧ q.val.val y ≠ 0 ∧
        f.val.val x * q.val.val y ≠ f.val.val y * q.val.val x := by
  obtain ⟨n,p,hp⟩ := hv
  have hg (G : BaseChange k d) (z : X) := g.property G z
  simp only [pow_one] at hg
  let f : KingPiece b d e w (n+1) := ⟨g.val*p,by
    intro G z
    change g.val.val (G⁻¹ • z) * p.val (G⁻¹ • z) = _ ^ (n+1) * (g.val.val z * p.val z)
    by_cases hz : g.val.val z = 0
    · simp [hg,hz]
    · have hz' : g.val.val (G⁻¹ • z) ≠ 0 := by rw [hg]; exact mul_ne_zero (Units.ne_zero _) hz
      rw [hp _ hz',hp _ hz,hg,hinv G z hz,mul_pow,pow_succ]; ring⟩
  let q : KingPiece b d e w (n+1) := ⟨g.val^(n+1),by
    intro G z
    change g.val.val (G⁻¹ • z) ^ (n+1) = _ ^ (n+1) * g.val.val z ^ (n+1)
    rw [hg,mul_pow]⟩
  refine ⟨n+1, Nat.zero_lt_succ n, f, q, pow_ne_zero _ hx, pow_ne_zero _ hy, ?_⟩
  change g.val.val x * p.val x * g.val.val y ^ (n+1) ≠ g.val.val y * p.val y * g.val.val x ^ (n+1)
  rw [hp _ hx,hp _ hy,pow_succ,pow_succ]
  intro he
  apply hxy
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero (n+1) hx) (pow_ne_zero (n+1) hy))
  simp only [pow_succ]
  linear_combination he

theorem not_subsingleton_closedPoints_of_chartFunction (g : KingPiece b d e w 1)
    {v : X → k} (hv : v ∈ chartFunctions g)
    (hinv : ∀ (G : BaseChange k d) x, g.val.val x ≠ 0 → v (G⁻¹ • x) = v x)
    {x y : X} (hx : g.val.val x ≠ 0) (hy : g.val.val y ≠ 0) (hxy : v x ≠ v y) :
    ¬ Set.Subsingleton {p : ProjectiveSpectrum (kingGrading b d e w) |
      IsClosed ({p} : Set (ProjectiveSpectrum (kingGrading b d e w)))} := by
  obtain ⟨m,hm,f,q,hx',hy',hs⟩ := exists_separating_forms_of_chartFunction g hv hinv hx hy hxy
  exact not_subsingleton_closedPoints_of_ratio b d e w x y hm f q hx' hy' hs

end EFiniteCharacterizations.VertexRepresentation
