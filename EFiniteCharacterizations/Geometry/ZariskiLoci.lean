module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Zariski-open loci in affine coordinates -/

@[expose] public section

namespace EFiniteCharacterizations

open MvPolynomial TopologicalSpace

variable {k σ X : Type*} [Field k]

/-- The Zariski topology on a parameter set given by its affine coordinates. -/
@[instance_reducible] noncomputable def coordinateZariski (c : X → σ → k) : TopologicalSpace X :=
  TopologicalSpace.induced (fun x ↦ pointToPoint (k := k) (c x)) inferInstance

theorem coordinateZariski_noetherian [Finite σ] (c : X → σ → k) :
    @NoetherianSpace X (coordinateZariski c) := by
  let _ := coordinateZariski c
  exact (show Topology.IsInducing (fun x ↦ pointToPoint (k := k) (c x)) from ⟨rfl⟩).noetherianSpace

theorem coordinateZariski_isOpen_ne_zero (c : X → σ → k) (p : MvPolynomial σ k) :
    @IsOpen X (coordinateZariski c) {x | eval (c x) p ≠ 0} := by
  refine ⟨PrimeSpectrum.basicOpen p,PrimeSpectrum.isOpen_basicOpen,?_⟩
  ext x
  change p ∉ vanishingIdeal k {c x} ↔ _
  rw [mem_vanishingIdeal_singleton_iff]
  rfl

/-- Injectivity of a rectangular polynomial matrix is open, including for
zero-dimensional source or target. A left inverse at a point gives a square
determinant whose nonvanishing certifies injectivity near that point. -/
theorem coordinateZariski_isOpen_injective_matrix (c : X → σ → k)
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n (MvPolynomial σ k)) :
    @IsOpen X (coordinateZariski c) {x | Function.Injective (A.map (eval (c x))).mulVec} := by
  classical
  let _ := coordinateZariski c
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  let M := A.map (eval (c x))
  obtain ⟨L,hL⟩ := M.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hx)
  let B := LinearMap.toMatrix' L
  have hBM : B * M = 1 := by
    simpa [B,LinearMap.toMatrix'_comp,← Matrix.toLin'_apply'] using congrArg LinearMap.toMatrix' hL
  let p := ((B.map (C : k →+* MvPolynomial σ k)) * A).det
  have hp (y : X) : eval (c y) p = (B * A.map (eval (c y))).det := by
    dsimp only [p]
    rw [RingHom.map_det]
    change ((B.map C * A).map (eval (c y))).det = _
    rw [Matrix.map_mul]
    congr 2
    ext i j
    simp [Matrix.map_apply]
  refine ⟨_,?_,coordinateZariski_isOpen_ne_zero c p,?_⟩
  · intro y hy v w he
    have hd : (B * A.map (eval (c y))).det ≠ 0 := (hp y) ▸ hy
    apply Matrix.mulVec_injective_of_det_ne_zero hd
    simp only [← Matrix.mulVec_mulVec,he]
  · change eval (c x) p ≠ 0
    rw [hp]
    change (B * M).det ≠ 0
    simp [hBM]

/-- For two tuples of action matrices depending polynomially on the same
parameters, the locus on which every intertwiner is zero is open. -/
theorem coordinateZariski_isOpen_zero_intertwiners (c : X → σ → k)
    {a m n : Type*} [Fintype a] [Fintype m] [Fintype n]
    (L : a → Matrix m m (MvPolynomial σ k)) (R : a → Matrix n n (MvPolynomial σ k)) :
    @IsOpen X (coordinateZariski c) {x | ∀ T : Matrix m n k,
      (∀ j, (L j).map (eval (c x)) * T = T * (R j).map (eval (c x))) → T = 0} := by
  classical
  let A : Matrix (a × m × n) (m × n) (MvPolynomial σ k) := fun (j,i,h) (s,t) ↦
    (if t = h then L j i s else 0) - (if s = i then R j t h else 0)
  have kernel (x : X) (v : m × n → k) (j : a) (i : m) (h : n) :
      ((A.map (eval (c x))).mulVec v) (j,i,h) =
      ((L j).map (eval (c x)) * (Matrix.of (Function.curry v)) - (Matrix.of (Function.curry v)) * (R j).map (eval (c x))) i h := by
    change (∑ q : m × n, eval (c x) ((if q.2 = h then L j i q.1 else 0) - (if q.1 = i then R j q.2 h else 0)) * v q) = _
    simp [Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.map_apply, apply_ite (eval (c x)), mul_sub, Finset.sum_sub_distrib, mul_ite, mul_comm]
  convert coordinateZariski_isOpen_injective_matrix c A using 1
  ext x
  change (∀ T : Matrix m n k, _ → T = 0) ↔ Function.Injective (A.map (eval (c x))).mulVec
  rw [← Matrix.coe_mulVecLin,← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  constructor
  · intro hx v hv
    have ht := hx (Function.curry v) (fun j ↦ Matrix.ext fun i h ↦ sub_eq_zero.mp
      ((kernel x v j i h).symm.trans (congrFun hv (j,i,h))))
    exact funext fun (i,h) ↦ congrFun (congrFun ht i) h
  · intro hx T ht
    let v := Function.uncurry T
    have hz : (A.map (eval (c x))).mulVec v = 0 := by
      funext (j,i,h)
      rw [kernel]
      change ((L j).map (eval (c x)) * T - T * (R j).map (eval (c x))) i h = 0
      simp [ht]
    exact Matrix.ext fun i h ↦ congrFun (hx v hz) (i,h)

/-- In a finite-coordinate parameter space, only finitely many values of a
classifying map can have nonempty open fibers. This applies to the map sending
a representation to its isomorphism class. -/
theorem coordinateZariski_finite_open_fibers [Finite σ] (c : X → σ → k)
    {I : Type*} (f : X → I) (s : Set I) (represented : s ⊆ Set.range f)
    (ho : ∀ i ∈ s, @IsOpen X (coordinateZariski c) (f ⁻¹' {i})) : s.Finite := by
  classical
  let _ := coordinateZariski c
  let _ := coordinateZariski_noetherian c
  let U (i : s) : Set X := f ⁻¹' {i.val}
  obtain ⟨t,ht⟩ := (NoetherianSpace.isCompact (⋃ i, U i)).elim_finite_subcover U
    (fun i ↦ ho _ i.property) (by rfl)
  have hall : ∀ i : s, i ∈ t := by
    intro i
    obtain ⟨x,hx⟩ := represented i.property
    have hi : x ∈ U i := hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.1 (ht (Set.mem_iUnion.2 ⟨i,hi⟩))
    obtain ⟨hj',hxj⟩ := Set.mem_iUnion.1 hj
    have he : j = i := Subtype.ext ((show f x = j.val from hxj).symm.trans hx)
    exact he ▸ hj'
  let _ : Fintype s := ⟨t,hall⟩
  exact Set.toFinite s

end EFiniteCharacterizations
