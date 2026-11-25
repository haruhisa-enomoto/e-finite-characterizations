module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.Option
public import Mathlib.Algebra.Order.Group.PiLex

/-! # A bi-invariant order on a finitely generated free group -/

@[expose] public section

noncomputable section
namespace EFiniteCharacterizations.FreeGroupBiorder
open Monoid Polynomial
open scoped Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private abbrev Mat (ι : Type*) := Matrix (Option ι) (Option ι) ℤ

/-- Rank-one matrices with a distinguished row. The extra column guarantees
that each one is nonzero, even with only one generator. -/
private def block (i j : ι) (z : ℤ) : Mat ι :=
  Matrix.of fun r c ↦ if r = some i ∧ c ≠ some j then z else 0

private theorem block_mul (i j l m : ι) (z w : ℤ) :
    block i j z * block l m w = if l = j then 0 else block i m (z*w) := by
  ext r c
  rw [Matrix.mul_apply,Finset.sum_eq_single (some l)]
  · by_cases h : l = j <;> by_cases hr : r = some i <;> by_cases hc : c = some m <;>
      simp [block,h,hr,hc]
  · intro a _ ha
    simp [block,ha]
  · simp

omit [Fintype ι] in
private theorem block_add (i j : ι) (z w : ℤ) :
    block i j (z+w) = block i j z + block i j w := by
  ext r c
  by_cases h : r = some i ∧ c ≠ some j <;> simp [block,h]

private abbrev exponent (x : FreeGroup Unit) :=
  ((FreeGroup.mulEquivIntOfUnique (α := Unit)) x).toAdd

/-- The cyclic factor with label i acts by 1 + tA, where A has square zero. -/
private def factor (i : ι) : FreeGroup Unit →* (Mat ι)[X] where
  toFun x := 1 + monomial 1 (block i i (exponent x))
  map_one' := by simp [exponent,block]; rfl
  map_mul' x y := by
    have add : exponent (x*y) = exponent x + exponent y := congrArg Multiplicative.toAdd
      ((FreeGroup.mulEquivIntOfUnique (α := Unit)).map_mul x y)
    simp [add,block_add,add_mul,mul_add,monomial_mul_monomial,block_mul,add_comm,add_left_comm]

private abbrev ρ : CoprodI (fun _ : ι ↦ FreeGroup Unit) →* (Mat ι)[X] := CoprodI.lift (factor (ι := ι))

/-- The highest coefficient of a nonempty reduced product is nonzero.
Its row and its excluded column are determined by the first and last labels. -/
private theorem word_top {i j : ι} (w : CoprodI.NeWord (fun _ : ι ↦ FreeGroup Unit) i j) :
    ∃ (d : ℕ) (z : ℤ), 0 < d ∧ z ≠ 0 ∧ (ρ w.prod).natDegree ≤ d ∧
      (ρ w.prod).coeff d = block i j z := by
  induction w with
  | @singleton i x hx =>
    rw [CoprodI.NeWord.prod_singleton,CoprodI.lift_of]
    have hn : exponent x ≠ 0 := fun h ↦ hx ((FreeGroup.mulEquivIntOfUnique (α := Unit)).injective
      (by simpa using congrArg Multiplicative.ofAdd h))
    refine ⟨1,_,by decide,hn,?_,?_⟩
    · exact natDegree_add_le_of_degree_le (by simp) (natDegree_monomial_le ..)
    · simp [factor,coeff_one]
  | @append i j l m u h v hu hv =>
    obtain ⟨d,z,hd,hz,hdu,hcu⟩ := hu
    obtain ⟨n,a,hn,ha,hdv,hcv⟩ := hv
    rw [CoprodI.NeWord.append_prod,map_mul]
    refine ⟨d+n,z*a,by omega,mul_ne_zero hz ha,natDegree_mul_le_of_le hdu hdv,?_⟩
    simp only [coeff_mul_add_eq_of_natDegree_le hdu hdv,hcu,hcv,block_mul,h.symm,↓reduceIte]

private theorem faithful : Function.Injective (ρ (ι := ι)) := by
  classical
  apply (injective_iff_map_eq_one _).mpr
  rw [(CoprodI.Word.equiv).forall_congr_left]
  intro w hw
  change ρ w.prod = 1 at hw
  change w.prod = 1
  by_cases hz : w = CoprodI.Word.empty
  · simp [hz]
  obtain ⟨i,j,v,rfl⟩ := CoprodI.NeWord.of_word w hz
  obtain ⟨d,z,hd,hn,_,hc⟩ := word_top v
  change ρ v.prod = 1 at hw
  simp only [hw,coeff_one,hd.ne',↓reduceIte] at hc
  exact (hn (by simpa [block] using congrArg (fun b : Mat ι ↦ b (some i) none) hc.symm)).elim

private abbrev representation : FreeGroup ι →* (Mat ι)[X] :=
  ρ.comp (freeGroupEquivCoprodI.toMonoidHom)

private theorem coeff_zero (a : FreeGroup ι) : (representation a).coeff 0 = 1 := by
  have all (x : CoprodI (fun _ : ι ↦ FreeGroup Unit)) : (ρ x).coeff 0 = 1 := by
    induction x using CoprodI.induction_on with
    | one => simp
    | of i x => simp [ρ,factor]
    | mul x y hx hy => simp [coeff_mul,hx,hy]
  exact all _

private abbrev Index (ι : Type*) [Fintype ι] := Fin (Fintype.card (Option ι))
private abbrev OrderedMat (ι : Type*) [Fintype ι] := Lex (Index ι → Lex (Index ι → ℤ))

private def matKey (A : Mat ι) : OrderedMat ι :=
  let e := (Fintype.equivFin (Option ι)).symm
  toLex (fun i ↦ toLex fun j ↦ A (e i) (e j))

omit [DecidableEq ι] in
private theorem matKey_injective : Function.Injective (matKey (ι := ι)) := by
  intro a b h
  ext i j
  let e := Fintype.equivFin (Option ι)
  have eq := congrArg (fun M : OrderedMat ι ↦ ofLex (ofLex M (e i)) (e j)) h
  simpa [matKey,e] using eq

private def key (a : FreeGroup ι) : Lex (ℕ → OrderedMat ι) :=
  toLex (fun n ↦ matKey ((representation a).coeff n))

private theorem key_injective : Function.Injective (key (ι := ι)) := by
  intro a b h
  apply freeGroupEquivCoprodI.injective
  apply faithful
  apply Polynomial.ext
  intro n
  exact matKey_injective (congrArg (fun f : Lex (ℕ → OrderedMat ι) ↦ ofLex f n) h)

private theorem coeff_mul_of_lower_zero {A B : (Mat ι)[X]} (ha : A.coeff 0 = 1) {n : ℕ}
    (hb : ∀ j < n, B.coeff j = 0) :
    (A*B).coeff n = B.coeff n ∧ (B*A).coeff n = B.coeff n := by
  constructor
  · rw [coeff_mul,Finset.sum_eq_single (0,n)]
    · simp [ha]
    · rintro ⟨i,j⟩ hij hne
      rw [Finset.mem_antidiagonal] at hij
      have lt : j < n := by
        by_contra! h
        exact hne (Prod.ext (by dsimp at hij ⊢; omega) (by dsimp at hij ⊢; omega))
      simp [hb j lt]
    · simp
  · rw [coeff_mul,Finset.sum_eq_single (n,0)]
    · simp [ha]
    · rintro ⟨i,j⟩ hij hne
      rw [Finset.mem_antidiagonal] at hij
      have lt : i < n := by
        by_contra! h
        exact hne (Prod.ext (by dsimp at hij ⊢; omega) (by dsimp at hij ⊢; omega))
      simp [hb i lt]
    · simp

private theorem key_lt_of_differences {a b u v : FreeGroup ι} (n : ℕ)
    (lower : ∀ m < n, (representation a).coeff m = (representation b).coeff m)
    (lt : matKey ((representation a).coeff n) < matKey ((representation b).coeff n))
    (equal : ∀ m ≤ n, (representation v).coeff m - (representation u).coeff m =
      (representation b).coeff m - (representation a).coeff m) : key u < key v := by
  refine ⟨n,fun m hm ↦ ?_,?_⟩
  · have e := equal m hm.le
    rw [lower m hm,sub_self,sub_eq_zero] at e
    exact congrArg matKey e.symm
  · apply sub_pos.mp
    have e := congrArg matKey (equal n le_rfl)
    change matKey _ - matKey _ = matKey _ - matKey _ at e
    exact e.symm ▸ sub_pos.mpr lt

/-- Comparing at the lowest degree where the two polynomials differ is
invariant under multiplication on either side: every group element has
constant coefficient the identity. -/
private theorem translate_lt {a b : FreeGroup ι} (h : key a < key b) (c : FreeGroup ι) :
    key (c*a) < key (c*b) ∧ key (a*c) < key (b*c) := by
  obtain ⟨n,hn,hlt⟩ := h
  have lower (m : ℕ) (hm : m < n) := matKey_injective (hn m hm)
  have diffs (m : ℕ) (hm : m ≤ n) := coeff_mul_of_lower_zero (coeff_zero c) (n := m)
    (B := representation b - representation a) (fun j hj ↦ by rw [coeff_sub]; exact sub_eq_zero.mpr (lower j (hj.trans_le hm)).symm)
  constructor
  · apply key_lt_of_differences n lower hlt
    intro m hm
    simpa only [map_mul,mul_sub,coeff_sub] using (diffs m hm).1
  · apply key_lt_of_differences n lower hlt
    intro m hm
    simpa only [map_mul,sub_mul,coeff_sub] using (diffs m hm).2

omit [DecidableEq ι] in
/-- Every finitely generated free group admits a linear order invariant under
left and right multiplication. -/
theorem exists_biorder (ι : Type*) [Fintype ι] :
    ∃ _ : LinearOrder (FreeGroup ι), MulLeftMono (FreeGroup ι) ∧ MulRightMono (FreeGroup ι) := by
  classical
  let o := LinearOrder.lift' (key (ι := ι)) key_injective
  let : LinearOrder (FreeGroup ι) := o
  refine ⟨o,⟨fun c a b h ↦ ?_⟩,⟨fun c a b h ↦ ?_⟩⟩
  · rcases h.eq_or_lt with rfl | h
    · rfl
    · exact (translate_lt h c).1.le
  · rcases h.eq_or_lt with rfl | h
    · rfl
    · exact (translate_lt h c).2.le

end EFiniteCharacterizations.FreeGroupBiorder
