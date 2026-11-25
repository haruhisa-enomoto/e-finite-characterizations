module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Farkas's lemma over an ordered field

Ported from `ExtensionClosedString.Mesh.Farkas` in the extension-closed string formalization.

A finite system `b ≤ A x` is either solvable, or there is `y ≥ 0` with `yᵀ A = 0` and
`yᵀ b > 0` (`farkas`). The proof is Fourier–Motzkin elimination of the last variable.
-/

@[expose] public section

set_option autoImplicit false

namespace EFiniteCharacterizations.Farkas

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The system `b ≤ A x` is solvable. -/
def Feasible {ι : Type*} [Fintype ι] {n : ℕ} (A : ι → Fin n → K) (b : ι → K) : Prop :=
  ∃ x : Fin n → K, ∀ i, b i ≤ ∑ j, A i j * x j

/-- A Farkas certificate for the infeasibility of `b ≤ A x`. -/
def Certificate {ι : Type*} [Fintype ι] {n : ℕ} (A : ι → Fin n → K) (b : ι → K) : Prop :=
  ∃ y : ι → K, (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, y i * A i j = 0) ∧ 0 < ∑ i, y i * b i

theorem farkas_zero {ι : Type*} [Fintype ι] (A : ι → Fin 0 → K) (b : ι → K) :
    Feasible A b ∨ Certificate A b := by
  classical
  by_cases h : ∀ i, b i ≤ 0
  · left; exact ⟨fun j ↦ j.elim0, fun i ↦ by simpa using h i⟩
  · right
    push Not at h
    obtain ⟨i₀, hi₀⟩ := h
    refine ⟨Pi.single i₀ 1, fun i ↦ ?_, fun j ↦ j.elim0, ?_⟩
    · by_cases hi : i = i₀
      · subst hi; simp
      · simp [Pi.single_apply, hi]
    · rw [Finset.sum_eq_single i₀ (fun i _ hi ↦ by simp [Pi.single_apply, hi]) (by simp)]
      simpa using hi₀

section Step

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (A : ι → Fin (n + 1) → K) (b : ι → K)

/-- The rows of the eliminated system. -/
abbrev ElimRow := {i // A i (Fin.last n) = 0} ⊕ ({i // 0 < A i (Fin.last n)} × {i // A i (Fin.last n) < 0})

open Classical in
noncomputable instance : Fintype (ElimRow A) := inferInstance

/-- The multipliers of the eliminated rows. -/
def coef : ElimRow A → ι → K
  | .inl z => fun i ↦ if i = z.1 then 1 else 0
  | .inr pq => fun i ↦ (if i = pq.1.1 then -A pq.2.1 (Fin.last n) else 0) +
      (if i = pq.2.1 then A pq.1.1 (Fin.last n) else 0)

theorem coef_nonneg (r : ElimRow A) (i : ι) : 0 ≤ coef A r i := by
  rcases r with z | ⟨p, q⟩
  · simp only [coef]; split_ifs <;> norm_num
  · simp only [coef]
    have h1 := p.2
    have h2 := q.2
    split_ifs <;> linarith

theorem sum_coef (r : ElimRow A) (f : ι → K) :
    ∑ i, coef A r i * f i = match r with
      | .inl z => f z.1
      | .inr pq => -A pq.2.1 (Fin.last n) * f pq.1.1 + A pq.1.1 (Fin.last n) * f pq.2.1 := by
  rcases r with z | ⟨p, q⟩
  · simp [coef]
  · simp only [coef, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]

theorem sum_coef_last (r : ElimRow A) : ∑ i, coef A r i * A i (Fin.last n) = 0 := by
  rw [sum_coef]
  rcases r with z | ⟨p, q⟩
  · exact z.2
  · simp only; ring

/-- The eliminated system. -/
def elimA : ElimRow A → Fin n → K := fun r j ↦ ∑ i, coef A r i * A i j.castSucc

def elimB : ElimRow A → K := fun r ↦ ∑ i, coef A r i * b i

theorem sum_comb (y : ElimRow A → K) (f : ι → K) :
    ∑ i, (∑ r, y r * coef A r i) * f i = ∑ r, y r * ∑ i, coef A r i * f i := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  ring

theorem certificate_of_elim (h : Certificate (elimA A) (elimB A b)) : Certificate A b := by
  obtain ⟨y, hy0, hyA, hyb⟩ := h
  refine ⟨fun i ↦ ∑ r, y r * coef A r i, fun i ↦ Finset.sum_nonneg fun r _ ↦
    mul_nonneg (hy0 r) (coef_nonneg A r i), fun j ↦ ?_, ?_⟩
  · rw [sum_comb A y (fun i ↦ A i j)]
    induction j using Fin.lastCases with
    | last => simp [sum_coef_last]
    | cast j => exact hyA j
  · rw [sum_comb A y b]; exact hyb

theorem feasible_of_elim (h : Feasible (elimA A) (elimB A b)) : Feasible A b := by
  classical
  obtain ⟨x', hx'⟩ := h
  set a : ι → K := fun i ↦ A i (Fin.last n) with ha
  set s : ι → K := fun i ↦ ∑ j, A i j.castSucc * x' j with hs
  have hrow : ∀ r : ElimRow A, elimB A b r ≤ ∑ i, coef A r i * s i := by
    intro r
    have := hx' r
    simp only [elimA, elimB] at this
    calc ∑ i, coef A r i * b i ≤ ∑ j, (∑ i, coef A r i * A i j.castSucc) * x' j := this
      _ = ∑ i, coef A r i * s i := by
        simp only [hs, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        ring
  let L : ι → K := fun p ↦ (b p - s p) / a p
  let U : ι → K := fun q ↦ (b q - s q) / a q
  have hLU : ∀ p q, 0 < a p → a q < 0 → L p ≤ U q := by
    intro p q hp hq
    have h := hrow (.inr (⟨p, hp⟩, ⟨q, hq⟩))
    simp only [elimB] at h
    rw [sum_coef, sum_coef] at h
    simp only at h
    simp only [L, U]
    rw [le_div_iff_of_neg hq]
    have e : a p * ((b p - s p) / a p * a q) = a q * (b p - s p) := by
      field_simp
    have key : a p * (b q - s q) ≤ a p * ((b p - s p) / a p * a q) := by
      rw [e]; simp only [ha] at h ⊢; linarith
    exact le_of_mul_le_mul_left key hp
  let Ps := Finset.univ.filter fun i ↦ 0 < a i
  let Ns := Finset.univ.filter fun i ↦ a i < 0
  let t : K := if hP : Ps.Nonempty then Ps.sup' hP L else if hN : Ns.Nonempty then Ns.inf' hN U else 0
  have hLt : ∀ p, 0 < a p → L p ≤ t := by
    intro p hp
    have hP : Ps.Nonempty := ⟨p, by simp [Ps, hp]⟩
    simp only [t, dif_pos hP]
    exact Finset.le_sup' L (by simp [Ps, hp])
  have htU : ∀ q, a q < 0 → t ≤ U q := by
    intro q hq
    by_cases hP : Ps.Nonempty
    · simp only [t, dif_pos hP]
      exact Finset.sup'_le _ _ fun p hp ↦ hLU p q (by simpa [Ps] using hp) hq
    · have hN : Ns.Nonempty := ⟨q, by simp [Ns, hq]⟩
      simp only [t, dif_neg hP, dif_pos hN]
      exact Finset.inf'_le U (by simp [Ns, hq])
  refine ⟨Fin.snoc x' t, fun i ↦ ?_⟩
  have hsum : ∑ j, A i j * (Fin.snoc x' t : Fin (n + 1) → K) j = s i + a i * t := by
    rw [Fin.sum_univ_castSucc]
    simp [hs, ha]
  rw [hsum]
  rcases lt_trichotomy (a i) 0 with hq | hz | hp
  · have := htU i hq
    simp only [U] at this
    rw [le_div_iff_of_neg hq] at this
    linarith
  · have h := hrow (.inl ⟨i, hz⟩)
    simp only [elimB] at h
    rw [sum_coef, sum_coef] at h
    simp only at h
    rw [hz, zero_mul, add_zero]
    exact h
  · have := hLt i hp
    simp only [L] at this
    rw [div_le_iff₀ hp] at this
    linarith

end Step

/-- **Farkas's lemma**: `b ≤ A x` is solvable, or there is `y ≥ 0` with `yᵀ A = 0` and
`yᵀ b > 0`. -/
theorem farkas : ∀ (n : ℕ) {ι : Type*} [Fintype ι] (A : ι → Fin n → K) (b : ι → K),
    Feasible A b ∨ Certificate A b := by
  intro n
  induction n with
  | zero => intro ι _ A b; exact farkas_zero A b
  | succ n ih =>
      intro ι _ A b
      classical
      rcases ih (elimA A) (elimB A b) with h | h
      · exact Or.inl (feasible_of_elim A b h)
      · exact Or.inr (certificate_of_elim A b h)

theorem not_feasible_and_certificate {ι : Type*} [Fintype ι] {n : ℕ} (A : ι → Fin n → K)
    (b : ι → K) : ¬ (Feasible A b ∧ Certificate A b) := by
  rintro ⟨⟨x, hx⟩, ⟨y, hy0, hyA, hyb⟩⟩
  have h1 : ∑ i, y i * b i ≤ ∑ i, y i * ∑ j, A i j * x j :=
    Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hx i) (hy0 i)
  have h2 : ∑ i, y i * ∑ j, A i j * x j = 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have := hyA j
    calc ∑ i, y i * (A i j * x j) = (∑ i, y i * A i j) * x j := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ ↦ by ring
      _ = 0 := by rw [this, zero_mul]
  linarith

/-- Either a weight vanishes on the prescribed rows and is negative on the
test rows, or a nonzero nonnegative combination of test rows is a signed
combination of the prescribed rows. -/
theorem separation_or_relation {n : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    (B : I → Fin n → K) (U : J → Fin n → K) :
    (∃ w : Fin n → K, (∀ i, ∑ t, B i t * w t = 0) ∧ ∀ j, ∑ t, U j t * w t < 0) ∨
    ∃ (a : J → K) (c : I → K), (∀ j, 0 ≤ a j) ∧ 0 < ∑ j, a j ∧
      ∀ t, ∑ j, a j * U j t = ∑ i, c i * B i t := by
  classical
  let A : (J ⊕ (I ⊕ I)) → Fin n → K := Sum.elim (fun j t ↦ - U j t)
    (Sum.elim B (fun i t ↦ - B i t))
  let b : (J ⊕ (I ⊕ I)) → K := Sum.elim (fun _ ↦ 1) (fun _ ↦ 0)
  rcases farkas n A b with ⟨w, hw⟩ | ⟨y, hy, hA, hb⟩
  · left
    refine ⟨w, fun i ↦ ?_, fun j ↦ ?_⟩
    · have hp := hw (.inr (.inl i))
      have hn := hw (.inr (.inr i))
      simp [A, b, Finset.sum_neg_distrib] at hp hn
      exact le_antisymm hn hp
    · have hn := hw (.inl j)
      simp [A, b, Finset.sum_neg_distrib] at hn
      linarith
  · right
    refine ⟨fun j ↦ y (.inl j), fun i ↦ y (.inr (.inl i)) - y (.inr (.inr i)),
      fun j ↦ hy _, ?_, fun t ↦ ?_⟩
    · simpa [b, Fintype.sum_sum_type] using hb
    · have he := hA t
      simp [A, Fintype.sum_sum_type, Finset.sum_neg_distrib] at he
      simp only [sub_mul, Finset.sum_sub_distrib]
      linarith only [he]

end EFiniteCharacterizations.Farkas
