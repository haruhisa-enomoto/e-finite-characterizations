module

public import EFiniteCharacterizations.Presentations.BlockDifferential
public import EFiniteCharacterizations.LinearAlgebra.PencilCoefficients
public import Mathlib.CategoryTheory.Preadditive.Comma

/-! # Finite jets of a pencil of differentials -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits

namespace EFiniteCharacterizations.PencilJet
set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

/-- The terms of the pencil modulo t to the power n+1, with the constant
coefficient in the last summand. -/
noncomputable def terms (X : C) : ℕ → C
  | 0 => X
  | n+1 => terms X n ⊞ X

noncomputable def head (X : C) : (n : ℕ) → X ⟶ terms X n
  | 0 => 𝟙 X
  | _+1 => biprod.inr

/-- Multiplication by the pencil d + t v on the truncated polynomial module. -/
noncomputable def differential {X Y : C} (d v : X ⟶ Y) :
    (n : ℕ) → terms X n ⟶ terms Y n
  | 0 => d
  | n+1 => blockDifferential (differential d v n) d (v ≫ head Y n)

private noncomputable def column {X Y : C} (a : ℕ → (X ⟶ Y)) (i : ℕ) :
    (n : ℕ) → X ⟶ terms Y n
  | 0 => a i
  | n+1 => biprod.lift (column a (i+1) n) (a i)

private noncomputable def row {X Y : C} (a : ℕ → (X ⟶ Y)) : (n : ℕ) → terms X n ⟶ Y
  | 0 => a 0
  | n+1 => biprod.desc (row a n) (a (n+1))

private theorem head_row {X Y : C} (a : ℕ → (X ⟶ Y)) (n : ℕ) :
    head X n ≫ row a n = a n := by cases n <;> simp [head, row]

private theorem column_differential {X Y S T : C} (u : S ⟶ T) (d v : X ⟶ Y)
    (a : ℕ → (S ⟶ X)) (b : ℕ → (T ⟶ Y)) (hr : ∀ i, a (i+1) ≫ d + a i ≫ v = u ≫ b (i+1))
    (i n : ℕ) (p : S ⟶ Y) (hp : a i ≫ d + p = u ≫ b i) :
    column a i n ≫ differential d v n + p ≫ head Y n = u ≫ column b i n := by
  induction n generalizing i p with
  | zero => simpa [column, differential, head] using hp
  | succ n ih =>
    change _ ≫ blockDifferential _ _ _ + p ≫ biprod.inr = u ≫ biprod.lift _ _
    apply biprod.hom_ext
    · have h := ih (i+1) (a i ≫ v) (hr i)
      simpa [column, blockDifferential, biprod.lift_desc, Preadditive.add_comp, Category.assoc] using h
    · simpa [column, Preadditive.add_comp, Category.assoc] using hp

private theorem differential_row {X Y S T : C} (u : S ⟶ T) (d v : X ⟶ Y)
    (c : ℕ → (X ⟶ S)) (b : ℕ → (Y ⟶ T)) (hz : c 0 ≫ u = d ≫ b 0)
    (hr : ∀ i, c (i+1) ≫ u = d ≫ b (i+1) + v ≫ b i) (n : ℕ) :
    row c n ≫ u = differential d v n ≫ row b n := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    change biprod.desc _ _ ≫ u = blockDifferential _ _ _ ≫ biprod.desc _ _
    apply biprod.hom_ext'
    · simpa [Category.assoc] using ih
    · simpa [blockDifferential, biprod.lift_desc, Category.assoc, head_row, add_comm] using hr n

private theorem column_row {S X : C} (a : ℕ → (S ⟶ X)) (c : ℕ → (X ⟶ X)) (i n : ℕ)
    (h : ∀ j ≤ n, a (i+j) ≫ c (n-j) = a (i+j)) :
    column a i n ≫ row c n = ∑ j ∈ Finset.range (n+1), a (i+j) := by
  induction n generalizing i with
  | zero => simpa [column, row] using h 0 (by omega)
  | succ n ih =>
    rw [column, row, biprod.lift_desc, ih (i+1)]
    · have hhead := h 0 (by omega)
      rw [show a i ≫ c (n+1) = a i by simpa using hhead]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Finset.sum_range_succ' (fun j ↦ a (i+j)) (n+1)).symm
    · intro j hj
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (j+1) (by omega)

private theorem column_row_eq_id {X : C} (a c : ℕ → (X ⟶ X)) {m l : ℕ}
    (ha : ∀ i, m ≤ i → a i = 0) (hs : ∑ i ∈ Finset.range m, a i = 𝟙 X)
    (hc : ∀ i, l ≤ i → c i = 𝟙 X) :
    column a 0 (m+l) ≫ row c (m+l) = 𝟙 X := by
  rw [column_row]
  · simp only [zero_add]
    rw [← hs]
    exact (Finset.sum_subset (Finset.range_mono (by omega : m ≤ m+l+1))
      (fun j _ hj ↦ ha j (by simpa using hj))).symm
  · intro j _
    by_cases hj : m ≤ j
    · simp [ha j hj]
    · simp [hc _ (by omega : l ≤ m+l-j)]

variable (k : Type*) [Field k] [Linear k C] {X Y : C}
  [Module.Finite k (X ⟶ X)] [Module.Finite k (Y ⟶ Y)] [Module.Finite k (X ⟶ Y)]

/-- A rigid differential on the same terms is a chain-level retract of a
finite jet at the special fiber of the line joining the two differentials. -/
theorem exists_retract (u d : X ⟶ Y) (hu : Function.Surjective (boundaryLinear k u u)) :
    ∃ n : ℕ, Nonempty (Retract (Arrow.mk u) (Arrow.mk (differential d (u-d) n))) := by
  let v := u - d
  let fst := LinearMap.fst k (X ⟶ X) (Y ⟶ Y)
  let snd := LinearMap.snd k (X ⟶ X) (Y ⟶ Y)
  let B := (Linear.rightComp k X v).comp fst
  let D := - (Linear.leftComp k Y v).comp snd
  have eq₁ : boundaryLinear k u d + B = boundaryLinear k u u := by
    apply LinearMap.ext
    intro x
    change x.1 ≫ d - u ≫ x.2 + x.1 ≫ (u - d) = x.1 ≫ u - u ≫ x.2
    rw [Preadditive.comp_sub]
    abel
  have eq₂ : boundaryLinear k d u + D = boundaryLinear k u u := by
    apply LinearMap.ext
    intro x
    change x.1 ≫ u - d ≫ x.2 + -((u-d) ≫ x.2) = x.1 ≫ u - u ≫ x.2
    rw [Preadditive.sub_comp]
    abel
  have hid : boundaryLinear k u u (𝟙 X, 𝟙 Y) = 0 := by simp
  obtain ⟨m, a, ha, hsa, ha₀, hra⟩ := exists_finite_pencil_coefficients
    (boundaryLinear k u d) B (eq₁ ▸ hu) _ (eq₁ ▸ hid)
  obtain ⟨l, c, hc, hc₀, hrc⟩ := exists_stable_pencil_coefficients
    (boundaryLinear k d u) D (eq₂ ▸ hu) _ (eq₂ ▸ hid)
  have hf := column_differential u d v (fun j ↦ (a j).1) (fun j ↦ (a j).2)
    (fun j ↦ by
      have h := hra j
      change (a (j+1)).1 ≫ d - u ≫ (a (j+1)).2 + (a j).1 ≫ v = 0 at h
      rw [← sub_eq_zero]
      convert h using 1
      abel) 0 (m+l) 0 (by simpa [boundaryLinear_apply] using sub_eq_zero.mp ha₀)
  have hg := differential_row u d v (fun j ↦ (c j).1) (fun j ↦ (c j).2)
    (sub_eq_zero.mp hc₀) (fun j ↦ by
      have h := hrc j
      change (c (j+1)).1 ≫ u - d ≫ (c (j+1)).2 + -(v ≫ (c j).2) = 0 at h
      rw [← sub_eq_zero]
      convert h using 1
      abel) (m+l)
  let i := Arrow.homMk (f := Arrow.mk u) (g := Arrow.mk (differential d v (m+l)))
    (column (fun j ↦ (a j).1) 0 _) (column (fun j ↦ (a j).2) 0 _) (by simpa using hf)
  let r := Arrow.homMk (f := Arrow.mk (differential d v (m+l))) (g := Arrow.mk u)
    (row (fun j ↦ (c j).1) _) (row (fun j ↦ (c j).2) _) hg
  refine ⟨m+l, ⟨⟨i,r,?_⟩⟩⟩
  apply Arrow.hom_ext
  · change column (fun j ↦ (a j).1) 0 (m+l) ≫ row (fun j ↦ (c j).1) (m+l) = 𝟙 X
    exact column_row_eq_id _ _ (fun j hj ↦ congrArg Prod.fst (ha j hj))
      (by simpa only [fst, map_sum, LinearMap.fst_apply] using congrArg fst hsa) (fun j hj ↦ congrArg Prod.fst (hc j hj))
  · change column (fun j ↦ (a j).2) 0 (m+l) ≫ row (fun j ↦ (c j).2) (m+l) = 𝟙 Y
    exact column_row_eq_id _ _ (fun j hj ↦ congrArg Prod.snd (ha j hj))
      (by simpa only [snd, map_sum, LinearMap.snd_apply] using congrArg snd hsa) (fun j hj ↦ congrArg Prod.snd (hc j hj))

end EFiniteCharacterizations.PencilJet
