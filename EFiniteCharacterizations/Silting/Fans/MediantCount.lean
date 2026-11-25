module

public import EFiniteCharacterizations.Silting.Fans.SectorSubdivision
public import Mathlib.Data.Set.Card

/-! # Counting the lattice points in a finite Stern–Brocot subdivision -/

@[expose] public section
namespace EFiniteCharacterizations.TwoTerm

variable {G : Type*} [AddCommGroup G]

theorem sternBrocotMediants_finite (n : ℕ) (v w : G) : (sternBrocotMediants n v w).Finite := by
  induction n generalizing v w with
  | zero => exact Set.finite_empty
  | succ n ih => exact ((ih v (v+w)).union (ih (v+w) w)).insert _

theorem sternBrocotMediants_card_le (n : ℕ) (v w : G) :
    (sternBrocotMediants n v w).ncard ≤ 2 ^ n - 1 := by
  induction n generalizing v w with
  | zero => simp [sternBrocotMediants]
  | succ n ih =>
    let s := sternBrocotMediants n v (v+w)
    let t := sternBrocotMediants n (v+w) w
    change (insert (v+w) (s ∪ t)).ncard ≤ _
    have hs : s.ncard ≤ _ := ih v (v+w)
    have ht : t.ncard ≤ _ := ih (v+w) w
    have hu := Set.ncard_union_le s t
    have hi := Set.ncard_insert_le (v+w) (s ∪ t)
    have hp : 0 < 2 ^ n := pow_pos (by decide) _
    rw [pow_succ]
    omega

private theorem left_coeff (a b : ℕ) (v w : G) :
    a • v + b • (v+w) = (a+b) • v + b • w := by simp [add_nsmul, nsmul_add, add_assoc]

private theorem right_coeff (a b : ℕ) (v w : G) :
    a • (v+w) + b • w = a • v + (a+b) • w := by simp [add_nsmul, nsmul_add, add_assoc]

private theorem positive_coefficients {n : ℕ} {v w x : G} (h : x ∈ sternBrocotMediants n v w) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a • v + b • w = x := by
  induction n generalizing v w with
  | zero => exact False.elim h
  | succ n ih =>
    rcases h with rfl | h | h
    · exact ⟨1,1,by decide,by decide,by simp⟩
    · obtain ⟨a,b,ha,hb,he⟩ := ih h
      exact ⟨a+b,b,by omega,hb,(left_coeff ..).symm.trans he⟩
    · obtain ⟨a,b,ha,hb,he⟩ := ih h
      exact ⟨a,a+b,ha,by omega,(right_coeff ..).symm.trans he⟩

private theorem card_of_unique_coefficients (n : ℕ) (v w : G)
    (hu : ∀ a b c d : ℕ, a • v + b • w = c • v + d • w → a = c ∧ b = d) :
    (sternBrocotMediants n v w).ncard + 1 = 2 ^ n := by
  induction n generalizing v w with
  | zero => simp [sternBrocotMediants]
  | succ n ih =>
    let s := sternBrocotMediants n v (v+w)
    let t := sternBrocotMediants n (v+w) w
    have hs := ih v (v+w) (by
      intro a b c d he
      rw [left_coeff, left_coeff] at he
      obtain ⟨h₁,h₂⟩ := hu _ _ _ _ he
      omega)
    have ht := ih (v+w) w (by
      intro a b c d he
      rw [right_coeff, right_coeff] at he
      obtain ⟨h₁,h₂⟩ := hu _ _ _ _ he
      omega)
    have left {x : G} (hx : x ∈ s) : ∃ a b : ℕ, b < a ∧ a • v + b • w = x := by
      obtain ⟨a,b,ha,_,he⟩ := positive_coefficients hx
      exact ⟨a+b,b,by omega,(left_coeff ..).symm.trans he⟩
    have right {x : G} (hx : x ∈ t) : ∃ a b : ℕ, a < b ∧ a • v + b • w = x := by
      obtain ⟨a,b,_,hb,he⟩ := positive_coefficients hx
      exact ⟨a,a+b,by omega,(right_coeff ..).symm.trans he⟩
    have hd : Disjoint s t := Set.disjoint_left.mpr fun _ hx hy ↦ by
      obtain ⟨a,b,hab,h₁⟩ := left hx
      obtain ⟨c,d,hcd,h₂⟩ := right hy
      obtain ⟨rfl,rfl⟩ := hu _ _ _ _ (h₁.trans h₂.symm)
      omega
    have hn : v+w ∉ s ∪ t := by
      have diag (a b : ℕ) (h : a • v + b • w = v+w) := hu a b 1 1 (by simpa using h)
      rintro (hx | hx)
      · obtain ⟨a,b,hlt,h⟩ := left hx
        obtain ⟨rfl,rfl⟩ := diag a b h
        omega
      · obtain ⟨a,b,hlt,h⟩ := right hx
        obtain ⟨rfl,rfl⟩ := diag a b h
        omega
    have fs : s.Finite := sternBrocotMediants_finite ..
    have ft : t.Finite := sternBrocotMediants_finite ..
    change (insert (v+w) (s ∪ t)).ncard + 1 = _
    change s.ncard + 1 = _ at hs
    change t.ncard + 1 = _ at ht
    rw [Set.ncard_insert_of_notMem hn (fs.union ft), Set.ncard_union_eq hd fs ft, pow_succ]
    omega

/-- For independent endpoint classes every one of the potential mediants is distinct. -/
theorem sternBrocotMediants_card_of_independent (n : ℕ) (v w : G)
    (hi : LinearIndependent ℤ ![v,w]) : (sternBrocotMediants n v w).ncard = 2 ^ n - 1 := by
  have hu (a b c d : ℕ) (he : a • v + b • w = c • v + d • w) : a = c ∧ b = d := by
    have eq := Fintype.linearIndependent_iffₛ.mp hi (![(a : ℤ),b]) (![(c : ℤ),d]) (by
      simpa [Fin.sum_univ_two] using he)
    exact ⟨by exact_mod_cast (show (a : ℤ) = c from eq 0), by exact_mod_cast (show (b : ℤ) = d from eq 1)⟩
  have := card_of_unique_coefficients n v w hu
  omega

end EFiniteCharacterizations.TwoTerm
