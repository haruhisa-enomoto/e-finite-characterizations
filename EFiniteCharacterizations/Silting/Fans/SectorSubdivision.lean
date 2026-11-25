module

public import EFiniteCharacterizations.Presentations.StableRigidComparison
public import Mathlib.Basic.Real.Basic

/-!
# Recursive Stern–Brocot subdivision of ordered presilting sectors

Section 8 of the manuscript (Lemmas 8.1–8.2). Given presilting complexes `E, L` with
`Hom(E, L[1]) = 0`, repeatedly inserting a presilting representative of the mediant
class `[E] + [L]` strictly decreases `dim_k Hom(-, -[1])` in the reverse direction on
both subsectors (`exists_presilting_sector_cover_of_mediants`,
`exists_presilting_sector_cover`).
-/

@[expose] public section

namespace EFiniteCharacterizations

section RealModule

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The closed cone spanned by two vectors. -/
def sectorBetween (v w : V) : Set V :=
  {x | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a • v + b • w = x}

theorem sectorBetween_split (v w : V) :
    sectorBetween v w = sectorBetween v (v + w) ∪ sectorBetween (v + w) w := by
  ext x
  change (∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a • v + b • w = x) ↔ _
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    rcases le_total b a with h | h
    · left
      refine ⟨a - b, b, sub_nonneg.mpr h, hb, ?_⟩
      simp only [sub_smul, smul_add]
      abel
    · right
      refine ⟨a, b - a, ha, sub_nonneg.mpr h, ?_⟩
      simp only [sub_smul, smul_add]
      abel
  · rintro (⟨a, b, ha, hb, rfl⟩ | ⟨a, b, ha, hb, rfl⟩)
    · refine ⟨a + b, b, add_nonneg ha hb, hb, ?_⟩
      simp only [add_smul, smul_add]
      abel
    · refine ⟨a, a + b, ha, add_nonneg ha hb, ?_⟩
      simp only [add_smul, smul_add]
      abel

end RealModule

namespace TwoTerm

universe u

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The lattice mediants in the first `n` levels of the Stern–Brocot subdivision. -/
def sternBrocotMediants {G : Type*} [Add G] : ℕ → G → G → Set G
  | 0, _, _ => ∅
  | n + 1, v, w => insert (v + w)
      (sternBrocotMediants n v (v + w) ∪ sternBrocotMediants n (v + w) w)

/-- Coverage of just the indicated mediants gives a subdivision into at most
`2 ^ n` compatible sectors when the reverse shifted Hom has dimension at most `n`. -/
theorem exists_presilting_sector_cover_of_mediants (g : ProjectiveClass R →+ V)
    (n : ℕ) (E L : TwoTerm R) (hE : E.IsPresilting) (hL : L.IsPresilting)
    (hEL : E.shiftedHomFinrank k L = 0) (hLE : L.shiftedHomFinrank k E ≤ n)
    (hcovered : ∀ c ∈ sternBrocotMediants n E.projectiveClass L.projectiveClass,
      ∃ Z : TwoTerm R, Z.IsPresilting ∧ Z.projectiveClass = c) :
    ∃ s : List (TwoTerm R × TwoTerm R), s.length ≤ 2 ^ n ∧
      (∀ p ∈ s, (p.1.directSum p.2).IsPresilting) ∧
      sectorBetween (g E.projectiveClass) (g L.projectiveClass) =
        {x | ∃ p ∈ s, x ∈ sectorBetween (g p.1.projectiveClass) (g p.2.projectiveClass)} := by
  induction n generalizing E L with
  | zero =>
    refine ⟨[(E,L)], by simp, ?_, by ext; simp⟩
    intro p hp
    obtain rfl := List.mem_singleton.mp hp
    exact (isPresilting_directSum_iff k E L).2 ⟨hE, hL, hEL, Nat.eq_zero_of_le_zero hLE⟩
  | succ n ih =>
    by_cases hz : L.shiftedHomFinrank k E = 0
    · refine ⟨[(E,L)], by simpa using (Nat.one_le_two_pow : 1 ≤ 2 ^ (n + 1)), ?_, by ext; simp⟩
      intro p hp
      obtain rfl := List.mem_singleton.mp hp
      exact (isPresilting_directSum_iff k E L).2 ⟨hE, hL, hEL, hz⟩
    obtain ⟨Z, hZ, hclass⟩ := hcovered _ (Set.mem_insert ..)
    obtain ⟨hEZ, hZL, hZE, hLZ⟩ := shiftedHomFinrank_mediant_bounds k E L Z hE hL hZ hEL
      (Nat.pos_of_ne_zero hz) hclass
    obtain ⟨s, hs, hsp, hsc⟩ := ih E Z hE hZ hEZ (by omega) (by
      rw [hclass]
      exact fun c hc ↦ hcovered c (Set.mem_insert_of_mem _ (Or.inl hc)))
    obtain ⟨t, ht, htp, htc⟩ := ih Z L hZ hL hZL (by omega) (by
      rw [hclass]
      exact fun c hc ↦ hcovered c (Set.mem_insert_of_mem _ (Or.inr hc)))
    refine ⟨s ++ t, ?_, ?_, ?_⟩
    · rw [List.length_append, pow_succ]
      omega
    · intro p hp'
      exact (List.mem_append.mp hp').elim (hsp p) (htp p)
    · have hv : g Z.projectiveClass = g E.projectiveClass + g L.projectiveClass := by rw [hclass, map_add]
      rw [sectorBetween_split, ← hv, hsc, htc]
      ext x
      simp only [Set.mem_union, Set.mem_ofPred_eq, List.mem_append]
      constructor
      · rintro (⟨p, hp', hx⟩ | ⟨p, hp', hx⟩)
        · exact ⟨p, Or.inl hp', hx⟩
        · exact ⟨p, Or.inr hp', hx⟩
      · rintro ⟨p, hp' | hp', hx⟩
        · exact Or.inl ⟨p, hp', hx⟩
        · exact Or.inr ⟨p, hp', hx⟩

/-- A sector with one vanishing shifted Hom admits a finite cover by sectors
of compatible pairs. The reverse shifted Hom dimension bounds the depth. -/
theorem exists_presilting_sector_cover (hR : IsEFinite R) (g : ProjectiveClass R →+ V)
    (E L : TwoTerm R) (hE : E.IsPresilting) (hL : L.IsPresilting) (hEL : E.shiftedHomFinrank k L = 0) :
    ∃ s : List (TwoTerm R × TwoTerm R), s.length ≤ 2 ^ L.shiftedHomFinrank k E ∧
      (∀ p ∈ s, (p.1.directSum p.2).IsPresilting) ∧
      sectorBetween (g E.projectiveClass) (g L.projectiveClass) =
        {x | ∃ p ∈ s, x ∈ sectorBetween (g p.1.projectiveClass) (g p.2.projectiveClass)} :=
  exists_presilting_sector_cover_of_mediants k g _ E L hE hL hEL le_rfl (fun c _ ↦ hR c)

end TwoTerm

end EFiniteCharacterizations
