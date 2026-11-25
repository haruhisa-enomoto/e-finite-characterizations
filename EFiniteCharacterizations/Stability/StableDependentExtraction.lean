module

public import EFiniteCharacterizations.Stability.DependentSemibrick

/-! # Joint stabilization of a dependent semibrick -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.FamilyExtraction

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]

private abbrev SClass (R : Type u) [Ring R] := Skeleton (FGModuleCat.{u} R)
private noncomputable abbrev obj (x : SClass R) := (fromSkeleton _).obj x
private noncomputable abbrev len (x : SClass R) := FGModuleCat.moduleLength (obj x)

private structure Supported (s : Finset (SClass R)) : Prop where
  semi : IsSemibrick (C := FGModuleCat.{u} R) ↑s
  nonempty : s.Nonempty
  relation : ∃ c : SClass R → ℤ, (∀ x ∈ s, c x ≠ 0) ∧ ∑ x ∈ s, c x • GrothendieckGroup.of (obj x) = 0

omit [IsArtinianRing R] in
private theorem exists_supported_subset {s : Finset (SClass R)}
    (hs : IsSemibrick (C := FGModuleCat.{u} R) ↑s)
    (hd : ¬ LinearIndependent ℤ (fun x : s ↦ GrothendieckGroup.of (obj x.val))) :
    ∃ t ⊆ s, Supported t := by
  classical
  rw [Fintype.linearIndependent_iff] at hd
  push Not at hd
  obtain ⟨c, hc, i, hi⟩ := hd
  let a (x : SClass R) := if hx : x ∈ s then c ⟨x,hx⟩ else 0
  let t := s.filter fun x ↦ a x ≠ 0
  have ht : t ⊆ s := Finset.filter_subset _ _
  refine ⟨t, ht, hs.subset ht, ⟨i.val, Finset.mem_filter.mpr ⟨i.property, by simpa [a] using hi⟩⟩,
    a, fun x hx ↦ (Finset.mem_filter.mp hx).2, ?_⟩
  have hsum : ∑ x ∈ s, a x • GrothendieckGroup.of (obj x) = 0 := by
    rw [← Finset.sum_coe_sort s (fun x ↦ a x • GrothendieckGroup.of (obj x))]
    simpa [a] using hc
  exact (Finset.sum_subset ht (by intro x hx hn; simp [show a x = 0 by simpa [t,hx] using hn])).trans hsum

omit [IsArtinianRing R] in
private theorem Supported.erase_vanishing {s : Finset (SClass R)} (hs : Supported s) {p : SClass R}
    (hp : p ∈ s) [DecidableEq (SClass R)] (w : Weight (FGModuleCat.{u} R))
    (hw : ∀ x ∈ s.erase p, w.eval (obj x) = 0) : ∀ x ∈ s, w.eval (obj x) = 0 := by
  obtain ⟨c, hn, hz⟩ := hs.relation
  have he := congrArg w hz
  simp only [map_sum, map_zsmul, map_zero] at he
  rw [Finset.sum_eq_single p] at he
  · intro x hx
    by_cases h : x = p
    · subst x
      exact (mul_eq_zero.mp he).resolve_left (hn p hp)
    · exact hw x (Finset.mem_erase.mpr ⟨h,hx⟩)
  · intro x hx hxp
    rw [show w (GrothendieckGroup.of (obj x)) = 0 from hw x (Finset.mem_erase.mpr ⟨hxp,hx⟩), smul_zero]
  · simp [hp]

omit [IsArtinianRing R] in
private theorem Supported.dependent {s : Finset (SClass R)} (hs : Supported s) :
    ¬ LinearIndependent ℤ (fun x : s ↦ GrothendieckGroup.of (obj x.val)) := by
  classical
  intro hi
  obtain ⟨c, hn, hz⟩ := hs.relation
  obtain ⟨x, hx⟩ := hs.nonempty
  rw [← Finset.sum_coe_sort s (fun x ↦ c x • GrothendieckGroup.of (obj x))] at hz
  exact hn x hx (Fintype.linearIndependent_iff.mp hi (fun i ↦ c i.val) hz ⟨x,hx⟩)

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

/-- Failure of equal-class Hom produces an integrally dependent family of
bricks stable at a single integral projective weight. -/
theorem exists_jointly_stable_dependent_semibrick (h : ¬ EqualClassHom (FGModuleCat.{u} R)) :
    ∃ (s : Finset (Skeleton (FGModuleCat.{u} R))) (g : ProjectiveClass R),
      (s : Set _) ⊆ stableClasses (C := FGModuleCat.{u} R) (projectiveClassWeight k g) ∧
      ¬ LinearIndependent ℤ (fun x : s ↦ GrothendieckGroup.of ((fromSkeleton _).obj x.val)) := by
  classical
  obtain ⟨s₀, hs₀, hd₀⟩ := exists_dependent_semibrick h
  obtain ⟨t₀, _, ht₀⟩ := exists_supported_subset hs₀ hd₀
  let P (m : ℕ) := ∃ s : Finset (SClass R), Supported s ∧ ∀ x ∈ s, len x ≤ m
  have hex : ∃ m, P m := ⟨t₀.sup len, t₀, ht₀, fun _ hx ↦ Finset.le_sup hx⟩
  let m := Nat.find hex
  let top (s : Finset (SClass R)) := s.filter fun x ↦ len x = m
  let Q (n : ℕ) := ∃ s : Finset (SClass R), Supported s ∧ (∀ x ∈ s, len x ≤ m) ∧ (top s).card = n
  obtain ⟨s₁, hs₁, hm₁⟩ := Nat.find_spec hex
  have hq : ∃ n, Q n := ⟨_, s₁, hs₁, hm₁, rfl⟩
  obtain ⟨s, hs, hm, hcount⟩ := Nat.find_spec hq
  have hmax : s.sup len = m := le_antisymm (Finset.sup_le hm)
    (Nat.find_min' hex ⟨s, hs, fun _ hx ↦ Finset.le_sup hx⟩)
  obtain ⟨p, hp, hplen⟩ := Finset.exists_mem_eq_sup s hs.nonempty len
  have hpm : len p = m := hplen.symm.trans hmax
  rcases joint_weight_or_shorter_relation k s (s.erase p) (Finset.erase_subset _ _) hs.semi
      (hs.erase_vanishing hp) with hw | ⟨A, B, hr, hb⟩
  · obtain ⟨g, hg⟩ := hw
    exact ⟨s, g, hg, hs.dependent⟩
  exfalso
  obtain ⟨r, hsr, hbound, hdr⟩ := hr.exists_dependent_semibrick_below
  obtain ⟨t, htr, ht⟩ := exists_supported_subset hsr hdr
  have length_eq (Z : FGModuleCat.{u} R) : len (toSkeleton Z) = FGModuleCat.moduleLength Z :=
    FGModuleCat.moduleLength_eq_of_iso (fromSkeletonToSkeletonIso Z)
  have bound (Z : FGModuleCat.{u} R) (hz : Z ∈ A ∨ Z ∈ B) :
      toSkeleton Z ∈ s.erase p ∨ FGModuleCat.moduleLength Z < m := by
    rcases hb Z hz with h | ⟨j, hj, hlt⟩
    · exact Or.inl h
    · exact Or.inr (hlt.trans_le (hm j hj))
  have bound' (x) (hx : x ∈ t) : x ∈ s.erase p ∨ len x < m := by
    obtain ⟨Z, rfl, hz⟩ := hbound x (htr hx)
    rw [length_eq]
    rcases hz with hl | hr | ⟨Y, hY, hlt⟩
    · exact bound Z (Or.inl hl)
    · exact bound Z (Or.inr hr)
    · right
      rcases bound Y hY with hy | hy
      · exact hlt.trans_le ((length_eq Y) ▸ hm _ (Finset.mem_of_mem_erase hy))
      · exact hlt.trans hy
  have htm (x) (hx : x ∈ t) : len x ≤ m := (bound' x hx).elim
    (fun hy ↦ hm x (Finset.mem_of_mem_erase hy)) LT.lt.le
  have hsub : top t ⊆ (top s).erase p := by
    intro x hx
    obtain ⟨hxt, hxm⟩ := Finset.mem_filter.mp hx
    have hy := (bound' x hxt).resolve_right (by omega)
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1, Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hy, hxm⟩⟩
  have hlower := Nat.find_min' hq (show Q (top t).card from ⟨t, ht, htm, rfl⟩)
  have hlt := (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem (Finset.mem_filter.mpr ⟨hp,hpm⟩ : p ∈ top s))
  omega

end EFiniteCharacterizations.FamilyExtraction
