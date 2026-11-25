module

public import Mathlib.RingTheory.HahnSeries.Addition
public import Mathlib.Order.Zorn

/-! # Solving triangular linear equations on well-ordered series -/

@[expose] public section

namespace EFiniteCharacterizations
namespace HahnTriangular

variable {Γ k : Type*} [LinearOrder Γ] [Field k]

private def Prefix (x y : HahnSeries Γ k) : Prop :=
  ∀ g, x.coeff g ≠ 0 → ∀ b ≤ g, y.coeff b = x.coeff b

private instance : Std.Refl (Prefix (Γ := Γ) (k := k)) := ⟨fun _ _ _ _ _ ↦ rfl⟩

private theorem prefix_trans {x y z : HahnSeries Γ k} (h : Prefix x y) (h' : Prefix y z) :
    Prefix x z := by
  intro g hg b hb
  exact (h' g ((h g hg g le_rfl).symm ▸ hg) b hb).trans (h g hg b hb)

/-- A chain of partial series extended only above their existing supports
has a union with well-ordered support. -/
private theorem chain_union (C : Set (HahnSeries Γ k)) (hC : IsChain Prefix C) :
    ∃ u : HahnSeries Γ k, (∀ x ∈ C, Prefix x u) ∧
      ∀ g, u.coeff g ≠ 0 → ∃ x ∈ C, x.coeff g ≠ 0 := by
  classical
  let occurs (g : Γ) := ∃ x ∈ C, (x : HahnSeries Γ k).coeff g ≠ 0
  let coeff (g : Γ) := if h : occurs g then h.choose.coeff g else 0
  have same {x y : HahnSeries Γ k} (hx : x ∈ C) (hy : y ∈ C) {g b : Γ}
      (hg : x.coeff g ≠ 0) (hb : b ≤ g) (hb' : y.coeff b ≠ 0) : x.coeff b = y.coeff b := by
    rcases hC.total hx hy with h | h
    · exact (h g hg b hb).symm
    · exact h b hb' b le_rfl
  have agree {x : HahnSeries Γ k} (hx : x ∈ C) {g : Γ} (hg : x.coeff g ≠ 0)
      (b : Γ) (hb : b ≤ g) : coeff b = x.coeff b := by
    dsimp only [coeff]
    split_ifs with h
    · exact (same hx h.choose_spec.1 hg hb h.choose_spec.2).symm
    · exact (not_ne_iff.mp fun hn ↦ h ⟨x,hx,hn⟩).symm
  have occ {b : Γ} (hb : coeff b ≠ 0) : occurs b := by
    by_contra h
    exact hb (by simp [coeff,h])
  have wf : (Function.support coeff).IsWF := by
    rw [Set.isWF_iff_no_descending_seq]
    intro f hm hf
    obtain ⟨x,hx,h₀⟩ := occ (hf 0)
    apply Set.isWF_iff_no_descending_seq.mp x.isWF_support f hm
    intro n
    change x.coeff (f n) ≠ 0
    rw [← agree hx h₀ (f n) (hm.antitone (Nat.zero_le n))]
    exact hf n
  exact ⟨⟨coeff,wf.isPWO⟩,fun x hx _ hg ↦ agree hx hg,fun _ ↦ occ⟩

/-- Let T shift lowest exponents by an order isomorphism. If it respects
agreement through each cutoff and a monomial can realize any prescribed leading
coefficient at the shifted exponent, then T is surjective on Hahn series. -/
theorem surjective (T : HahnSeries Γ k →+ HahnSeries Γ k) (φ : Γ ≃o Γ)
    (causal : ∀ x y g, (∀ b ≤ g, (x : HahnSeries Γ k).coeff b = y.coeff b) →
      ∀ b ≤ φ g, (T x).coeff b = (T y).coeff b)
    (diagonal : ∀ g d, ∃ a : k, (T (HahnSeries.single g a)).coeff (φ g) = d ∧
      ∀ b < φ g, (T (HahnSeries.single g a)).coeff b = 0) : Function.Surjective T := by
  classical
  intro v
  let Partial (x : HahnSeries Γ k) := ∀ g, x.coeff g ≠ 0 → ∀ b ≤ φ g, (T x).coeff b = v.coeff b
  let A := {x : HahnSeries Γ k // Partial x}
  let r (x y : A) := Prefix x.val y.val
  let : Std.Refl r := ⟨fun _ _ _ _ _ ↦ rfl⟩
  have bound (c : Set A) (hc : IsChain r c) : ∃ u : A, ∀ x ∈ c, r x u := by
    have chain : IsChain Prefix (Subtype.val '' c) := by
      rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ _
      exact hc.total hx hy
    obtain ⟨u,hu,hcover⟩ := chain_union _ chain
    refine ⟨⟨u,?_⟩,fun x hx ↦ hu _ ⟨x,hx,rfl⟩⟩
    intro g hg b hb
    obtain ⟨_,⟨x,hx,rfl⟩,hxg⟩ := hcover g hg
    exact (causal u x.val g (hu _ ⟨x,hx,rfl⟩ g hxg) b hb).trans (x.property g hxg b hb)
  obtain ⟨x,hmax⟩ := exists_maximal_of_chains_bounded bound (fun h h' ↦ prefix_trans h h')
  refine ⟨x.val,?_⟩
  by_contra hn
  let err := v - T x.val
  have nonempty : err.support.Nonempty :=
    HahnSeries.support_nonempty_iff.2 (sub_ne_zero.mpr (Ne.symm hn))
  let b := err.isWF_support.min nonempty
  have hb : err.coeff b ≠ 0 := err.isWF_support.min_mem nonempty
  have prior {p : Γ} (hp : p < b) : (T x.val).coeff p = v.coeff p := by
    apply Eq.symm
    apply sub_eq_zero.mp
    by_contra h
    exact hp.not_ge (err.isWF_support.min_le _ h)
  let g := φ.symm b
  have shift : φ g = b := φ.apply_symm_apply _
  obtain ⟨a,ha,ha'⟩ := diagonal g (err.coeff b)
  rw [shift] at ha ha'
  have fresh (p : Γ) (hp : x.val.coeff p ≠ 0) : p < g := by
    by_contra! le
    have h := x.property p hp b (shift ▸ φ.monotone le)
    exact hb (sub_eq_zero.mpr h.symm)
  have hzero : x.val.coeff g = 0 := by
    by_contra h
    exact (fresh g h).false
  have hane : a ≠ 0 := by
    rintro rfl
    exact hb (ha.symm.trans (by simp))
  let y := x.val + HahnSeries.single g a
  have hy (p : Γ) (hp : p ≤ b) : (T y).coeff p = v.coeff p := by
    change (T (x.val + _)).coeff p = _
    rw [map_add,HahnSeries.coeff_add]
    rcases hp.eq_or_lt with rfl | hlt
    · rw [ha]
      change _ + (v.coeff _ - _) = _
      exact add_sub_cancel _ _
    · rw [ha' p hlt,add_zero,prior hlt]
  have valid : Partial y := by
    intro p hp l hl
    apply hy l
    apply hl.trans
    rw [← shift]
    apply φ.monotone
    by_contra! h
    have hxp : x.val.coeff p = 0 := not_ne_iff.mp (fun h' ↦ (fresh p h').not_gt h)
    exact hp (by simp [y,hxp,HahnSeries.coeff_single_of_ne h.ne'])
  have extxy : r x ⟨y,valid⟩ := by
    intro p hp l hl
    simp [y,HahnSeries.coeff_single_of_ne (hl.trans_lt (fresh p hp)).ne]
  have back := hmax ⟨y,valid⟩ extxy
  have hyg : y.coeff g ≠ 0 := by simpa [y,hzero] using hane
  exact hyg ((back g hyg g le_rfl).symm.trans hzero)

end HahnTriangular
end EFiniteCharacterizations
