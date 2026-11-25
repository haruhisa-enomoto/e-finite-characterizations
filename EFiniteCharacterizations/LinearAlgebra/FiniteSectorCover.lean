module

public import EFiniteCharacterizations.Silting.Fans.SectorSubdivision
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Covering a plane by sectors with finitely many boundary directions -/

@[expose] public section

open FiniteDimensional Module

namespace EFiniteCharacterizations

/-- Suppose that finitely many directions meet every open linear half-plane.
If each direction has a compatible neighbor on each side of its line, then
the compatible sectors cover every nonzero point of the plane. -/
theorem mem_sector_of_finite_directions {V : Type*} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    (hd : Module.finrank ℝ V = 2) (s : Set V) (hs : s.Finite) (C : V → V → Prop)
    (start : ∀ f : V →ₗ[ℝ] ℝ, f ≠ 0 → ∃ v ∈ s, 0 < f v)
    (step : ∀ v ∈ s, ∀ f : V →ₗ[ℝ] ℝ, f ≠ 0 → f v = 0 → ∃ w ∈ s, C v w ∧ 0 < f w)
    (g : V) (hg : g ≠ 0) : ∃ v w, C v w ∧ g ∈ sectorBetween v w := by
  classical
  obtain ⟨z,hz⟩ : ∃ z : V, z ∉ Submodule.span ℝ {g} := by
    by_contra! h
    have he : Submodule.span ℝ {g} = ⊤ := top_unique (fun z _ ↦ h z)
    have hb := finrank_span_le_card (R := ℝ) ({g} : Set V)
    rw [he,finrank_top,hd] at hb
    simp at hb
  let F : Fin 2 → V := ![z,g]
  have hF : LinearIndependent ℝ F := linearIndependent_fin2.2 ⟨hg,fun a ha ↦
    hz (Submodule.mem_span_singleton.2 ⟨a,ha⟩)⟩
  let B := basisOfLinearIndependentOfCardEqFinrank hF (by simp [hd])
  have hB (i : Fin 2) : B i = F i := congrFun (coe_basisOfLinearIndependentOfCardEqFinrank ..) i
  let x := B.coord 1
  let y := B.coord 0
  have xg : x g = 1 := by change B.coord 1 (F 1) = 1; rw [← hB]; simp
  have yg : y g = 0 := by change B.coord 0 (F 1) = 0; rw [← hB]; simp
  have hy : y ≠ 0 := by
    intro he
    have h := DFunLike.congr_fun he (B 0)
    simp [y] at h
  obtain ⟨u,hus,hu⟩ := start y hy
  let S := hs.toFinset.filter fun v ↦ 0 < y v
  obtain ⟨v,hv,hmax⟩ := S.exists_max_image (fun v ↦ x v / y v) ⟨u,Finset.mem_filter.2 ⟨hs.mem_toFinset.2 hus,hu⟩⟩
  obtain ⟨hvs,hyv⟩ := Finset.mem_filter.1 hv
  let m := x v / y v
  let l := x - m • y
  have hl (a : V) : l a = x a - m * y a := rfl
  have hvg : l g = 1 := by simp [hl,xg,yg]
  obtain ⟨w,hws,hvw,hw⟩ := step v (hs.mem_toFinset.1 hvs) l
    (fun he ↦ by simp [he] at hvg) (by rw [hl]; simp [m,hyv.ne'])
  have hyw : y w ≤ 0 := by
    by_contra! h
    have hh := hmax w (Finset.mem_filter.2 ⟨hs.mem_toFinset.2 hws,h⟩)
    have := (div_le_iff₀ h).1 hh
    rw [hl] at hw
    linarith
  let b := (l w)⁻¹
  let a := -y w / y v * b
  have hb : 0 < b := inv_pos.2 hw
  have ha : 0 ≤ a := mul_nonneg (div_nonneg (neg_nonneg.2 hyw) hyv.le) hb.le
  refine ⟨v,w,hvw,a,b,ha,hb.le,?_⟩
  apply B.repr.injective
  ext i
  fin_cases i
  · change y (a • v + b • w) = y g
    rw [yg,map_add,map_smul,map_smul]
    change a * y v + b * y w = 0
    dsimp only [a]
    field_simp
    ring
  · change x (a • v + b • w) = x g
    rw [xg,map_add,map_smul,map_smul]
    change a * x v + b * x w = 1
    have h := inv_mul_cancel₀ hw.ne'
    change b * l w = 1 at h
    rw [hl] at h
    dsimp only [m] at h
    dsimp only [a]
    linear_combination (norm := (field_simp; ring)) h

end EFiniteCharacterizations
