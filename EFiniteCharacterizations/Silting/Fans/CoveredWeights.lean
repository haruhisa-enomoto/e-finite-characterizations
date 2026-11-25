module

public import EFiniteCharacterizations.Presentations.PresiltingHom
public import EFiniteCharacterizations.Presentations.ProjectiveHomWeight

/-! # The weak numerical torsion classes at a presilting weight -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

/-- The Euler weight measures the difference of the two perpendicular Hom dimensions. -/
theorem eulerWeight_eq_perpendicular_difference (P : TwoTerm R) (M : FGModuleCat.{u} R) :
    (P.eulerWeight k).eval M =
      (homFinrank k (cokernel P.differential) M : ℤ) - homFinrank k M (P.nakayamaKernel k) :=
  (P.eulerWeight_eval k M).trans (P.euler_eq_hom_difference k M)

/-- The weak quotient test is the left perpendicular of the Nakayama kernel. -/
theorem nonneg_eulerWeight_all_quotients_iff (P : TwoTerm R) (hP : P.IsPresilting)
    (M : FGModuleCat.{u} R) :
    (∀ {Q : FGModuleCat.{u} R} (q : M ⟶ Q) [Epi q], 0 ≤ (P.eulerWeight k).eval Q) ↔
      Subsingleton (M ⟶ P.nakayamaKernel k) := by
  let X := cokernel P.differential
  let Y := P.nakayamaKernel k
  have hXY : Subsingleton (X ⟶ Y) := (P.isPresilting_iff_no_hom_nakayamaKernel k).1 hP
  constructor
  · intro h
    suffices hz : ∀ f : M ⟶ Y, f = 0 from ⟨fun f g ↦ (hz f).trans (hz g).symm⟩
    intro f
    by_contra hf
    let q := Abelian.factorThruImage f
    let j := Abelian.image.ι f
    have hj : j ≠ 0 := by
      intro hj
      apply hf
      rw [← Abelian.image.fac f]
      exact (congrArg (q ≫ ·) hj).trans comp_zero
    have hn := h q
    have hz := (homFinrank_eq_zero_iff k X (Abelian.image f)).2 (fun a ↦
      (cancel_mono j).1 ((hXY.elim (a ≫ j) 0).trans zero_comp.symm))
    have hp := (homFinrank_pos_iff k (Abelian.image f) Y).2 ⟨j, hj⟩
    rw [P.eulerWeight_eq_perpendicular_difference k, hz] at hn
    change (0 : ℤ) ≤ 0 - (homFinrank k (Abelian.image f) Y : ℤ) at hn
    omega
  · intro h Q q _
    have hz := (homFinrank_eq_zero_iff k Q Y).2 (fun a ↦
      (cancel_epi q).1 ((h.elim (q ≫ a) 0).trans comp_zero.symm))
    rw [P.eulerWeight_eq_perpendicular_difference k, hz, Nat.cast_zero, sub_zero]
    exact Int.natCast_nonneg _

/-- The weak subobject test is the right perpendicular of the cokernel. -/
theorem nonpos_eulerWeight_all_subobjects_iff (P : TwoTerm R) (hP : P.IsPresilting)
    (M : FGModuleCat.{u} R) :
    (∀ {L : FGModuleCat.{u} R} (i : L ⟶ M) [Mono i], (P.eulerWeight k).eval L ≤ 0) ↔
      Subsingleton (cokernel P.differential ⟶ M) := by
  let X := cokernel P.differential
  let Y := P.nakayamaKernel k
  have hXY : Subsingleton (X ⟶ Y) := (P.isPresilting_iff_no_hom_nakayamaKernel k).1 hP
  constructor
  · intro h
    suffices hz : ∀ f : X ⟶ M, f = 0 from ⟨fun f g ↦ (hz f).trans (hz g).symm⟩
    intro f
    by_contra hf
    let q := Abelian.factorThruImage f
    let j := Abelian.image.ι f
    have hq : q ≠ 0 := by
      intro hq
      apply hf
      rw [← Abelian.image.fac f]
      exact (congrArg (· ≫ j) hq).trans zero_comp
    have hn := h j
    have hz := (homFinrank_eq_zero_iff k (Abelian.image f) Y).2 (fun a ↦
      (cancel_epi q).1 ((hXY.elim (q ≫ a) 0).trans comp_zero.symm))
    have hp := (homFinrank_pos_iff k X (Abelian.image f)).2 ⟨q, hq⟩
    rw [P.eulerWeight_eq_perpendicular_difference k, hz] at hn
    change (homFinrank k X (Abelian.image f) : ℤ) - 0 ≤ 0 at hn
    omega
  · intro h L i _
    have hz := (homFinrank_eq_zero_iff k X L).2 (fun a ↦
      (cancel_mono i).1 ((h.elim (a ≫ i) 0).trans zero_comp.symm))
    rw [P.eulerWeight_eq_perpendicular_difference k, hz, Nat.cast_zero, zero_sub]
    omega

/-- The semistable modules at the weight of a presilting differential are
exactly the modules in its two Hom perpendiculars. -/
theorem isSemistable_eulerWeight_iff_perpendicular (P : TwoTerm R) (hP : P.IsPresilting)
    (M : FGModuleCat.{u} R) :
    (P.eulerWeight k).IsSemistable M ↔
      Subsingleton (cokernel P.differential ⟶ M) ∧ Subsingleton (M ⟶ P.nakayamaKernel k) := by
  constructor
  · rintro ⟨hzero, hsub⟩
    have hX := (P.nonpos_eulerWeight_all_subobjects_iff k hP M).1 hsub
    have hd := (homFinrank_eq_zero_iff k (cokernel P.differential) M).2 (fun f ↦ hX.elim f 0)
    rw [P.eulerWeight_eq_perpendicular_difference k, hd] at hzero
    have hY : homFinrank k M (P.nakayamaKernel k) = 0 := by omega
    let hz := (homFinrank_eq_zero_iff k _ _).1 hY
    exact ⟨hX, ⟨fun f g ↦ (hz f).trans (hz g).symm⟩⟩
  · rintro ⟨hX, hY⟩
    have hX' := (homFinrank_eq_zero_iff k (cokernel P.differential) M).2 (fun f ↦ hX.elim f 0)
    have hY' := (homFinrank_eq_zero_iff k M (P.nakayamaKernel k)).2 (fun f ↦ hY.elim f 0)
    refine ⟨?_, (P.nonpos_eulerWeight_all_subobjects_iff k hP M).2 hX⟩
    rw [P.eulerWeight_eq_perpendicular_difference k, hX', hY', sub_self]

end EFiniteCharacterizations.TwoTerm
