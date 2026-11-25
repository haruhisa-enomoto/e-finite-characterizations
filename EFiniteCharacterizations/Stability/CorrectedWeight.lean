module

public import EFiniteCharacterizations.Stability.Weights
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Ring

/-! # Normalizing a weight at an object -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace EFiniteCharacterizations.Weight

variable {C : Type*} [Category C] [Abelian C]

/-- Adjustment of a weight by a positive size so that it vanishes on `B`. -/
def corrected (g d : Weight C) (B : C) : Weight C :=
  d.eval B • g - g.eval B • d

theorem eval_corrected (g d : Weight C) (B L : C) :
    (g.corrected d B).eval L = d.eval B * g.eval L - g.eval B * d.eval L := by
  simp only [corrected, eval, AddMonoidHom.sub_apply, AddMonoidHom.zsmul_apply, zsmul_eq_mul, Int.cast_id]

/-- Strictly opposite weight signs on subobjects and their quotients make
the corrected weight stable. -/
theorem isStable_corrected (g d : Weight C) {B : C} (hB : ¬ IsZero B)
    (hd : ∀ X : C, ¬ IsZero X → 0 < d.eval X)
    (hg : ∀ {L : C} (i : L ⟶ B) [Mono i], ¬ IsZero L → ¬ IsIso i →
      g.eval L < 0 ∧ 0 < g.eval (cokernel i)) :
    (g.corrected d B).IsStable B := by
  refine ⟨hB, ?_, ?_⟩
  · rw [eval_corrected, mul_comm, sub_self]
  · intro L i _ hL hi
    let Q := cokernel i
    have hQ : ¬ IsZero Q := by
      intro hz
      have : Epi i := Abelian.epi_of_cokernel_π_eq_zero i (hz.eq_of_tgt _ _)
      exact hi (isIso_of_mono_of_epi i)
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hS : S.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i)
      (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
    have hdadd : d.eval B = d.eval L + d.eval Q := d.eval_shortExact S hS
    have hgadd : g.eval B = g.eval L + g.eval Q := g.eval_shortExact S hS
    obtain ⟨hsg, hsq⟩ := hg i hL hi
    rw [eval_corrected, hdadd, hgadd]
    have heq :
        (d.eval L + d.eval Q) * g.eval L - (g.eval L + g.eval Q) * d.eval L =
        d.eval Q * g.eval L - g.eval Q * d.eval L := by ring
    rw [heq]
    exact sub_neg.mpr ((mul_neg_of_pos_of_neg (hd Q hQ) hsg).trans (mul_pos hsq (hd L hL)))

end EFiniteCharacterizations.Weight
