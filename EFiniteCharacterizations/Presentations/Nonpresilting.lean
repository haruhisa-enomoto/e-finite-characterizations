module

public import EFiniteCharacterizations.Presentations.NakayamaPairing
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Prod

/-! # A nonpresilting differential has a nonzero Hom defect -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

/-- Nonvanishing shifted Hom yields a nonzero map from the cokernel of the
differential to its Nakayama kernel. -/
theorem exists_nonzero_hom_of_not_isPresilting (P : TwoTerm R) (hP : ¬ P.IsPresilting) :
    ∃ f : cokernel P.differential ⟶ P.nakayamaKernel k, f ≠ 0 := by
  classical
  have : Module.Projective R P.source := P.projective_source
  have : Module.Projective R P.target := P.projective_target
  let p := P.differential
  let d := (Linear.rightComp k P.source p).coprod (-Linear.leftComp k P.target p)
  have hd : ¬ Function.Surjective d := by
    intro hd
    apply hP
    intro v
    obtain ⟨x, hx⟩ := hd v
    exact ⟨x, by simpa [d, p, homotopyBoundary, sub_eq_add_neg] using hx⟩
  obtain ⟨v, hv⟩ := not_forall.mp hd
  let U := LinearMap.range d
  have hvq : U.mkQ v ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero U).mp hz
    exact hv ⟨x, hx⟩
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero k hvq
  let χ := ψ.comp U.mkQ
  have hχ : χ ≠ 0 := by
    intro hz
    exact hψ (congrArg (fun a : Module.Dual k (P.source ⟶ P.target) ↦ a v) hz)
  have hχd (x) : χ (d x) = 0 := by
    change ψ (U.mkQ (d x)) = 0
    have hz : U.mkQ (d x) = 0 := (Submodule.Quotient.mk_eq_zero U).mpr ⟨x, rfl⟩
    rw [hz, map_zero]
  have hleft : (Linear.leftComp k P.target p).dualMap χ = 0 := by
    ext b
    simpa [d] using hχd (0, b)
  have hright : (Linear.rightComp k P.source p).dualMap χ = 0 := by
    ext a
    simpa [d] using hχd (a, 0)
  let g := nakayamaPairing k P.source P.target χ
  have hvp : g ≫ nakayamaMorphism k p = 0 := by
    rw [← nakayamaPairing_dual_leftComp k p χ, hleft, map_zero]
  have hpg : p ≫ g = 0 := by
    rw [← nakayamaPairing_dual_rightComp k p χ, hright, map_zero]
  let l := kernel.lift (nakayamaMorphism k p) g hvp
  have hl : p ≫ l = 0 := by
    apply (cancel_mono (kernel.ι (nakayamaMorphism k p))).mp
    simpa [l] using hpg
  let q := cokernel.desc p l hl
  refine ⟨q, ?_⟩
  intro hq
  change q = (0 : cokernel p ⟶ kernel (nakayamaMorphism k p)) at hq
  have hlz : l = 0 := calc
    l = cokernel.π p ≫ q := (cokernel.π_desc p l hl).symm
    _ = 0 := by rw [hq, comp_zero]
  have hgz : g = 0 := calc
    g = l ≫ kernel.ι (nakayamaMorphism k p) := (kernel.lift_ι _ _ _).symm
    _ = 0 := by rw [hlz, zero_comp]
  exact hχ ((nakayamaPairing k P.source P.target).injective (hgz.trans (map_zero _).symm))

end EFiniteCharacterizations.TwoTerm
