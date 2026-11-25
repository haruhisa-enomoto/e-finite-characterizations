module

public import EFiniteCharacterizations.Modules.HomDimension
public import EFiniteCharacterizations.Stability.CorrectedWeight
public import EFiniteCharacterizations.Stability.MinimalImage

/-! # Stable bricks from a difference of Hom dimensions -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations

open EFiniteCharacterizations.FGModuleCat

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

omit [IsArtinianRing R] in
/-- The corrected weight stabilizes the image when proper subobjects and quotients satisfy the two Hom vanishings. -/
theorem stable_image_of_hom_vanishing
    {X Y : FGModuleCat.{u} R} (g d : Weight (FGModuleCat.{u} R))
    (hd : ∀ M : FGModuleCat.{u} R, ¬ IsZero M → 0 < d.eval M)
    (hg : ∀ M : FGModuleCat.{u} R,
      g.eval M = (homFinrank k X M : ℤ) - (homFinrank k M Y : ℤ))
    (f : X ⟶ Y) (hne : ¬ IsZero (image f))
    (hsub : ∀ {L : FGModuleCat R} (i : L ⟶ image f) [Mono i], ¬ IsIso i → ∀ g : X ⟶ L, g = 0)
    (hquot : ∀ {Q : FGModuleCat R} (q : image f ⟶ Q) [Epi q], ¬ IsIso q → ∀ g : Q ⟶ Y, g = 0) :
    (g.corrected d (image f)).IsStable (image f) := by
  apply Weight.isStable_corrected _ _ hne hd
  intro L i _ hL hi
  have hleft : homFinrank k X L = 0 :=
    (homFinrank_eq_zero_iff k X L).2 (hsub i hi)
  let j := i ≫ image.ι f
  have hj : j ≠ 0 := by
    intro hz
    apply hL
    apply (IsZero.iff_id_eq_zero L).2
    apply (cancel_mono j).1
    rw [Category.id_comp, zero_comp, hz]
  have hright : 0 < homFinrank k L Y := (homFinrank_pos_iff k L Y).2 ⟨j, hj⟩
  let q := cokernel.π i
  have hq : ¬ IsIso q := by
    intro hq
    have hzero : i = 0 := by
      apply (cancel_mono q).1
      exact (cokernel.condition i).trans zero_comp.symm
    apply hL
    apply (IsZero.iff_id_eq_zero L).2
    apply (cancel_mono i).1
    rw [Category.id_comp, zero_comp, hzero]
  have hQ : ¬ IsZero (cokernel i) := by
    intro hz
    have : Epi i := Abelian.epi_of_cokernel_π_eq_zero i (hz.eq_of_tgt _ _)
    exact hi (isIso_of_mono_of_epi i)
  let p := factorThruImage f ≫ q
  have hp : p ≠ 0 := by
    intro hz
    apply hQ
    apply (IsZero.iff_id_eq_zero (cokernel i)).2
    apply (cancel_epi p).1
    rw [Category.comp_id, comp_zero, hz]
  have hpos : 0 < homFinrank k X (cokernel i) :=
    (homFinrank_pos_iff k X (cokernel i)).2 ⟨p, hp⟩
  have hzero : homFinrank k (cokernel i) Y = 0 :=
    (homFinrank_eq_zero_iff k (cokernel i) Y).2 (hquot q hq)
  rw [hg L, hg (cokernel i), hleft, hzero]
  omega

/-- If a weight is the difference of the Hom dimensions from `X` and to `Y`, a
nonzero map from `X` to `Y` gives a brick stable at a corrected weight. -/
theorem exists_stable_image_of_hom_difference
    {X Y : FGModuleCat.{u} R} (g d : Weight (FGModuleCat.{u} R))
    (hd : ∀ M : FGModuleCat.{u} R, ¬ IsZero M → 0 < d.eval M)
    (hg : ∀ M : FGModuleCat.{u} R,
      g.eval M = (homFinrank k X M : ℤ) - (homFinrank k M Y : ℤ))
    (h : ∃ f : X ⟶ Y, f ≠ 0) :
    ∃ f : X ⟶ Y, f ≠ 0 ∧ IsBrick (image f) ∧
      (g.corrected d (image f)).IsStable (image f) := by
  obtain ⟨f, hf, hb, hmin⟩ := exists_minimal_image_brick (R := R) h
  exact ⟨f, hf, hb, stable_image_of_hom_vanishing k g d hd hg f hb.1
    (fun i _ hi ↦ hom_to_proper_subobject_of_minimal_image f hmin i hi)
    (fun q _ hq ↦ hom_from_proper_quotient_of_minimal_image f hmin q hq)⟩

end EFiniteCharacterizations
