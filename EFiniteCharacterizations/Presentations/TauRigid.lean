module

public import EFiniteCharacterizations.Presentations.FinitePresiltingCokernels
public import EFiniteCharacterizations.Presentations.MinimalPresentations

/-! # The presentation criterion for tau-rigidity -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

/-- A module is tau-rigid when its Hom to the Auslander–Reiten translate
vanishes. The translate is the Nakayama kernel of a minimal projective
presentation. -/
def IsTauRigid (M : FGModuleCat.{u} R) : Prop :=
  ∃ p : MinimalPresentation M, Subsingleton (M ⟶ p.twoTerm.nakayamaKernel k)

variable {k}

omit [IsNoetherianRing R] in
/-- Precomposition by a projective differential is surjective into
isomorphic targets simultaneously. -/
theorem TwoTerm.surjective_precompose_of_iso (P : TwoTerm R) {M N : FGModuleCat.{u} R}
    (e : M ≅ N) (h : Function.Surjective (P.precompose M)) :
    Function.Surjective (P.precompose N) := by
  intro f
  obtain ⟨g, hg⟩ := h (f ≫ e.inv)
  change P.differential ≫ g = f ≫ e.inv at hg
  refine ⟨g ≫ e.hom, ?_⟩
  change P.differential ≫ g ≫ e.hom = f
  rw [← Category.assoc, hg, Category.assoc, e.inv_hom_id, Category.comp_id]

theorem IsTauRigid.exists_presilting_cokernel {M : FGModuleCat.{u} R} (h : IsTauRigid k M) :
    ∃ P : TwoTerm R, P.IsPresilting ∧ Nonempty (cokernel P.differential ≅ M) := by
  obtain ⟨p, hp⟩ := h
  have hs := (p.twoTerm.surjective_precompose_iff_no_hom_nakayamaKernel k M).2 hp
  exact ⟨p.twoTerm, (TwoTerm.surjective_boundary_iff_surjective_precompose _ _).2
    (p.twoTerm.surjective_precompose_of_iso p.cokernelIso.symm hs), ⟨p.cokernelIso⟩⟩

variable (k)

/-- Any retract of a presilting cokernel is tau-rigid. -/
theorem TwoTerm.isTauRigid_of_cokernel_retract (P : TwoTerm R) (hP : P.IsPresilting)
    {M : FGModuleCat.{u} R} (i : M ⟶ cokernel P.differential)
    (r : cokernel P.differential ⟶ M) (h : i ≫ r = 𝟙 M) : IsTauRigid k M := by
  obtain ⟨p⟩ := MinimalPresentation.nonempty_minimalPresentation k M
  have hs := p.surjective_precompose_of_retract i r h P (cokernel.π P.differential)
    (cokernel.condition _) (ShortComplex.exact_cokernel _)
    ((TwoTerm.surjective_boundary_iff_surjective_precompose P P).1 hP)
  exact ⟨p, (TwoTerm.surjective_precompose_iff_no_hom_nakayamaKernel k _ _).1 hs⟩

/-- A module is tau-rigid exactly when it admits a presilting presentation. -/
theorem isTauRigid_iff_exists_presilting_cokernel (M : FGModuleCat.{u} R) :
    IsTauRigid k M ↔ ∃ P : TwoTerm R, P.IsPresilting ∧ Nonempty (cokernel P.differential ≅ M) := by
  refine ⟨IsTauRigid.exists_presilting_cokernel, ?_⟩
  rintro ⟨P, hP, ⟨e⟩⟩
  exact P.isTauRigid_of_cokernel_retract k hP e.inv e.hom e.inv_hom_id

theorem IsTauRigid.of_retract {M N : FGModuleCat.{u} R} (hN : IsTauRigid k N)
    (i : M ⟶ N) (r : N ⟶ M) (h : i ≫ r = 𝟙 M) : IsTauRigid k M := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hN.exists_presilting_cokernel
  exact P.isTauRigid_of_cokernel_retract k hP (i ≫ e.inv) (e.hom ≫ r) (by simp [h])

/-- The isomorphism classes of indecomposable tau-rigid modules. -/
def indecomposableTauRigidClasses : Set (Skeleton (FGModuleCat.{u} R)) :=
  {c | ∃ M : FGModuleCat.{u} R, Indecomposable M ∧ IsTauRigid k M ∧ toSkeleton M = c}

theorem indecomposableTauRigidClasses_eq_presiltingCokernelClasses :
    indecomposableTauRigidClasses (R := R) k = TwoTerm.indecomposablePresiltingCokernelClasses := by
  ext c
  constructor
  · rintro ⟨M, hM, hτ, rfl⟩
    obtain ⟨P, hP, ⟨e⟩⟩ := hτ.exists_presilting_cokernel
    have hInd : Indecomposable (cokernel P.differential) :=
      ⟨fun h ↦ hM.1 (h.of_iso e.symm), fun _ _ f ↦ hM.2 _ _ (e.symm.trans f)⟩
    exact ⟨P, hP, hInd, toSkeleton_eq_toSkeleton_iff.mpr ⟨e⟩⟩
  · rintro ⟨P, hP, hInd, rfl⟩
    exact ⟨_, hInd, (isTauRigid_iff_exists_presilting_cokernel k _).2 ⟨P, hP, ⟨Iso.refl _⟩⟩, rfl⟩

omit [IsNoetherianRing R] in
/-- E-finiteness in rank at most two implies finiteness of the indecomposable
tau-rigid modules over the ground field. -/
theorem finite_indecomposableTauRigidClasses_of_rank_le_two
    (hr : (simpleIsomorphismClasses R).ncard ≤ 2) (hR : IsEFinite R) :
    letI := IsNoetherianRing.of_finite k R
    (indecomposableTauRigidClasses (R := R) k).Finite := by
  let _ := IsNoetherianRing.of_finite k R
  rw [indecomposableTauRigidClasses_eq_presiltingCokernelClasses]
  exact TwoTerm.finite_indecomposablePresiltingCokernelClasses_of_rank_le_two k hr hR

end EFiniteCharacterizations
