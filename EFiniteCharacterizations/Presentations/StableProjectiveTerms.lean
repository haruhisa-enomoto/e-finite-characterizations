module

public import EFiniteCharacterizations.Modules.ProjectiveBiproducts
public import EFiniteCharacterizations.Modules.FiniteModuleMorphisms
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-! # Equal projective classes give common terms after stabilization -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.ProjectiveClass

variable {R : Type u} [Ring R]

/-- Isomorphism as a relation on finite projective modules. -/
def isoSetoid (R : Type u) [Ring R] : Setoid (FiniteProjective R) where
  r P Q := Nonempty (P.val ≅ Q.val)
  iseqv := ⟨fun P ↦ ⟨Iso.refl P.val⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩⟩

/-- Isomorphism classes of finite projective modules. -/
def IsoClasses (R : Type u) [Ring R] := Quotient (isoSetoid R)

/-- The isomorphism class of a finite projective. -/
def isoClass (P : FiniteProjective R) : IsoClasses R := Quotient.mk _ P

theorem isoClass_eq_iff {P Q : FiniteProjective R} : isoClass P = isoClass Q ↔ Nonempty (P.val ≅ Q.val) :=
  Quotient.eq

theorem zeroProjective_isZero : IsZero (zeroProjective R).val :=
  (FGModuleCat.isZero_iff_subsingleton _).mpr (inferInstanceAs (Subsingleton PUnit))

/-- The zero finite projective is an additive identity for binary direct sums. -/
theorem nonempty_zeroBiprodIso (P : FiniteProjective R) :
    Nonempty (((zeroProjective R).val ⊞ P.val) ≅ P.val) := by
  refine ⟨⟨biprod.snd, biprod.inr, ?_, by simp⟩⟩
  apply biprod.hom_ext'
  · exact zeroProjective_isZero.eq_of_src _ _
  · simp

@[simp] theorem of_zeroProjective : of (zeroProjective R) = 0 := by
  obtain ⟨i⟩ := nonempty_zeroBiprodIso (zeroProjective R)
  have h := of_eq_of_iso (biprod (zeroProjective R) (zeroProjective R)) (zeroProjective R) i
  rw [of_biprod, add_eq_right] at h
  exact h

instance : Zero (IsoClasses R) where
  zero := isoClass (zeroProjective R)

noncomputable instance : Add (IsoClasses R) where
  add := Quotient.map₂ (sa := isoSetoid R) (sb := isoSetoid R) (sc := isoSetoid R) biprod (by
    intro P P' hP Q Q' hQ
    obtain ⟨e⟩ := hP
    obtain ⟨f⟩ := hQ
    exact ⟨biprod.mapIso e f⟩)

noncomputable instance : AddCommMonoid (IsoClasses R) where
  add_assoc a b c := Quotient.inductionOn₃ a b c fun P Q T ↦
    isoClass_eq_iff.mpr ⟨biprod.associator P.val Q.val T.val⟩
  add_comm a b := Quotient.inductionOn₂ a b fun P Q ↦
    isoClass_eq_iff.mpr ⟨biprod.braiding P.val Q.val⟩
  zero_add a := Quotient.inductionOn a fun P ↦ isoClass_eq_iff.mpr (nonempty_zeroBiprodIso P)
  add_zero a := Quotient.inductionOn a fun P ↦ by
    obtain ⟨e⟩ := nonempty_zeroBiprodIso P
    exact isoClass_eq_iff.mpr ⟨(biprod.braiding P.val (zeroProjective R).val).trans e⟩
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl

@[simp] theorem isoClass_biprod (P Q : FiniteProjective R) :
    isoClass (biprod P Q) = isoClass P + isoClass Q := rfl

/-- The split Grothendieck class maps to the group completion of the
monoid of projective isomorphism classes. -/
noncomputable def toIsoClassCompletion (R : Type u) [Ring R] :
    ProjectiveClass R →+ Algebra.GrothendieckAddGroup (IsoClasses R) :=
  ProjectiveClass.lift (fun P ↦ Algebra.GrothendieckAddGroup.of (isoClass P))
    (fun _ _ e ↦ congrArg Algebra.GrothendieckAddGroup.of (isoClass_eq_iff.mpr ⟨e⟩))
    (fun P Q T e ↦ by
      let F := forget₂ (FGModuleCat R) (ModuleCat.{u} R)
      let i : T.val ≅ (biprod P Q).val := F.preimageIso (e.trans (FGModuleCat.forgetBiprodIso P.val Q.val).symm)
      rw [← map_add, ← isoClass_biprod, isoClass_eq_iff.mpr ⟨i⟩])

@[simp] theorem toIsoClassCompletion_of (P : FiniteProjective R) :
    toIsoClassCompletion R (of P) = Algebra.GrothendieckAddGroup.of (isoClass P) :=
  lift_of _ _ _ P

/-- Equal classes of projectives give an isomorphism after adding a common
projective. This uses group completion and does not require cancellation. -/
theorem exists_biprod_iso_of_of_eq {P Q : FiniteProjective R} (h : of P = of Q) :
    ∃ T : FiniteProjective R, Nonempty (P.val ⊞ T.val ≅ Q.val ⊞ T.val) := by
  have he := congrArg (toIsoClassCompletion R) h
  simp only [toIsoClassCompletion_of] at he
  change (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (IsoClasses R))) (isoClass P) =
    (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (IsoClasses R))) (isoClass Q) at he
  rw [← AddLocalization.mk_zero_eq_addMonoidOf_mk, ← AddLocalization.mk_zero_eq_addMonoidOf_mk] at he
  obtain ⟨t, ht⟩ := AddLocalization.r_iff_exists.mp (AddLocalization.mk_eq_mk_iff.mp he)
  obtain ⟨T, hT⟩ := Quotient.exists_rep (t.val : IsoClasses R)
  change t.val + (0 + isoClass P) = t.val + (0 + isoClass Q) at ht
  change isoClass T = t.val at hT
  rw [← hT, zero_add, zero_add, add_comm (isoClass T) (isoClass P), add_comm (isoClass T) (isoClass Q),
    ← isoClass_biprod, ← isoClass_biprod] at ht
  exact ⟨T, isoClass_eq_iff.mp ht⟩

end EFiniteCharacterizations.ProjectiveClass

namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R]

/-- Equal two-term classes have the same terms up to isomorphism after adding
one contractible complex to each. -/
theorem exists_stable_term_isos (P Q : TwoTerm R) (h : P.projectiveClass = Q.projectiveClass) :
    ∃ S T : FiniteProjective R,
      Nonempty (P.source ⊞ S.val ≅ Q.source ⊞ T.val) ∧
      Nonempty (P.target ⊞ S.val ≅ Q.target ⊞ T.val) := by
  let P₀ : FiniteProjective R := ⟨P.target, P.projective_target⟩
  let P₁ : FiniteProjective R := ⟨P.source, P.projective_source⟩
  let Q₀ : FiniteProjective R := ⟨Q.target, Q.projective_target⟩
  let Q₁ : FiniteProjective R := ⟨Q.source, Q.projective_source⟩
  change ProjectiveClass.of P₀ - ProjectiveClass.of P₁ = ProjectiveClass.of Q₀ - ProjectiveClass.of Q₁ at h
  have hc : ProjectiveClass.of P₀ + ProjectiveClass.of Q₁ = ProjectiveClass.of Q₀ + ProjectiveClass.of P₁ := by
    calc
      _ = (ProjectiveClass.of P₀ - ProjectiveClass.of P₁) + (ProjectiveClass.of P₁ + ProjectiveClass.of Q₁) := by abel
      _ = _ := by rw [h]; abel
  have hsum : ProjectiveClass.of (ProjectiveClass.biprod P₀ Q₁) =
      ProjectiveClass.of (ProjectiveClass.biprod Q₀ P₁) := by simpa only [ProjectiveClass.of_biprod] using hc
  obtain ⟨U, ⟨e⟩⟩ := ProjectiveClass.exists_biprod_iso_of_of_eq hsum
  refine ⟨ProjectiveClass.biprod Q₁ U, ProjectiveClass.biprod P₁ U, ?_, ?_⟩
  · exact ⟨(biprod.associator P.source Q.source U.val).symm.trans
      ((biprod.mapIso (biprod.braiding P.source Q.source) (Iso.refl U.val)).trans
        (biprod.associator Q.source P.source U.val))⟩
  · exact ⟨(biprod.associator P.target Q.source U.val).symm.trans
      (e.trans (biprod.associator Q.target P.source U.val))⟩

end EFiniteCharacterizations.TwoTerm
