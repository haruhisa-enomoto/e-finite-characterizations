module

public import EFiniteCharacterizations.LinearAlgebra.ArrowScalarExtension
public import EFiniteCharacterizations.LinearAlgebra.ScalarDescent
public import EFiniteCharacterizations.Presentations.RigidPair
public import EFiniteCharacterizations.Presentations.StableRigidComparison

/-! # Additive closure of presilting complexes of the same class -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace EFiniteCharacterizations

section RigidPair

variable (k : Type*) [Field k] {C : Type*} [Category C] [Preadditive C] [Linear k C]

/-- Rigid differentials on fixed terms belong to one another's additive
closures over the ground field. -/
theorem isInAdd_arrow_of_rigid_pair {X Y : C} (p q : X ⟶ Y)
    [Module.Finite k (X ⟶ X)] [Module.Finite k (Y ⟶ Y)] [Module.Finite k (X ⟶ Y)]
    (hp : Function.Surjective (boundaryLinear k p p))
    (hq : Function.Surjective (boundaryLinear k q q)) :
    IsInAdd (Arrow.mk p) (Arrow.mk q) ∧ IsInAdd (Arrow.mk q) (Arrow.mk p) := by
  let F := RatFunc k
  let G : C ⥤ ScalarCategory k F C := ScalarCategory.of
  let H : ScalarCategory k F (Arrow C) ⥤ Arrow (ScalarCategory k F C) := ScalarCategory.arrowComparison F
  let J : Arrow C ⥤ ScalarCategory k F (Arrow C) := ScalarCategory.of
  obtain ⟨a, b, hab⟩ := exists_iso_square_of_rigid_pair k p q hp hq
  let e : H.obj (J.obj (Arrow.mk p)) ≅ H.obj (J.obj (Arrow.mk q)) := Arrow.isoMk' (G.map p) (G.map q) a b hab
  exact ScalarCategory.isInAdd_of_scalar_iso F (H.preimageIso e)

end RigidPair

namespace TwoTerm

universe u

variable {R : Type u} [Ring R]

/-- Regard a two-term complex as an arrow between its terms. -/
def asArrow (P : TwoTerm R) : Arrow (FGModuleCat.{u} R) := Arrow.mk P.differential

/-- Include the first summand into a degreewise direct sum of complexes. -/
noncomputable def inlDirectSum (P Q : TwoTerm R) : P.asArrow ⟶ (P.directSum Q).asArrow :=
  Arrow.homMk biprod.inl biprod.inl (by
    change biprod.inl ≫ blockDifferential P.differential Q.differential 0 = P.differential ≫ biprod.inl
    simp)

/-- Project from a degreewise direct sum of complexes to its first summand. -/
noncomputable def fstDirectSum (P Q : TwoTerm R) : (P.directSum Q).asArrow ⟶ P.asArrow :=
  Arrow.homMk biprod.fst biprod.fst (by
    change biprod.fst ≫ P.differential = blockDifferential P.differential Q.differential 0 ≫ biprod.fst
    rw [blockDifferential_zero, biprod.map_fst])

@[simp] theorem inlDirectSum_fstDirectSum (P Q : TwoTerm R) :
    inlDirectSum P Q ≫ fstDirectSum P Q = 𝟙 P.asArrow := by
  apply Arrow.hom_ext <;> exact biprod.inl_fst

/-- Include the second summand into a degreewise direct sum of complexes. -/
noncomputable def inrDirectSum (P Q : TwoTerm R) : Q.asArrow ⟶ (P.directSum Q).asArrow :=
  Arrow.homMk biprod.inr biprod.inr (by
    change biprod.inr ≫ blockDifferential P.differential Q.differential 0 = Q.differential ≫ biprod.inr
    rw [blockDifferential_zero, biprod.inr_map])

/-- Project from a degreewise direct sum of complexes to its second summand. -/
noncomputable def sndDirectSum (P Q : TwoTerm R) : (P.directSum Q).asArrow ⟶ Q.asArrow :=
  Arrow.homMk biprod.snd biprod.snd (by
    change biprod.snd ≫ Q.differential = blockDifferential P.differential Q.differential 0 ≫ biprod.snd
    simp)

@[simp] theorem inrDirectSum_sndDirectSum (P Q : TwoTerm R) :
    inrDirectSum P Q ≫ sndDirectSum P Q = 𝟙 Q.asArrow := by
  apply Arrow.hom_ext <;> exact biprod.inr_snd

theorem totalDirectSum (P Q : TwoTerm R) : fstDirectSum P Q ≫ inlDirectSum P Q +
    sndDirectSum P Q ≫ inrDirectSum P Q = 𝟙 (P.directSum Q).asArrow := by
  apply Arrow.hom_ext <;> exact biprod.total

theorem isInAdd_directSum (P Q : TwoTerm R) (X : Arrow (FGModuleCat.{u} R))
    (hP : IsInAdd P.asArrow X) (hQ : IsInAdd Q.asArrow X) : IsInAdd (P.directSum Q).asArrow X :=
  IsInAdd.of_total hP hQ _ _ _ _ (totalDirectSum P Q)

/-- Membership in the additive closure after allowing a contractible direct
summand on the generating complex. -/
def IsInStableAdd (P Q : TwoTerm R) : Prop :=
  ∃ T : FiniteProjective R, IsInAdd P.asArrow (Q.directSum (contractible T)).asArrow

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
/-- Presilting complexes of the same integral class generate one another up
to contractible summands, over every field. -/
theorem isInStableAdd_of_isPresilting_of_class_eq (P Q : TwoTerm R)
    (hP : P.IsPresilting) (hQ : Q.IsPresilting) (h : P.projectiveClass = Q.projectiveClass) :
    P.IsInStableAdd Q ∧ Q.IsInStableAdd P := by
  have (X Y : FGModuleCat.{u} R) : Module.Finite k (X ⟶ Y) := finiteModuleHom_isFinite k X Y
  obtain ⟨S, T, ⟨i₁⟩, ⟨i₀⟩⟩ := exists_stable_term_isos P Q h
  let P' := P.directSum (contractible S)
  let Q' := Q.directSum (contractible T)
  let e₁ : P'.source ≅ Q'.source := i₁
  let e₀ : P'.target ≅ Q'.target := i₀
  let _ := Q'.projective_source
  let _ := Q'.projective_target
  let v := e₁.inv ≫ P'.differential ≫ e₀.hom
  let U := ofDifferential v
  have hv : e₁.hom ≫ U.differential = P'.differential ≫ e₀.hom := by
    change e₁.hom ≫ e₁.inv ≫ P'.differential ≫ e₀.hom = _
    rw [Iso.hom_inv_id_assoc]
  have hu : U.IsPresilting := (isPresilting_iff_of_term_isos k P' U e₁ e₀ hv).1
    ((isPresilting_directSum_contractible_iff k P S).2 hP)
  have hq' := (isPresilting_directSum_contractible_iff k Q T).2 hQ
  have hpq : IsInAdd U.asArrow Q'.asArrow ∧ IsInAdd Q'.asArrow U.asArrow :=
    isInAdd_arrow_of_rigid_pair k v Q'.differential
      ((isPresilting_iff_boundaryLinear_surjective (k := k) U).1 hu)
      ((isPresilting_iff_boundaryLinear_surjective (k := k) Q').1 hq')
  let i : P'.asArrow ≅ U.asArrow := Arrow.isoMk' P'.differential U.differential e₁ e₀ hv
  have hP' : IsInAdd P.asArrow P'.asArrow := IsInAdd.of_retraction _ _ (inlDirectSum_fstDirectSum P _)
  have hQ' : IsInAdd Q.asArrow Q'.asArrow := IsInAdd.of_retraction _ _ (inlDirectSum_fstDirectSum Q _)
  exact ⟨⟨T, hP'.trans ((IsInAdd.of_retraction _ _ i.hom_inv_id).trans hpq.1)⟩,
    ⟨S, hQ'.trans (hpq.2.trans (IsInAdd.of_retraction _ _ i.inv_hom_id))⟩⟩

end TwoTerm

end EFiniteCharacterizations
