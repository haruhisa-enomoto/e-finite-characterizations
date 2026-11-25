module

public import EFiniteCharacterizations.Presentations.StableRigidComparison
public import EFiniteCharacterizations.Modules.FittingInversion
public import EFiniteCharacterizations.Presentations.RigidPencilInversion

/-! # Inversion on arbitrary modules at a fixed projective class -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace EFiniteCharacterizations

section Additive

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (N : D)

private noncomputable def sumHomEquiv (X Y : C) [HasBinaryBiproduct X Y] :
    (F.obj (X ⊞ Y) ⟶ N) ≃ (F.obj X ⟶ N) × (F.obj Y ⟶ N) where
  toFun g := (F.map biprod.inl ≫ g, F.map biprod.inr ≫ g)
  invFun h := F.map biprod.fst ≫ h.1 + F.map biprod.snd ≫ h.2
  left_inv g := by
    dsimp only
    rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, ← F.map_comp,
      ← F.map_comp, ← F.map_add, biprod.total, F.map_id, Category.id_comp]
  right_inv := fun ⟨a,b⟩ ↦ by
    simp [Preadditive.comp_add, ← F.map_comp_assoc]

private theorem bijective_precomp_sum_id (X Y T : C) [HasBinaryBiproduct X T]
    [HasBinaryBiproduct Y T] (f : X ⟶ Y) :
    Function.Bijective (fun g : F.obj (Y ⊞ T) ⟶ N ↦ F.map (biprod.map f (𝟙 T)) ≫ g) ↔
      Function.Bijective (fun g : F.obj Y ⟶ N ↦ F.map f ≫ g) := by
  let e := sumHomEquiv F N
  let t := fun g : F.obj Y ⟶ N ↦ F.map f ≫ g
  have eqn : (fun g : F.obj (Y ⊞ T) ⟶ N ↦ F.map (biprod.map f (𝟙 T)) ≫ g) =
      (e X T).symm ∘ Prod.map t id ∘ (e Y T) := by
    funext g
    apply (e X T).injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    apply Prod.ext <;> change F.map _ ≫ F.map _ ≫ g = _
    · rw [← F.map_comp_assoc, biprod.inl_map, F.map_comp, Category.assoc]; rfl
    · rw [← F.map_comp_assoc, biprod.inr_map, Category.id_comp]; rfl
  rw [eqn, Equiv.comp_bijective, Equiv.bijective_comp]
  exact ⟨fun hb ↦ ⟨fun a b hab ↦ congrArg Prod.fst
    (hb.1 (show Prod.map t id (a, (0 : F.obj T ⟶ N)) = Prod.map t id (b, 0) from Prod.ext hab rfl)),
    fun x ↦ by obtain ⟨y,hy⟩ := hb.2 (x, (0 : F.obj T ⟶ N)); exact ⟨y.1, congrArg Prod.fst hy⟩⟩,
    fun hb ↦ hb.prodMap Function.bijective_id⟩

end Additive

namespace TwoTerm

universe u

variable {R : Type u} [Ring R]

/-- A module inverts the differential under the contravariant Hom functor. -/
def InvertedOn (P : TwoTerm R) (N : ModuleCat.{u} R) : Prop :=
  Function.Bijective (fun g : P.target.obj ⟶ N ↦ P.differential.hom ≫ g)

theorem invertedOn_of_iso {Q : TwoTerm R} {X Y : ModuleCat.{u} R}
    (e : X ≅ Y) (h : Q.InvertedOn Y) : Q.InvertedOn X := by
  let a := Iso.homCongr (Iso.refl Q.target.obj) e
  let b := Iso.homCongr (Iso.refl Q.source.obj) e.symm
  let C := fun f : Q.target.obj ⟶ Y ↦ Q.differential.hom ≫ f
  have he : (fun f : Q.target.obj ⟶ X ↦ Q.differential.hom ≫ f) = b ∘ C ∘ a := by
    funext f
    change _ = (𝟙 _ ≫ (Q.differential.hom ≫ (𝟙 _ ≫ f ≫ e.hom)) ≫ e.inv)
    simp
  unfold TwoTerm.InvertedOn
  rw [he]
  exact b.bijective.comp (h.comp a.bijective)

@[simp] theorem invertedOn_directSum_contractible (P : TwoTerm R) (T : FiniteProjective R)
    (N : ModuleCat.{u} R) : (P.directSum (contractible T)).InvertedOn N ↔ P.InvertedOn N := by
  let F := forget₂ (FGModuleCat R) (ModuleCat.{u} R)
  let : F.Additive := ⟨rfl⟩
  change Function.Bijective (fun g : F.obj (P.target ⊞ T.val) ⟶ N ↦
    F.map (blockDifferential P.differential (𝟙 T.val) 0) ≫ g) ↔ _
  rw [blockDifferential_zero]
  exact bijective_precomp_sum_id F N _ _ _ _

/-- The zero projective class permits a single quotient of the original ring.
The quotient represents inversion of the differential on arbitrary restricted
modules and excludes a simple module. -/
theorem exists_quotient_inverting_of_class_zero [IsArtinianRing R] [IsNoetherianRing R]
    (P : TwoTerm R) (hc : P.projectiveClass = 0) (hd : ¬ IsIso P.differential) :
    ∃ I : TwoSidedIdeal R,
      (∃ (S : Type u) (_ : AddCommGroup S) (_ : Module R S),
        IsSimpleModule R S ∧ ¬ I ≤ (Module.annihilator R S).toTwoSided) ∧
      ∀ (T : Type u) [Ring T] (g : R →+* T),
        (∀ (N : Type u) [AddCommGroup N] [Module T N],
          letI := Module.compHom N g
          P.InvertedOn (ModuleCat.of R N)) ↔
        ∃! q : R ⧸ I.asIdeal →+* T, q.comp (Ideal.Quotient.mk I.asIdeal) = g := by
  obtain ⟨S,⟨e⟩⟩ := ProjectiveClass.exists_biprod_iso_of_of_eq
    (sub_eq_zero.mp hc : ProjectiveClass.of ⟨P.target,P.projective_target⟩ =
      ProjectiveClass.of ⟨P.source,P.projective_source⟩)
  let Q := P.directSum (contractible S)
  let i : Q.target ≅ Q.source := e
  let a := Q.differential ≫ i.hom
  let f : Module.End R Q.source := a.hom.hom
  have : Module.Finite R Q.source := Q.source.property
  have : Module.Projective R Q.source := Q.projective_source
  have hf : ¬ Function.Bijective f := by
    intro hb
    have : IsIso a := (FGModuleCat.isIso_iff_bijective a).2 hb
    have : IsIso Q.differential := by
      have eqn : Q.differential = a ≫ i.inv := by simp [a]
      rw [eqn]
      infer_instance
    have hi : IsIso (blockDifferential P.differential (𝟙 S.val) 0) := this
    rw [blockDifferential_zero] at hi
    exact hd (isIso_left_of_isIso_biprod_map _ (𝟙 S.val))
  obtain ⟨I,hS,hI⟩ := exists_quotient_inverting_endomorphism f hf
  refine ⟨I,hS,fun T _ g ↦ ?_⟩
  rw [← hI T g]
  apply forall_congr'
  intro N
  apply forall_congr'
  intro _
  apply forall_congr'
  intro _
  let := Module.compHom N g
  let V := ModuleCat.of R N
  rw [← invertedOn_directSum_contractible P S V]
  let F := forget₂ (FGModuleCat R) (ModuleCat.{u} R)
  let t := fun h : Q.target.obj ⟶ V ↦ Q.differential.hom ≫ h
  let s := (F.mapIso i.symm).homFromEquiv (Z := V)
  let b : (Q.source.obj ⟶ V) ≃ (Q.source →ₗ[R] N) := ModuleCat.homAddEquiv.toEquiv
  have he : (fun l : Q.source →ₗ[R] N ↦ l.comp f) = b ∘ t ∘ s ∘ b.symm := by
    funext l
    rfl
  rw [he, Equiv.comp_bijective]
  change Function.Bijective t ↔ _
  rw [← Function.comp_assoc, Equiv.bijective_comp, Equiv.bijective_comp]

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]
include k

/-- Every module inverting a differential also inverts each presilting
differential of the same integral class, over an arbitrary ground field. -/
theorem invertedOn_of_isPresilting_of_class_eq (P Q : TwoTerm R) (hP : P.IsPresilting)
    (hc : P.projectiveClass = Q.projectiveClass) (N : ModuleCat.{u} R) (hQ : Q.InvertedOn N) :
    P.InvertedOn N := by
  obtain ⟨S,T,⟨e₁⟩,⟨e₀⟩⟩ := exists_stable_term_isos P Q hc
  let P' := P.directSum (contractible S)
  let Q' := Q.directSum (contractible T)
  let i₁ : P'.source ≅ Q'.source := e₁
  let i₀ : P'.target ≅ Q'.target := e₀
  let σ := i₁.hom ≫ Q'.differential ≫ i₀.inv
  have hp' : P'.IsPresilting := (isPresilting_directSum_contractible_iff k P S).2 hP
  have hq' : Q'.InvertedOn N := (invertedOn_directSum_contractible Q T N).2 hQ
  let F := forget₂ (FGModuleCat R) (ModuleCat.{u} R)
  have hσ : Function.Bijective (Linear.leftComp k N σ.hom) := by
    let t := fun g : Q'.target.obj ⟶ N ↦ Q'.differential.hom ≫ g
    let s := ((F.mapIso i₀).homFromEquiv (Z := N))
    let r := ((F.mapIso i₁.symm).homFromEquiv (Z := N))
    have eqn : ⇑(Linear.leftComp k N σ.hom) = r ∘ t ∘ s := by
      funext g
      change F.map (i₁.hom ≫ Q'.differential ≫ i₀.inv) ≫ g =
        F.map i₁.hom ≫ F.map Q'.differential ≫ F.map i₀.inv ≫ g
      simp
    rw [eqn]
    exact r.bijective.comp (hq'.comp s.bijective)
  exact (invertedOn_directSum_contractible P S N).1
    (P'.bijective_leftComp_of_isPresilting k hp' σ N hσ)

/-- A presilting representative for the inversion comparison can be chosen
uniformly for every module inverting the given differential. -/
theorem exists_presilting_invertedOn_of_isEFinite (hR : IsEFinite R) (Q : TwoTerm R) :
    ∃ P : TwoTerm R, P.IsPresilting ∧ P.projectiveClass = Q.projectiveClass ∧
      ∀ N, Q.InvertedOn N → P.InvertedOn N := by
  obtain ⟨P,hP,hc⟩ := hR Q.projectiveClass
  exact ⟨P,hP,hc,invertedOn_of_isPresilting_of_class_eq k P Q hP hc⟩

end TwoTerm

end EFiniteCharacterizations
