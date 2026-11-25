module

public import EFiniteCharacterizations.LinearAlgebra.FinitePowerCancellation
public import EFiniteCharacterizations.ScalarExtension.FieldExtensionTensorHom
public import EFiniteCharacterizations.ScalarExtension.RestrictionOfExtension
public import EFiniteCharacterizations.Presentations.RigidPair
public import EFiniteCharacterizations.Silting.ThickSubcategories.ThickPencil
public import Mathlib.CategoryTheory.Limits.Comma

/-!
# Uniqueness of two-term presilting complexes of a given `g`-vector

Lemma 2.1(2) (`lem:fan-lattice`) of the manuscript: over any ground field `k`, two
two-term presilting complexes with the same class in `K₀(proj R)` are isomorphic in
the homotopy category (`nonempty_homotopyIso_of_isPresilting_of_class_eq`), whether
or not they are basic.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations

noncomputable section

variable (R : Type u) [Ring R]

/-- The coordinatewise finite power of a finite module and its maps. -/
def modulePower (n : ℕ) : FGModuleCat.{u} R ⥤ FGModuleCat.{u} R where
  obj X := FGModuleCat.of R (Fin n → X)
  map f := FGModuleCat.ofHom (LinearMap.pi fun i : Fin n ↦ f.hom.hom.comp (LinearMap.proj i))
  map_id _ := rfl
  map_comp _ _ := rfl

instance (n : ℕ) : (modulePower R n).Additive where
  map_add := by intros; rfl

namespace FieldExtension

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Algebra k R]
  [Module.Finite k R] [Module.Finite k F]

/-- On ground modules, extending and then restricting is naturally a finite power. -/
def restrictExtendPowerIso {n : ℕ} (b : Module.Basis (Fin n) k F) :
    (ScalarCategory.of (k := k) (S := F) (C := FGModuleCat.{u} R)) ⋙
      extendScalarCategory k F R ⋙ restrict k F R ≅ modulePower R n := by
  refine NatIso.ofComponents (fun X ↦ (restrictExtendBasisEquiv k F R b X).toFGModuleCatIso) ?_
  intro X Y f
  change (restrict k F R).map (homTensorMap k F R X Y (1 ⊗ₜ[k] f)) ≫ _ = _
  rw [homTensorMap_tmul, one_smul]
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change F ⊗[k] (X.obj : Type u) at z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro c x
    change restrictExtendBasisEquiv k F R b Y ((extendMap k F R f).hom.hom (c ⊗ₜ[k] x)) =
      fun i ↦ f.hom.hom (restrictExtendBasisEquiv k F R b X (c ⊗ₜ[k] x) i)
    simp only [extendMap_tmul, restrictExtendBasisEquiv_tmul]
    funext i
    exact ((f.hom.hom.restrictScalars k).map_smul _ _).symm
  · intro z w hz hw
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hz hw).trans (map_add _ _ _).symm)

end FieldExtension

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

private def transportArrowIso {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) (H : D ⥤ C) (P : C ⥤ C) (e : G ⋙ H ≅ P) (A B : Arrow C)
    (i : G.mapArrow.obj A ≅ G.mapArrow.obj B) : P.mapArrow.obj A ≅ P.mapArrow.obj B :=
  let t := (Functor.mapArrowFunctor C C).mapIso e
  (t.app A).symm ≪≫ H.mapArrow.mapIso i ≪≫ t.app B

set_option backward.isDefEq.respectTransparency false in
/-- Rigid differentials on the same modules become isomorphic squares after
taking the same positive number of copies on both sides. -/
theorem exists_modulePower_iso_of_rigid_pair [Finite k] {X Y : FGModuleCat.{u} R} (p q : X ⟶ Y)
    (hp : Function.Surjective (boundaryLinear k p p))
    (hq : Function.Surjective (boundaryLinear k q q)) :
    ∃ n : ℕ, 0 < n ∧ Nonempty ((modulePower R n).mapArrow.obj (Arrow.mk p) ≅
      (modulePower R n).mapArrow.obj (Arrow.mk q)) := by
  have (M N : FGModuleCat.{u} R) : Module.Finite k (M ⟶ N) := finiteModuleHom_isFinite k M N
  obtain ⟨F, _, _, _, a, b, hab⟩ := exists_finite_field_iso_square_of_rigid_pair k p q hp hq
  have : Module.Finite k F := Module.Finite.of_finite
  let G : FGModuleCat.{u} R ⥤ ScalarCategory k F (FGModuleCat.{u} R) := ScalarCategory.of
  let H := FieldExtension.extendScalarCategory k F R ⋙ FieldExtension.restrict k F R
  let i : G.mapArrow.obj (Arrow.mk p) ≅ G.mapArrow.obj (Arrow.mk q) :=
    Arrow.isoMk' (G.map p) (G.map q) a b hab
  let e : G ⋙ H ≅ modulePower R (Module.finrank k F) :=
    FieldExtension.restrictExtendPowerIso R k F (Module.finBasis k F)
  exact ⟨Module.finrank k F, Module.finrank_pos, ⟨transportArrowIso G H _ e _ _ i⟩⟩

private def powerProjection (n : ℕ) (A : Arrow (FGModuleCat.{u} R)) (i : Fin n) :
    (modulePower R n).mapArrow.obj A ⟶ A :=
  Arrow.homMk (FGModuleCat.ofHom (LinearMap.proj i)) (FGModuleCat.ofHom (LinearMap.proj i)) rfl

private def powerFanLimit (n : ℕ) (A : Arrow (FGModuleCat.{u} R)) :
    IsLimit (Fan.mk _ (powerProjection R n A)) := by
  refine Fan.IsLimit.mk _
    (fun s ↦ Arrow.homMk (FGModuleCat.ofHom (LinearMap.pi fun i ↦ (s.proj i).left.hom.hom))
      (FGModuleCat.ofHom (LinearMap.pi fun i ↦ (s.proj i).right.hom.hom)) ?_) ?_ ?_
  · apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    exact DFunLike.congr_fun (congrArg (fun m ↦ m.hom.hom) (s.proj i).w) x
  · intro s i
    exact Arrow.hom_ext _ _ rfl rfl
  · intro s m h
    apply Arrow.hom_ext <;> apply FGModuleCat.hom_ext <;> apply LinearMap.ext <;> intro x <;> funext i
    · exact DFunLike.congr_fun (congrArg (fun a ↦ a.left.hom.hom) (h i)) x
    · exact DFunLike.congr_fun (congrArg (fun a ↦ a.right.hom.hom) (h i)) x

private theorem infinite_rigid_square [Infinite k] {X Y : FGModuleCat.{u} R} (p q : X ⟶ Y)
    (hp : Function.Surjective (boundaryLinear k p p)) (hq : Function.Surjective (boundaryLinear k q q)) :
    Nonempty (Arrow.mk p ≅ Arrow.mk q) := by
  have (M N : FGModuleCat.{u} R) : Module.Finite k (M ⟶ N) := finiteModuleHom_isFinite k M N
  obtain ⟨d, hd, hiso⟩ := exists_iso_square_of_rigid_pair_polynomial k p q hp hq
  have hx : ∃ x : k, d.eval x ≠ 0 := by
    by_contra! hz
    exact hd (Polynomial.zero_of_eval_zero d hz)
  obtain ⟨x,hx⟩ := hx
  obtain ⟨a,b,hab⟩ := hiso (Polynomial.aeval x) (by simpa using hx)
  let G : FGModuleCat.{u} R ⥤ ScalarCategory k k (FGModuleCat.{u} R) := ScalarCategory.of
  let : G.Full := ⟨fun {M N} ↦ (TensorProduct.lid k (M ⟶ N)).symm.surjective⟩
  let : G.Faithful := ⟨fun {M N} ↦ (TensorProduct.lid k (M ⟶ N)).symm.injective⟩
  refine ⟨Arrow.isoMk' p q (G.preimageIso a) (G.preimageIso b) (G.map_injective ?_)⟩
  change a.hom ≫ G.map q = G.map p ≫ b.hom at hab
  simpa only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage] using hab

/-- Rigid differentials on the same modules have isomorphic squares over k itself. -/
theorem nonempty_arrow_iso_of_rigid_pair [IsNoetherianRing R] {X Y : FGModuleCat.{u} R} (p q : X ⟶ Y)
    (hp : Function.Surjective (boundaryLinear k p p)) (hq : Function.Surjective (boundaryLinear k q q)) :
    Nonempty (Arrow.mk p ≅ Arrow.mk q) := by
  cases finite_or_infinite k with
  | inr _ => exact infinite_rigid_square R k p q hp hq
  | inl _ =>
    have fin (M N : FGModuleCat.{u} R) : Finite (M ⟶ N) := by
      have := finiteModuleHom_isFinite k M N
      let b := Module.finBasis k (M ⟶ N)
      exact Finite.of_injective b.equivFun b.equivFun.injective
    have (A B : Arrow (FGModuleCat.{u} R)) : Finite (A ⟶ B) :=
      Finite.of_injective (fun f : A ⟶ B ↦ (f.left, f.right))
        (fun _ _ h ↦ Arrow.hom_ext _ _ (congrArg Prod.fst h) (congrArg Prod.snd h))
    obtain ⟨n,hn,⟨j⟩⟩ := exists_modulePower_iso_of_rigid_pair R k p q hp hq
    let : HasFiniteProducts (Arrow (FGModuleCat.{u} R)) := ⟨fun _ ↦ inferInstance⟩
    let iso (A : Arrow (FGModuleCat.{u} R)) := (powerFanLimit R n A).conePointUniqueUpToIso (limit.isLimit _)
    exact nonempty_iso_of_finite_homs_of_power_iso (Arrow.mk p) (Arrow.mk q) hn
      ((iso (Arrow.mk p)).symm ≪≫ j ≪≫ iso (Arrow.mk q))

namespace TwoTerm

variable {R} [IsNoetherianRing R]

private abbrev toHomotopy := doubleFunctor (C := FGModuleCat.{u} R) ⋙ HomotopyCategory.quotient _ _

private def removeContractible (P : TwoTerm R) (S : FiniteProjective R) :
    (P.directSum (contractible S)).homotopyObject ≅ P.homotopyObject := by
  let H := toHomotopy (R := R)
  let Q := contractible S
  change H.obj (P.directSum Q).asArrow ≅ H.obj P.asArrow
  have hz : IsZero (H.obj Q.asArrow) := isZero_contractible S
  refine ⟨H.map (fstDirectSum P Q), H.map (inlDirectSum P Q), ?_, ?_⟩
  · have h := congrArg H.map (totalDirectSum P Q)
    rw [H.map_add, H.map_comp, H.map_comp, H.map_id] at h
    rw [hz.eq_of_tgt (H.map (sndDirectSum P Q)) 0, zero_comp, add_zero] at h
    exact h
  · rw [← H.map_comp, inlDirectSum_fstDirectSum, H.map_id]

include k in
/-- Over every ground field, presilting two-term complexes with equal projective
class are isomorphic in the homotopy category. -/
theorem nonempty_homotopyIso_of_isPresilting_of_class_eq (P Q : TwoTerm R)
    (hp : P.IsPresilting) (hq : Q.IsPresilting) (h : P.projectiveClass = Q.projectiveClass) :
    Nonempty (P.homotopyObject ≅ Q.homotopyObject) := by
  obtain ⟨S, T, ⟨i₁⟩, ⟨i₀⟩⟩ := exists_stable_term_isos P Q h
  let P' := P.directSum (contractible S)
  let Q' := Q.directSum (contractible T)
  let e₁ : P'.source ≅ Q'.source := i₁
  let e₀ : P'.target ≅ Q'.target := i₀
  let _ := Q'.projective_source
  let _ := Q'.projective_target
  let v := e₁.inv ≫ P'.differential ≫ e₀.hom
  let U := ofDifferential v
  have hv : e₁.hom ≫ U.differential = P'.differential ≫ e₀.hom := e₁.hom_inv_id_assoc _
  let i : P'.asArrow ≅ U.asArrow := Arrow.isoMk' _ _ e₁ e₀ hv
  have hu := (isPresilting_iff_of_term_isos k P' U e₁ e₀ hv).1
    ((isPresilting_directSum_contractible_iff k P S).2 hp)
  have hq' := (isPresilting_directSum_contractible_iff k Q T).2 hq
  obtain ⟨j⟩ := nonempty_arrow_iso_of_rigid_pair R k v Q'.differential
    ((isPresilting_iff_boundaryLinear_surjective (k := k) U).1 hu)
    ((isPresilting_iff_boundaryLinear_surjective (k := k) Q').1 hq')
  let H := toHomotopy (R := R)
  exact ⟨(removeContractible P S).symm ≪≫ H.mapIso (i ≪≫ j) ≪≫ removeContractible Q T⟩

end TwoTerm
end
end EFiniteCharacterizations
