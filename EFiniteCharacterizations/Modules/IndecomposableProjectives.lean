module

public import EFiniteCharacterizations.Modules.FiniteModuleMorphisms
public import EFiniteCharacterizations.Modules.ProjectiveBiproducts
public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.FiniteLength

/-! # Simple quotients of indecomposable projectives -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.FGModuleCat

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- Every nonzero finite module admits an epimorphism to a simple module. -/
theorem exists_simple_quotient {X : FGModuleCat.{u} R} (hX : ¬ IsZero X) :
    ∃ (S : FGModuleCat.{u} R) (f : X ⟶ S), Simple S ∧ Epi f := by
  have : Nontrivial X := not_subsingleton_iff_nontrivial.mp (fun h ↦ hX ((isZero_iff_subsingleton X).2 h))
  have : Module.Finite R X := X.property
  have : IsNoetherian R X := inferInstance
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (α := Submodule R X)
  let S := FGModuleCat.of R (X ⧸ N)
  have : IsSimpleModule R (X ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN
  let f : X ⟶ S := FGModuleCat.ofHom N.mkQ
  let F := forget₂ (FGModuleCat R) (ModuleCat.{u} R)
  have : Simple (F.obj S) := (simple_iff_isSimpleModule' (F.obj S)).2
    (show IsSimpleModule R (X ⧸ N) from inferInstance)
  exact ⟨S, f, F.simple_of_simple_obj S, (epi_iff_surjective f).mpr N.mkQ_surjective⟩

private theorem isZero_submodule_of_isZero_obj {X : FGModuleCat.{u} R} (A : Submodule R X)
    (h : IsZero (FGModuleCat.of R A)) : A = ⊥ := by
  have hs := (isZero_iff_subsingleton _).mp h
  exact le_antisymm (fun x hx ↦ (Submodule.mem_bot R).2
    (congrArg Subtype.val (@Subsingleton.elim A hs ⟨x, hx⟩ 0))) bot_le

private theorem eq_bot_or_eq_bot_of_compl {X : FGModuleCat.{u} R} (hX : Indecomposable X)
    {A B : Submodule R X} (hc : IsCompl A B) : A = ⊥ ∨ B = ⊥ := by
  let A' := FGModuleCat.of R A
  let B' := FGModuleCat.of R B
  let F := forget₂ (FGModuleCat R) (ModuleCat.{u} R)
  let e := (A.prodEquivOfIsCompl B hc).symm.toModuleIso
  let i : X ≅ A' ⊞ B' := F.preimageIso (e.trans
    ((forgetBiprodIso A' B').trans (ModuleCat.biprodIsoProd A'.obj B'.obj)).symm)
  exact (hX.2 A' B' i).imp (isZero_submodule_of_isZero_obj A) (isZero_submodule_of_isZero_obj B)

variable [IsArtinianRing R]

/-- By Fitting decomposition, an endomorphism of an indecomposable finite
module over an Artinian ring is nilpotent or invertible. -/
theorem fitting_nilpotent_or_isIso {X : FGModuleCat.{u} R} (hX : Indecomposable X)
    (f : X ⟶ X) : IsNilpotent (f.hom.hom : Module.End R X) ∨ IsIso f := by
  have : Module.Finite R X := X.property
  have : IsNoetherian R X := inferInstance
  let a : Module.End R X := f.hom.hom
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow a)
  rcases eq_bot_or_eq_bot_of_compl hX (hn (n+1) (Nat.le_succ n)) with hk | hr
  · have hi : Function.Injective (a ^ (n + 1)) := LinearMap.ker_eq_bot.mp hk
    have hs : Function.Surjective (a ^ (n + 1)) := LinearMap.range_eq_top.mp (by
      have h := (hn (n + 1) (Nat.le_succ n)).sup_eq_top
      rwa [hk, bot_sup_eq] at h)
    exact Or.inr ((isIso_iff_bijective f).mpr
      ⟨Module.End.injective_of_iterate_injective (by omega) hi,
        Module.End.surjective_of_iterate_surjective (by omega) hs⟩)
  · exact Or.inl ⟨n + 1, LinearMap.range_eq_bot.mp hr⟩

/-- An endomorphism acting as the identity on a nonzero quotient of an
indecomposable module is invertible. -/
theorem isIso_of_quotient_eq_self {X Y : FGModuleCat.{u} R} (hX : Indecomposable X)
    (p : X ⟶ Y) (hp : p ≠ 0) (a : X ⟶ X) (ha : a ≫ p = p) : IsIso a := by
  rcases fitting_nilpotent_or_isIso hX a with ⟨n, hn⟩ | hi
  · have ha' : p.hom.hom.comp a.hom.hom = p.hom.hom := congrArg (fun f : X ⟶ Y ↦ f.hom.hom) ha
    have hpow (m : ℕ) : p.hom.hom.comp ((a.hom.hom : Module.End R X) ^ m) = p.hom.hom := by
      induction m with
      | zero => simp [Module.End.one_eq_id]
      | succ m hm => rw [pow_succ', Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha', hm]
    apply (hp (FGModuleCat.hom_ext ?_)).elim
    simpa [hn] using (hpow n).symm
  · exact hi

/-- Indecomposable projectives admitting the same simple quotient are
isomorphic. The argument uses the two lifts of the quotient maps. -/
theorem nonempty_iso_of_common_quotient {P Q S : FGModuleCat.{u} R}
    [Module.Projective R P] [Module.Projective R Q] (hP : Indecomposable P) (hQ : Indecomposable Q)
    (p : P ⟶ S) (q : Q ⟶ S) [Epi p] [Epi q] (hS : ¬ IsZero S) : Nonempty (P ≅ Q) := by
  obtain ⟨f, hf⟩ := exists_lift_of_projective q p
  obtain ⟨g, hg⟩ := exists_lift_of_projective p q
  have hp : p ≠ 0 := fun hp ↦ hS (IsZero.iff_id_eq_zero _ |>.mpr
    ((cancel_epi p).mp (by rw [hp, zero_comp, zero_comp])))
  have hq : q ≠ 0 := fun hq ↦ hS (IsZero.iff_id_eq_zero _ |>.mpr
    ((cancel_epi q).mp (by rw [hq, zero_comp, zero_comp])))
  have : IsIso (f ≫ g) := isIso_of_quotient_eq_self hP p hp _ (by rw [Category.assoc, hg, hf])
  have : IsIso (g ≫ f) := isIso_of_quotient_eq_self hQ q hq _ (by rw [Category.assoc, hf, hg])
  have : Mono f := ⟨fun a b h ↦ (cancel_mono (f ≫ g)).mp (by simp only [← Category.assoc, h])⟩
  have : Epi f := ⟨fun a b h ↦ (cancel_epi (g ≫ f)).mp (by simp only [Category.assoc, h])⟩
  have : IsIso f := isIso_of_mono_of_epi f
  exact ⟨asIso f⟩

end EFiniteCharacterizations.FGModuleCat
