/-
Adapted from the pretorsion-image-closed formalization,
PretorsionImageClosed.Length.Modules
(commit e6e95f6c295649bccf0ca476c9a5b008320e9443, Apache 2.0).
-/
module

public import EFiniteCharacterizations.Modules.FiniteModuleMorphisms
public import EFiniteCharacterizations.Stability.Weights
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Length

/-! # Composition length of finite modules -/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits

namespace EFiniteCharacterizations

private theorem toNat_lt_toNat_of_lt {m n : ℕ∞} (h : m < n) (hn : n ≠ ⊤) : m.toNat < n.toNat := by
  have hm : m ≠ ⊤ := ne_top_of_lt h
  exact Nat.cast_lt.1 (by rwa [ENat.natCast_toNat hm, ENat.natCast_toNat hn])

namespace FGModuleCat

variable {R : Type*} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]

/-- The composition length of a finitely generated module over a Noetherian
Artinian ring, as a natural number. -/
noncomputable def moduleLength (X : FGModuleCat R) : ℕ := (Module.length R X).toNat

theorem moduleLength_coe (X : FGModuleCat R) : (moduleLength X : ℕ∞) = Module.length R X :=
  ENat.natCast_toNat Module.length_ne_top

theorem moduleLength_eq_zero_iff (X : FGModuleCat R) : moduleLength X = 0 ↔ Subsingleton X := by
  rw [← Module.length_eq_zero_iff (R := R), ← moduleLength_coe]
  exact_mod_cast Iff.rfl

theorem moduleLength_eq_zero_iff_isZero (X : FGModuleCat R) :
  moduleLength X = 0 ↔ IsZero X := by
  rw [moduleLength_eq_zero_iff, isZero_iff_subsingleton]

omit [IsNoetherianRing R] [IsArtinianRing R] in
theorem moduleLength_eq_of_iso {X Y : FGModuleCat R} (e : X ≅ Y) :
  moduleLength X = moduleLength Y := by
  rw [moduleLength, moduleLength, LinearEquiv.length_eq (FGModuleCat.isoToLinearEquiv e)]

theorem moduleLength_lt_of_mono {X Y : FGModuleCat R} (f : X ⟶ Y) [Mono f]
    (hni : ¬ IsIso f) : moduleLength X < moduleLength Y := by
  have hinj : Function.Injective f.hom.hom := (mono_iff_injective f).1 inferInstance
  have hns : LinearMap.range f.hom.hom ≠ ⊤ := fun h =>
    hni ((isIso_iff_bijective f).2 ⟨hinj, LinearMap.range_eq_top.1 h⟩)
  have h1 : Module.length R X = Module.length R (LinearMap.range f.hom.hom) :=
    LinearEquiv.length_eq (LinearEquiv.ofInjective f.hom.hom hinj)
  have h2 := Submodule.length_lt hns
  rw [moduleLength, moduleLength, h1]
  exact toNat_lt_toNat_of_lt h2 Module.length_ne_top

theorem moduleLength_lt_of_epi {X Y : FGModuleCat R} (f : X ⟶ Y) [Epi f]
    (hni : ¬ IsIso f) : moduleLength Y < moduleLength X := by
  have hsurj : Function.Surjective f.hom.hom := (epi_iff_surjective f).1 inferInstance
  have hni' : LinearMap.ker f.hom.hom ≠ ⊥ := fun h =>
    hni ((isIso_iff_bijective f).2 ⟨LinearMap.ker_eq_bot.1 h, hsurj⟩)
  have hadd : Module.length R X = Module.length R (LinearMap.ker f.hom.hom) + Module.length R Y :=
    Module.length_eq_add_of_exact (LinearMap.ker f.hom.hom).subtype f.hom.hom
      (Submodule.subtype_injective _) hsurj (LinearMap.exact_subtype_ker_map f.hom.hom)
  have hpos : 0 < Module.length R (LinearMap.ker f.hom.hom) :=
    Module.length_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 hni')
  have hlt : Module.length R Y < Module.length R X := by
    rw [hadd]
    exact ENat.lt_add_left Module.length_ne_top hpos
  exact toNat_lt_toNat_of_lt hlt Module.length_ne_top

theorem moduleLength_shortExact (S : ShortComplex (FGModuleCat R)) (hS : S.ShortExact) :
    moduleLength S.X₂ = moduleLength S.X₁ + moduleLength S.X₃ := by
  let F := forget₂ (FGModuleCat R) (ModuleCat R)
  have h := hS.map_of_exact F
  have hlen : Module.length R S.X₂ = Module.length R S.X₁ + Module.length R S.X₃ :=
    Module.length_eq_add_of_exact S.f.hom.hom S.g.hom.hom h.moduleCat_injective_f
      h.moduleCat_surjective_g ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp h.exact)
  have hnat := congrArg ENat.toNat hlen
  rw [ENat.toNat_add Module.length_ne_top Module.length_ne_top] at hnat
  exact hnat

/-- Composition length as an additive weight. -/
noncomputable def lengthWeight (R : Type*) [Ring R] [IsNoetherianRing R] [IsArtinianRing R] :
    Weight (FGModuleCat R) :=
  GrothendieckGroup.lift (fun M ↦ (moduleLength M : ℤ))
    (fun S hS ↦ by exact_mod_cast moduleLength_shortExact S hS)

@[simp] theorem lengthWeight_eval (M : FGModuleCat R) :
    Weight.eval (C := FGModuleCat R) (lengthWeight R) M = (moduleLength M : ℤ) :=
  GrothendieckGroup.lift_of (C := FGModuleCat R) _ _ M

/-- The ambient Grothendieck class of a nonzero finite module is nonzero. -/
theorem class_ne_zero {M : FGModuleCat R} (hM : ¬ IsZero M) : GrothendieckGroup.of M ≠ 0 := by
  intro h
  have hlen : Weight.eval (C := FGModuleCat R) (lengthWeight R) M = 0 := by
    unfold Weight.eval
    rw [h, map_zero]
  apply hM
  rw [lengthWeight_eval] at hlen
  exact (moduleLength_eq_zero_iff_isZero M).1 (by exact_mod_cast hlen)

end FGModuleCat

end EFiniteCharacterizations
