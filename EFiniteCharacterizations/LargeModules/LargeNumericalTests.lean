module

public import EFiniteCharacterizations.LargeModules.LargePerpendicular

/-! # Finite numerical tests for precomposition on arbitrary modules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

theorem injective_precomposition_of_finite_submodule_tests (P : TwoTerm R) (hp : P.IsPresilting)
    (M : ModuleCat.{u} R) (h : ∀ (N : FGModuleCat.{u} R) (i : N.obj ⟶ M),
      Function.Injective i.hom → (P.eulerWeight k).eval N ≤ 0) :
    Function.Injective (fun f : P.target →ₗ[R] M ↦ f.comp P.differential.hom.hom) := by
  let d := P.differential.hom.hom
  suffices hz : ∀ f : P.target →ₗ[R] M, f.comp d = 0 → f = 0 by
    intro a b hab
    exact sub_eq_zero.mp (hz (a-b) (by rw [LinearMap.sub_comp,sub_eq_zero]; exact hab))
  intro f hf
  let U := LinearMap.range f
  let N := FGModuleCat.of R U
  let b : P.target ⟶ N := FGModuleCat.ofHom f.rangeRestrict
  have hb : P.differential ≫ b = 0 := by
    ext x
    exact LinearMap.congr_fun hf x
  have hs := (P.nonpos_eulerWeight_all_subobjects_iff k hp N).1 (fun {X} i _ ↦
    h X (i.hom ≫ ModuleCat.ofHom U.subtype) (Subtype.val_injective.comp ((FGModuleCat.mono_iff_injective i).1 inferInstance)))
  have he := hs.elim (cokernel.desc _ b hb) 0
  have he' := cokernel.π_desc _ b hb
  rw [he,comp_zero] at he'
  exact LinearMap.ext fun x ↦ congrArg Subtype.val (congrArg (fun t : P.target ⟶ N ↦ t.hom.hom x) he'.symm)

/-- A functional obstructing surjectivity is represented by a map to the
finite Nakayama module. Its image is a finite quotient detecting the obstruction. -/
theorem surjective_precomposition_of_finite_quotient_tests (P : TwoTerm R) (hp : P.IsPresilting)
    (M : ModuleCat.{u} R) (h : ∀ (Q : FGModuleCat.{u} R) (q : M ⟶ Q.obj),
      Function.Surjective q.hom → 0 ≤ (P.eulerWeight k).eval Q) :
    Function.Surjective (fun f : P.target →ₗ[R] M ↦ f.comp P.differential.hom.hom) := by
  let d := P.differential.hom.hom
  have := P.projective_source
  have := P.projective_target
  change Function.Surjective (d.lcomp k M)
  rw [← LinearMap.dualMap_injective_iff, ← LinearMap.ker_eq_bot]
  apply eq_bot_iff.mpr
  intro χ hχ
  change (d.lcomp k M).dualMap χ = 0 at hχ
  let f := nakayamaHomEquiv k R P.source M χ
  have hf : (d.nakayamaMap (k := k)).comp f = 0 := by
    rw [← nakayamaHomEquiv_dualMap_lcomp, hχ, map_zero]
  let U := LinearMap.range f
  have : Module.Finite R (NakayamaModule k R P.source) := (nakayamaObject k P.source).property
  let Q := FGModuleCat.of R U
  let i : Q ⟶ nakayamaObject k P.source := FGModuleCat.ofHom U.subtype
  have hi : i ≫ nakayamaMorphism k P.differential = 0 := by
    ext x
    obtain ⟨y,hy⟩ := x.property
    change d.nakayamaMap (k := k) x.val = 0
    rw [← hy]
    exact LinearMap.congr_fun hf y
  have hs := (P.nonneg_eulerWeight_all_quotients_iff k hp Q).1 (fun {X} q _ ↦
    h X (ModuleCat.ofHom f.rangeRestrict ≫ q.hom)
      (((FGModuleCat.epi_iff_surjective q).1 inferInstance).comp f.surjective_rangeRestrict))
  change Subsingleton (Q ⟶ kernel (nakayamaMorphism k P.differential)) at hs
  have he := hs.elim (kernel.lift _ i hi) 0
  have he' := kernel.lift_ι _ i hi
  rw [he,zero_comp] at he'
  apply (nakayamaHomEquiv k R P.source M).map_eq_zero_iff.mp
  exact LinearMap.ext fun x ↦ congrArg (fun t : Q ⟶ nakayamaObject k P.source ↦ t.hom.hom (f.rangeRestrict x)) he'.symm

end EFiniteCharacterizations.TwoTerm
