module

public import EFiniteCharacterizations.Modules.CompositionLength
public import EFiniteCharacterizations.Modules.HomDimension
public import EFiniteCharacterizations.Presentations.TwoTerm

/-! # Integral Hom weights of finite projectives -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

theorem homFinrank_shortExact_of_projective (P : FGModuleCat.{u} R) [Module.Projective R P]
    (S : ShortComplex (FGModuleCat.{u} R)) (hS : S.ShortExact) :
    homFinrank k P S.X₂ = homFinrank k P S.X₁ + homFinrank k P S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  have := finiteModuleHom_isFinite k P S.X₂
  let a := Linear.rightComp k P S.f
  let b := Linear.rightComp k P S.g
  have ha : Function.Injective a := fun x y h ↦ (cancel_mono S.f).mp h
  have hb : Function.Surjective b := by
    intro z
    have hs := (FGModuleCat.epi_iff_surjective S.g).1 inferInstance
    obtain ⟨v, hv⟩ := Module.projective_lifting_property S.g.hom.hom z.hom.hom hs
    refine ⟨ObjectProperty.homMk (ModuleCat.ofHom v), ?_⟩
    exact FGModuleCat.hom_ext hv
  have hker : LinearMap.ker b = LinearMap.range a := by
    ext y
    constructor
    · intro hy
      have hy' : y ≫ S.g = 0 := hy
      let w := KernelFork.IsLimit.lift' hS.fIsKernel y hy'
      exact ⟨w.val, w.property⟩
    · rintro ⟨x, rfl⟩
      change (x ≫ S.f) ≫ S.g = 0
      rw [Category.assoc, S.zero, comp_zero]
  have hr := b.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hb, finrank_top, hker, LinearMap.finrank_range_of_inj ha,
    add_comm] at hr
  simpa only [homFinrank_eq_finrank] using hr.symm

/-- Evaluation on a finite module by the dimension of Hom from a fixed projective. -/
noncomputable def projectiveHomWeight (P : FGModuleCat.{u} R) [Module.Projective R P] :
    Weight (FGModuleCat.{u} R) :=
  GrothendieckGroup.lift (fun M ↦ (homFinrank k P M : ℤ))
    (fun S hS ↦ by exact_mod_cast homFinrank_shortExact_of_projective k P S hS)

@[simp] theorem projectiveHomWeight_eval (P : FGModuleCat.{u} R) [Module.Projective R P]
    (M : FGModuleCat.{u} R) : (projectiveHomWeight k P).eval M = homFinrank k P M :=
  GrothendieckGroup.lift_of _ _ M

/-- Total dimension over the ground field, regarded as an additive weight. -/
noncomputable def dimensionWeight : Weight (FGModuleCat.{u} R) :=
  projectiveHomWeight k (FGModuleCat.of R R)

@[simp] theorem dimensionWeight_eval (M : FGModuleCat.{u} R) :
    (dimensionWeight (R := R) k).eval M = Module.finrank k (M.obj : Type u) := by
  rw [dimensionWeight, projectiveHomWeight_eval, homFinrank_eq_finrank]
  exact_mod_cast ((finiteModuleHomLinearEquiv k (FGModuleCat.of R R) M).trans
    (LinearMap.ringLmapEquivSelf R k (M.obj : Type u))).finrank_eq

theorem dimensionWeight_pos (M : FGModuleCat.{u} R) (hM : ¬ IsZero M) :
    0 < (dimensionWeight (R := R) k).eval M := by
  have : Module.Finite R (M.obj : Type u) := M.property
  have : Module.Finite k (M.obj : Type u) := Module.Finite.trans R _
  have hnt : Nontrivial (M.obj : Type u) :=
    not_subsingleton_iff_nontrivial.mp (hM ∘ (FGModuleCat.isZero_iff_subsingleton M).2)
  rw [dimensionWeight_eval, Int.natCast_pos]
  exact Module.finrank_pos_iff.mpr hnt

/-- The Euler weight of a two-term projective complex. -/
noncomputable def TwoTerm.eulerWeight (P : TwoTerm R) : Weight (FGModuleCat.{u} R) := by
  have := P.projective_source
  have := P.projective_target
  exact projectiveHomWeight k P.target - projectiveHomWeight k P.source

theorem TwoTerm.eulerWeight_eval (P : TwoTerm R) (M : FGModuleCat.{u} R) :
    (P.eulerWeight k).eval M = (homFinrank k P.target M : ℤ) - homFinrank k P.source M := by
  have := P.projective_source
  have := P.projective_target
  change (projectiveHomWeight k P.target).eval M - (projectiveHomWeight k P.source).eval M = _
  rw [projectiveHomWeight_eval, projectiveHomWeight_eval]

end EFiniteCharacterizations
