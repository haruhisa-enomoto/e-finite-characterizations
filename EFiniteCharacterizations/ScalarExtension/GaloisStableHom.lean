module

public import EFiniteCharacterizations.Subcategories.TorsionPairs
public import EFiniteCharacterizations.Stability.StableIsotypicQuotients
public import EFiniteCharacterizations.LinearAlgebra.GaloisComponents

/-! # Galois-semilinear maps between stable extension modules -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Module
open scoped ModuleCat.Algebra TensorProduct

universe u
namespace EFiniteCharacterizations.FieldExtension

variable (k F R : Type u) [Field k] [Field F] [Algebra k F] [Ring R] [Algebra k R]
  [Module.Finite k R] [Module.Finite k F]
local notation "A" => ExtendedAlgebra k F R

/-- A map on restrictions intertwines the extension-field action up to σ. -/
def IsGaloisHom {X Y : FGModuleCat.{u} A} (σ : Gal(F/k))
    (f : restrictObj k F R X ⟶ restrictObj k F R Y) : Prop :=
  ∀ (c : F) (x : X), f.hom.hom (scalarActionMap k F R X c x) =
    scalarActionMap k F R Y (σ c) (f.hom.hom x)

theorem exists_galoisHom [IsGalois k F] {X Y : FGModuleCat.{u} A}
    (f : restrictObj k F R X ⟶ restrictObj k F R Y) (hf : f ≠ 0) :
    ∃ (σ : Gal(F/k)) (g : restrictObj k F R X ⟶ restrictObj k F R Y), g ≠ 0 ∧ IsGaloisHom k F R σ g := by
  classical
  let := isScalarTower_ground_extension k F R X.obj
  let := isScalarTower_ground_extension k F R Y.obj
  let eX := restrictVectorSpaceEquiv k F R X.obj
  let eY := restrictVectorSpaceEquiv k F R Y.obj
  let f₀ : X →ₗ[k] Y := eY.toLinearMap.comp ((f.hom.hom.restrictScalars k).comp eX.symm.toLinearMap)
  let b := Module.finBasis k F
  let g₀ (σ : Gal(F/k)) : restrictObj k F R X →ₗ[R] restrictObj k F R Y :=
    ∑ i, (scalarActionMap k F R Y (σ (b.traceDual i))).comp (f.hom.hom.comp (scalarActionMap k F R X (b i)))
  let g (σ : Gal(F/k)) : restrictObj k F R X ⟶ restrictObj k F R Y := ObjectProperty.homMk (ModuleCat.ofHom (g₀ σ))
  have hg (σ : Gal(F/k)) (x : X) : (g σ).hom.hom x = galoisComponent b f₀ σ x := by
    change g₀ σ (show restrictObj k F R X from x) = _
    let l i := (scalarActionMap k F R Y (σ (b.traceDual i))).comp (f.hom.hom.comp (scalarActionMap k F R X (b i)))
    exact (LinearMap.sum_apply Finset.univ l (show restrictObj k F R X from x)).trans (by rfl)
  have hne : ∃ σ, g σ ≠ 0 := by
    by_contra! h
    apply hf
    ext x
    have he := sum_galoisComponent b f₀ (show X from x)
    exact he.symm.trans (Finset.sum_eq_zero fun σ _ ↦ (hg σ x).symm.trans (by rw [h σ]; rfl))
  obtain ⟨σ,hσ⟩ := hne
  refine ⟨σ,g σ,hσ,fun c x ↦ ?_⟩
  change (g σ).hom.hom (show X from c • x) = σ c • (show Y from (g σ).hom.hom x)
  rw [hg,hg,galoisComponent_smul]

variable [IsNoetherianRing R] [IsNoetherianRing (ExtendedAlgebra k F R)]

private theorem weights_ker_range {θ : Weight (FGModuleCat.{u} R)} {M N : FGModuleCat.{u} R}
    (hs : θ.IsSemistable M) (ht : θ.IsSemistable N) (f : M →ₗ[R] N) :
    θ.eval (FGModuleCat.of R (LinearMap.ker f)) = 0 ∧
      θ.eval (FGModuleCat.of R (LinearMap.range f)) = 0 := by
  let K := LinearMap.ker f
  let I := LinearMap.range f
  let i : FGModuleCat.of R K ⟶ M := FGModuleCat.ofHom K.subtype
  let j : FGModuleCat.of R I ⟶ N := FGModuleCat.ofHom I.subtype
  let q : M ⟶ FGModuleCat.of R I := FGModuleCat.ofHom f.rangeRestrict
  let _ : Mono i := (FGModuleCat.mono_iff_injective i).2 Subtype.val_injective
  let _ : Mono j := (FGModuleCat.mono_iff_injective j).2 Subtype.val_injective
  obtain ⟨w,hw⟩ := shortExact_of_range_ker i q Subtype.val_injective (LinearMap.range_eq_top.mp f.range_rangeRestrict)
    (by change K.subtype.range = f.rangeRestrict.ker; rw [Submodule.range_subtype,LinearMap.ker_rangeRestrict])
  have he := θ.eval_shortExact _ hw
  change θ.eval M = θ.eval (FGModuleCat.of R K) + θ.eval (FGModuleCat.of R I) at he
  have hzero := hs.1
  have hK := hs.2 i
  have hI := ht.2 j
  change θ.eval (FGModuleCat.of R K) ≤ 0 at hK
  change θ.eval (FGModuleCat.of R I) ≤ 0 at hI
  change θ.eval (FGModuleCat.of R K) = 0 ∧ θ.eval (FGModuleCat.of R I) = 0
  omega

private theorem eq_bot_or_top_of_invariant {P : TwoTerm R} {N : FGModuleCat.{u} A}
    (hn : ((extendTwoTerm k F R P).eulerWeight F).IsStable N) (U : Submodule R (restrictObj k F R N))
    (hU : ∀ c : F, ∀ x ∈ U, scalarActionMap k F R N c x ∈ U)
    (hz : (P.eulerWeight k).eval (FGModuleCat.of R U) = 0) : U = ⊥ ∨ U = ⊤ := by
  let V := ofInvariantSubmodule k F R N U hU
  let Z := FGModuleCat.of A V
  let i : Z ⟶ N := FGModuleCat.ofHom V.subtype
  let _ : Mono i := (FGModuleCat.mono_iff_injective i).2 Subtype.val_injective
  have he := eval_eq_of_invariantSubmodule k F R N U hU (P.eulerWeight k)
  rw [hz,eulerWeight_eval_restrictObj] at he
  have h0 : ((extendTwoTerm k F R P).eulerWeight F).eval Z = 0 :=
    (mul_eq_zero.mp he.symm).resolve_left (by exact_mod_cast (Module.finrank_pos (R := k) (M := F)).ne')
  by_cases ht : IsIso i
  · right
    exact Submodule.eq_top_iff'.mpr fun x ↦ by
      obtain ⟨z,hz⟩ := ((FGModuleCat.isIso_iff_bijective i).1 ht).2 x
      exact hz ▸ z.property
  · left
    have hzero : IsZero Z := by by_contra hnz; exact (hn.2.2 i hnz ht).ne h0
    let hs := (FGModuleCat.isZero_iff_subsingleton Z).1 hzero
    exact eq_bot_iff.mpr fun x hx ↦ congrArg Subtype.val (hs.elim (⟨x,hx⟩ : V) 0)

/-- A nonzero semilinear map between stable extension modules is bijective
if the two restrictions are semistable at both corresponding weights. -/
theorem bijective_of_galoisHom {P Q : TwoTerm R} {X Y : FGModuleCat.{u} A} {σ : Gal(F/k)}
    {f : restrictObj k F R X ⟶ restrictObj k F R Y} (hf : f ≠ 0) (hg : IsGaloisHom k F R σ f)
    (hx : ((extendTwoTerm k F R P).eulerWeight F).IsStable X)
    (hy : ((extendTwoTerm k F R Q).eulerWeight F).IsStable Y)
    (hxQ : (Q.eulerWeight k).IsSemistable (restrictObj k F R X))
    (hyP : (P.eulerWeight k).IsSemistable (restrictObj k F R Y)) : Function.Bijective f.hom.hom := by
  let l := f.hom.hom
  have h₁ := (weights_ker_range R ((isSemistable_restrictObj_iff k F R P X).2 hx.isSemistable) hyP l).1
  have h₂ := (weights_ker_range R hxQ ((isSemistable_restrictObj_iff k F R Q Y).2 hy.isSemistable) l).2
  have hn : l ≠ 0 := fun he ↦ hf (FGModuleCat.hom_ext he)
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply (eq_bot_or_top_of_invariant k F R hx l.ker (fun c x hx ↦ ?_) h₁).resolve_right
    · exact fun h ↦ hn (LinearMap.ker_eq_top.mp h)
    · exact (hg c x).trans ((congrArg (scalarActionMap k F R Y (σ c)) hx).trans (map_zero _))
  · apply LinearMap.range_eq_top.mp
    apply (eq_bot_or_top_of_invariant k F R hy l.range ?_ h₂).resolve_left
    · exact fun h ↦ hn (LinearMap.range_eq_bot.mp h)
    · rintro c _ ⟨x,rfl⟩
      exact ⟨_,(hg (σ.symm c) x).trans (by rw [σ.apply_symm_apply])⟩

end EFiniteCharacterizations.FieldExtension
