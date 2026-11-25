module

public import EFiniteCharacterizations.Presentations.StableInversion
public import EFiniteCharacterizations.Silting.Fans.CoveredWeights
public import Mathlib.LinearAlgebra.Pi

/-! # Finite submodules in the perpendicular of a presilting differential -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]

theorem invertedOn_iff_linear (P : TwoTerm R) (N : ModuleCat.{u} R) :
    P.InvertedOn N ↔ Function.Bijective (fun f : P.target →ₗ[R] N ↦ f.comp P.differential.hom.hom) := by
  let s : (P.source.obj ⟶ N) ≃ (P.source →ₗ[R] N) := ModuleCat.homAddEquiv.toEquiv
  let t : (P.target.obj ⟶ N) ≃ (P.target →ₗ[R] N) := ModuleCat.homAddEquiv.toEquiv
  change _ ↔ Function.Bijective (s ∘ (fun g ↦ P.differential.hom ≫ g) ∘ t.symm)
  rw [Equiv.comp_bijective, Equiv.bijective_comp]
  rfl

include k in
/-- Every finitely generated submodule of a module inverting a presilting
differential is contained in a finitely generated submodule that inverts it. -/
theorem exists_fg_invertedOn_ge (P : TwoTerm R) (hp : P.IsPresilting)
    (N : ModuleCat.{u} R) (hn : P.InvertedOn N) (U : Submodule R N) (hu : U.FG) :
    ∃ V : Submodule R N, U ≤ V ∧ V.FG ∧ P.InvertedOn (ModuleCat.of R V) := by
  classical
  have : Module.Finite R U := Module.Finite.of_fg hu
  let A := FGModuleCat.of R U
  let d := P.differential.hom.hom
  have := finiteModuleHom_isFinite k P.source A
  let b := (Module.finBasis k (P.source ⟶ A)).map (finiteModuleHomLinearEquiv k P.source A)
  let n := Module.finrank k (P.source ⟶ A)
  have h := (invertedOn_iff_linear P N).mp hn
  choose l hl using fun i : Fin n ↦ h.2 (U.subtype.comp (b i))
  let D := U × (Fin n → P.target)
  let q : D →ₗ[R] N := U.subtype.coprod (LinearMap.lsum R (fun _ : Fin n ↦ P.target) ℕ l)
  let V := LinearMap.range q
  have hU : U ≤ V := fun x hx ↦ ⟨(⟨x,hx⟩,0), by change x + (LinearMap.lsum R _ ℕ l) 0 = x; rw [map_zero,add_zero]⟩
  have hlV (i : Fin n) (x : P.target) : l i x ∈ V :=
    ⟨(0,Pi.single i x), by change (0 : N) + (LinearMap.lsum R _ ℕ l) (Pi.single i x) = _; rw [zero_add, LinearMap.lsum_piSingle]⟩
  let c := U.inclusion hU
  let L := fun i ↦ (l i).codRestrict V (hlV i)
  have hc (i : Fin n) : (L i).comp d = c.comp (b i) := by
    apply LinearMap.ext
    intro x
    exact Subtype.ext (LinearMap.congr_fun (hl i) x)
  have liftFromU (w : P.source →ₗ[R] U) :
      ∃ z : P.target →ₗ[R] V, z.comp d = c.comp w := by
    refine ⟨∑ i, b.repr w i • L i, ?_⟩
    apply LinearMap.ext
    intro x
    have he := LinearMap.congr_fun (b.sum_repr w) x
    change (∑ i, b.repr w i • L i) (d x) = c (w x)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply] at he ⊢
    rw [← he, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Subtype.ext
    rw [show (L i) (d x) = c (b i x) from LinearMap.congr_fun (hc i) x]
    rfl
  have : Module.Finite R P.target := P.target.property
  refine ⟨V,hU,Submodule.fg_range q,(invertedOn_iff_linear _ _).mpr ⟨?_,?_⟩⟩
  · intro f g he
    have he' : V.subtype.comp f = V.subtype.comp g :=
      h.1 (congrArg (V.subtype.comp ·) he)
    exact LinearMap.ext fun x ↦ Subtype.ext (LinearMap.congr_fun he' x)
  · intro f
    have : Module.Projective R P.source := P.projective_source
    obtain ⟨v,hv⟩ := Module.projective_lifting_property q.rangeRestrict f q.surjective_rangeRestrict
    let w := (LinearMap.fst R U (Fin n → P.target)).comp v
    let t := fun i : Fin n ↦ (LinearMap.proj i).comp ((LinearMap.snd R U (Fin n → P.target)).comp v)
    have pair (i : Fin n) : ∃ (a : Module.End R P.source) (z : Module.End R P.target),
        t i = d.comp a - z.comp d := by
      obtain ⟨⟨a,z⟩,haz⟩ := hp (FGModuleCat.ofHom (t i))
      exact ⟨a.hom.hom,z.hom.hom,(congrArg (fun g ↦ g.hom.hom) haz).symm⟩
    choose a z hz using pair
    obtain ⟨y,hy⟩ := liftFromU (w + ∑ i, (b i).comp (a i))
    refine ⟨y - ∑ i, (L i).comp (z i), ?_⟩
    apply LinearMap.ext
    intro x
    have hyx := LinearMap.congr_fun hy x
    have hvx := LinearMap.congr_fun hv x
    change (y (d x) - _) = _
    change y (d x) = c ((w + ∑ i, (b i).comp (a i)) x) at hyx
    change q.rangeRestrict (v x) = f x at hvx
    rw [hyx, ← hvx]
    apply Subtype.ext
    change _ = q (v x)
    simp only [q, LinearMap.lsum_apply, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.add_apply, map_add, map_sum]
    have ht (i : Fin n) : l i ((v x).2 i) =
        (b i (a i x) : U) - (l i) (z i (d x)) := by
      change l i (t i x) = _
      rw [hz, LinearMap.sub_apply, map_sub]
      exact congrArg₂ (· - ·) (LinearMap.congr_fun (hl i) (a i x)) rfl
    change ↑(c (w x) + ∑ i, c (b i (a i x)) - ∑ i, L i (z i (d x))) =
      ((w x : U) : N) + (∑ i, (l i).comp (LinearMap.proj i)) ((v x).2)
    simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_sum, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
    simp_rw [ht, Finset.sum_sub_distrib]
    abel

private theorem invertedOn_of_cofinal (P : TwoTerm R) (N : ModuleCat.{u} R)
    (h : ∀ U : Submodule R N, U.FG → ∃ V : Submodule R N, U ≤ V ∧
      P.InvertedOn (ModuleCat.of R V)) : P.InvertedOn N := by
  have : Module.Finite R P.source := P.source.property
  have : Module.Finite R P.target := P.target.property
  apply (invertedOn_iff_linear _ _).2
  constructor
  · intro f g he
    obtain ⟨V,hV,hi⟩ := h (f.range ⊔ g.range) ((Submodule.fg_range f).sup (Submodule.fg_range g))
    let f' := f.codRestrict V (fun x ↦ hV (le_sup_left (a := f.range) (b := g.range) ⟨x,rfl⟩))
    let g' := g.codRestrict V (fun x ↦ hV (le_sup_right (a := f.range) (b := g.range) ⟨x,rfl⟩))
    have he' : f' = g' := ((invertedOn_iff_linear _ _).mp hi).1
      (LinearMap.ext fun x ↦ Subtype.ext (LinearMap.congr_fun he x))
    exact LinearMap.ext fun x ↦ congrArg Subtype.val (LinearMap.congr_fun he' x)
  · intro f
    obtain ⟨V,hV,hi⟩ := h f.range (Submodule.fg_range f)
    let f' := f.codRestrict V (fun x ↦ hV ⟨x,rfl⟩)
    obtain ⟨g,hg⟩ := ((invertedOn_iff_linear _ _).mp hi).2 f'
    exact ⟨V.subtype.comp g, LinearMap.ext fun x ↦ congrArg Subtype.val (LinearMap.congr_fun hg x)⟩

variable [IsNoetherianRing R]

/-- Inversion on a finite module is detected by the two Hom perpendiculars
of the differential, for arbitrary projective terms and differential. -/
theorem invertedOn_iff_perpendicular (P : TwoTerm R) (M : FGModuleCat.{u} R) :
    P.InvertedOn M.obj ↔
      Subsingleton (cokernel P.differential ⟶ M) ∧ Subsingleton (M ⟶ P.nakayamaKernel k) := by
  have h : P.InvertedOn M.obj ↔ Function.Bijective (P.precompose M) := by
    let s : (P.source ⟶ M) ≃ (P.source.obj ⟶ M.obj) := InducedCategory.homEquiv
    let t : (P.target ⟶ M) ≃ (P.target.obj ⟶ M.obj) := InducedCategory.homEquiv
    change Function.Bijective (s ∘ (P.precompose M) ∘ t.symm) ↔ _
    rw [Equiv.comp_bijective, Equiv.bijective_comp]
  rw [h]
  apply and_congr _ (surjective_precompose_iff_no_hom_nakayamaKernel k P M)
  rw [← AddMonoidHom.ker_eq_bot_iff, (P.cokernelHomEquiv M).toEquiv.subsingleton_congr]
  constructor
  · intro h
    rw [h]
    infer_instance
  · intro h
    exact eq_bot_iff.mpr fun x hx ↦ congrArg Subtype.val
      (h.elim (⟨x,hx⟩ : (P.precompose M).ker) 0)

/-- On finite modules, inversion coincides with semistability for the Euler weight. -/
theorem invertedOn_iff_semistable (P : TwoTerm R) (hp : P.IsPresilting) (M : FGModuleCat.{u} R) :
    P.InvertedOn M.obj ↔ (P.eulerWeight k).IsSemistable M := by
  exact (invertedOn_iff_perpendicular k P M).trans (isSemistable_eulerWeight_iff_perpendicular k P hp M).symm

/-- An arbitrary module inverts a presilting differential precisely when it
is a directed union of finite semistable submodules. -/
theorem invertedOn_iff_directed_union_semistable (P : TwoTerm R) (hp : P.IsPresilting)
    (N : ModuleCat.{u} R) :
    P.InvertedOn N ↔ ∃ S : Set (Submodule R N), S.Nonempty ∧ DirectedOn (· ≤ ·) S ∧
      sSup S = ⊤ ∧ ∀ V ∈ S, ∃ _ : Module.Finite R V, (P.eulerWeight k).IsSemistable (FGModuleCat.of R V) := by
  constructor
  · intro hn
    let S : Set (Submodule R N) := {V | V.FG ∧ P.InvertedOn (ModuleCat.of R V)}
    have cover (U : Submodule R N) (hu : U.FG) : ∃ V ∈ S, U ≤ V := by
      obtain ⟨V,hUV,hfg,hi⟩ := exists_fg_invertedOn_ge k P hp N hn U hu
      exact ⟨V,⟨hfg,hi⟩,hUV⟩
    obtain ⟨V,hV,_⟩ := cover ⊥ Submodule.fg_bot
    refine ⟨S,⟨V,hV⟩,?_,?_,?_⟩
    · intro U hU V hV
      obtain ⟨W,hW,hle⟩ := cover (U ⊔ V) (hU.1.sup hV.1)
      exact ⟨W,hW,le_sup_left.trans hle,le_sup_right.trans hle⟩
    · apply top_unique
      intro x _
      obtain ⟨W,hW,hx⟩ := cover (R ∙ x) (Submodule.fg_span_singleton x)
      exact le_sSup hW (hx (Submodule.subset_span rfl))
    · intro W hW
      let := Module.Finite.of_fg hW.1
      exact ⟨inferInstance,(invertedOn_iff_semistable k P hp (FGModuleCat.of R W)).mp hW.2⟩
  · rintro ⟨S,hs,hd,ht,h⟩
    apply invertedOn_of_cofinal
    intro U hu
    obtain ⟨V,hV,hle⟩ := (isCompactElement_iff_le_of_directed_sSup_le U).mp
      ((Submodule.fg_iff_compact U).mp hu) S hs hd (ht ▸ le_top)
    obtain ⟨_,hsem⟩ := h V hV
    exact ⟨V,hle,(invertedOn_iff_semistable k P hp (FGModuleCat.of R V)).mpr hsem⟩

end EFiniteCharacterizations.TwoTerm
