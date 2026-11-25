module

public import EFiniteCharacterizations.LargeModules.LargePerpendicular
public import EFiniteCharacterizations.Stability.SemistableApproximations
public import EFiniteCharacterizations.Modules.CompositionLength

/-! # Finite reflections into a presilting perpendicular -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsArtinianRing R] [IsNoetherianRing R]

/-- A left approximation by semistable modules of least length has unique
factorizations, since the kernel of a difference yields another approximation. -/
theorem exists_semistable_reflection (θ : Weight (FGModuleCat.{u} R))
    (hθ : CovariantlyFinite θ.IsSemistable) (X : FGModuleCat.{u} R) :
    ∃ (L : FGModuleCat.{u} R) (i : X ⟶ L), θ.IsSemistable L ∧ ∀ Y, θ.IsSemistable Y →
      Function.Bijective (fun g : L ⟶ Y ↦ i ≫ g) := by
  classical
  let A (n : ℕ) := ∃ (L : FGModuleCat.{u} R) (i : X ⟶ L),
    FGModuleCat.moduleLength L = n ∧ θ.IsSemistable L ∧
      ∀ Y, θ.IsSemistable Y → Function.Surjective (fun g : L ⟶ Y ↦ i ≫ g)
  have hA : ∃ n, A n := by
    obtain ⟨L,i,hL,hi⟩ := hθ X
    exact ⟨_,L,i,rfl,hL,hi⟩
  obtain ⟨L,i,hlen,hL,hi⟩ := Nat.find_spec hA
  refine ⟨L,i,hL,fun Y hY ↦ ⟨?_,hi Y hY⟩⟩
  intro g g' he
  change i ≫ g = i ≫ g' at he
  by_contra hn
  let d := g - g'
  let p := Abelian.factorThruImage d
  have hzero : i ≫ d = 0 := by rw [Preadditive.comp_sub, he, sub_self]
  have hip : i ≫ p = 0 := by
    apply (cancel_mono (Abelian.image.ι d)).1
    simpa [p] using hzero
  let j := kernel.ι p
  let b := kernel.lift p i hip
  have hb : b ≫ j = i := kernel.lift_ι _ _ _
  have hk := hL.kernel_of_epi (hL.image hY d) p
  have hsmall : A (FGModuleCat.moduleLength (kernel p)) := by
    refine ⟨_,b,rfl,hk,?_⟩
    intro Z hZ f
    obtain ⟨q,hq⟩ := hi Z hZ f
    exact ⟨j ≫ q, by change b ≫ j ≫ q = f; rw [← Category.assoc,hb]; exact hq⟩
  have hj : ¬ IsIso j := by
    intro hj
    have hp : p = 0 := zero_of_epi_comp j (kernel.condition p)
    apply hn
    apply sub_eq_zero.mp
    change d = 0
    rw [← Abelian.image.fac d]
    exact (congrArg (· ≫ Abelian.image.ι d) hp).trans zero_comp
  exact (Nat.not_lt_of_ge (Nat.find_min' hA hsmall))
    ((FGModuleCat.moduleLength_lt_of_mono j hj).trans_eq hlen)

namespace TwoTerm

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
/-- Every finite module has a finite reflection that remains universal for
maps to arbitrary modules inverting the differential. -/
theorem exists_perpendicular_reflection_of_presilting
    (P : TwoTerm R) (hp : P.IsPresilting) (X : FGModuleCat.{u} R) :
    ∃ (L : FGModuleCat.{u} R) (i : X ⟶ L), P.InvertedOn L.obj ∧
      ∀ N : ModuleCat.{u} R, P.InvertedOn N →
        Function.Bijective (fun g : L.obj ⟶ N ↦ i.hom ≫ g) := by
  have hθ := (P.functoriallyFinite_semistable k hp).1
  obtain ⟨L,i,hL,hi⟩ := exists_semistable_reflection _ hθ X
  refine ⟨L,i,(invertedOn_iff_semistable k P hp L).2 hL,?_⟩
  intro N hn
  have : Module.Finite R L := L.property
  have : Module.Finite R X := X.property
  have cover (U : Submodule R N) (hu : U.FG) := exists_fg_invertedOn_ge k P hp N hn U hu
  constructor
  · intro f g he
    obtain ⟨V,hV,hfg,hv⟩ := cover (f.hom.range ⊔ g.hom.range)
      ((Submodule.fg_range f.hom).sup (Submodule.fg_range g.hom))
    let := Module.Finite.of_fg hfg
    let Y := FGModuleCat.of R V
    let f' : L ⟶ Y := FGModuleCat.ofHom (f.hom.codRestrict V (fun x ↦ hV (le_sup_left (a := f.hom.range) (b := g.hom.range) ⟨x,rfl⟩)))
    let g' : L ⟶ Y := FGModuleCat.ofHom (g.hom.codRestrict V (fun x ↦ hV (le_sup_right (a := f.hom.range) (b := g.hom.range) ⟨x,rfl⟩)))
    have he' : f' = g' := (hi Y ((invertedOn_iff_semistable k P hp Y).1 hv)).1
      (FGModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext (congrArg (fun a : X.obj ⟶ N ↦ a.hom x) he)))
    exact ModuleCat.hom_ext (LinearMap.ext fun x ↦ congrArg (fun a : L ⟶ Y ↦ ((a.hom.hom x : V) : N)) he')
  · intro f
    obtain ⟨V,hV,hfg,hv⟩ := cover f.hom.range (Submodule.fg_range f.hom)
    let := Module.Finite.of_fg hfg
    let Y := FGModuleCat.of R V
    let f' : X ⟶ Y := FGModuleCat.ofHom (f.hom.codRestrict V (fun x ↦ hV ⟨x,rfl⟩))
    obtain ⟨g,hg⟩ := (hi Y ((invertedOn_iff_semistable k P hp Y).1 hv)).2 f'
    exact ⟨g.hom ≫ ModuleCat.ofHom V.subtype, ModuleCat.hom_ext (LinearMap.ext fun x ↦
      congrArg (fun a : X ⟶ Y ↦ ((a.hom.hom x : V) : N)) hg)⟩

include k in
theorem exists_finite_perpendicular_reflection (_hR : IsEFinite R)
    (P : TwoTerm R) (hp : P.IsPresilting) (X : FGModuleCat.{u} R) :
    ∃ (L : FGModuleCat.{u} R) (i : X ⟶ L), P.InvertedOn L.obj ∧
      ∀ N : ModuleCat.{u} R, P.InvertedOn N →
        Function.Bijective (fun g : L.obj ⟶ N ↦ i.hom ≫ g) :=
  exists_perpendicular_reflection_of_presilting k P hp X

include k in
/-- The reflected regular module represents elements of arbitrary modules in
the perpendicular by evaluation at the image of one. -/
theorem exists_pointed_perpendicular_of_presilting (P : TwoTerm R) (hp : P.IsPresilting) :
    ∃ (L : FGModuleCat.{u} R) (e : L), P.InvertedOn L.obj ∧
      ∀ N : ModuleCat.{u} R, P.InvertedOn N → Function.Bijective (fun f : L →ₗ[R] N ↦ f e) := by
  obtain ⟨L,i,hL,hi⟩ := exists_perpendicular_reflection_of_presilting k P hp (FGModuleCat.of R R)
  refine ⟨L,i.hom.hom 1,hL,fun N hn ↦ ⟨?_,?_⟩⟩
  · intro f g he
    suffices h : ModuleCat.ofHom f = ModuleCat.ofHom g from congrArg ModuleCat.Hom.hom h
    apply (hi N hn).1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change f (i.hom.hom r) = g (i.hom.hom r)
    have hr : i.hom.hom r = r • i.hom.hom 1 := by
      rw [← map_smul]; exact congrArg i.hom.hom (mul_one r).symm
    rw [hr,map_smul,map_smul]
    exact congrArg (r • ·) he
  · intro y
    obtain ⟨f,hf⟩ := (hi N hn).2 (ModuleCat.ofHom (LinearMap.toSpanSingleton R N y))
    exact ⟨f.hom, (congrArg (fun g ↦ ModuleCat.Hom.hom g (1 : R)) hf).trans
      (LinearMap.toSpanSingleton_apply_one R N y)⟩

include k in
theorem exists_finite_pointed_perpendicular (_hR : IsEFinite R) (P : TwoTerm R) (hp : P.IsPresilting) :
    ∃ (L : FGModuleCat.{u} R) (e : L), P.InvertedOn L.obj ∧
      ∀ N : ModuleCat.{u} R, P.InvertedOn N → Function.Bijective (fun f : L →ₗ[R] N ↦ f e) :=
  exists_pointed_perpendicular_of_presilting k P hp

end TwoTerm

end EFiniteCharacterizations
