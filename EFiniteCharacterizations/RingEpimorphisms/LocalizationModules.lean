module

public import EFiniteCharacterizations.RingEpimorphisms.UniversalLocalization
public import EFiniteCharacterizations.RingEpimorphisms.RingEpimorphism

/-! # Modules over universal localizations -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace EFiniteCharacterizations

variable {R B : Type u} [Ring R] [Ring B] {I : Type v} {φ : I → TwoTerm R} {f : R →+* B}

theorem IsUniversalLocalization.epic (h : IsUniversalLocalization φ f) : IsRingEpimorphism f := by
  intro T _ g g' he
  apply (h.desc T (g.comp f) ?_).unique rfl he.symm
  apply (invertsFamily_comp_iff φ f g).2
  intro i
  apply ((φ i).induce f |>.isIso_induce_iff_regular g).2
  let := Module.compHom T g
  exact ((φ i).induce f |>.isIso_iff_invertedOn_all).1 (h.inverts i) (ModuleCat.of B T)

/-- Solving the inversion equations pointwise gives a solution with values
in the additive endomorphisms. Uniqueness makes each solution additive. -/
theorem TwoTerm.invertedOn_end_action (P : TwoTerm R) (M : ModuleCat.{u} R) (h : P.InvertedOn M) :
    let ρ : R →+* Module.End ℤ M := Module.toModuleEnd ℤ _
    letI := Module.compHom (Module.End ℤ M) ρ
    P.InvertedOn (ModuleCat.of R (Module.End ℤ M)) := by
  let ρ : R →+* Module.End ℤ M := Module.toModuleEnd ℤ _
  let := Module.compHom (Module.End ℤ M) ρ
  have hb := (P.invertedOn_iff_linear M).1 h
  let T := Module.End ℤ M
  let ev (x : M) : T →ₗ[R] M :=
    { toFun := fun b ↦ b x, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  apply (P.invertedOn_iff_linear _).2
  constructor
  · intro a b he
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro x
    have hxy : (ev x).comp a = (ev x).comp b := hb.1
      (congrArg ((ev x).comp ·) he)
    exact LinearMap.congr_fun hxy y
  · intro a
    choose b hb' using fun x : M ↦ hb.2 ((ev x).comp a)
    change ∀ x, (b x).comp P.differential.hom.hom = (ev x).comp a at hb'
    have ha (x y : M) : b (x+y) = b x + b y := by
      apply hb.1
      change (b (x+y)).comp _ = (b x + b y).comp _
      rw [LinearMap.add_comp,hb',hb',hb']
      exact LinearMap.ext fun z ↦ (a z).map_add x y
    let F (y : P.target) : T := AddMonoidHom.toIntLinearMap
      { toFun := fun x ↦ b x y
        map_zero' := by simpa using congrArg (fun t ↦ t y) (ha 0 0)
        map_add' := fun x z ↦ LinearMap.congr_fun (ha x z) y }
    let g : P.target →ₗ[R] T :=
      { toFun := F
        map_add' := fun y z ↦ LinearMap.ext fun x ↦ (b x).map_add y z
        map_smul' := fun r y ↦ LinearMap.ext fun x ↦ (b x).map_smul r y }
    exact ⟨g,LinearMap.ext fun y ↦ LinearMap.ext fun x ↦ LinearMap.congr_fun (hb' x) y⟩

/-- Every module inverting the family admits a compatible action by the
localization ring. -/
theorem IsUniversalLocalization.exists_module (h : IsUniversalLocalization φ f)
    (M : ModuleCat.{u} R) (hi : ∀ i, (φ i).InvertedOn M) :
    ∃ m : Module B M, ∀ (r : R) (x : M), letI := m; f r • x = r • x := by
  let ρ : R →+* Module.End ℤ M := Module.toModuleEnd ℤ _
  obtain ⟨q,hq,_⟩ := h.desc _ ρ fun i ↦ ((φ i).isIso_induce_iff_regular ρ).2
    ((φ i).invertedOn_end_action M (hi i))
  exact ⟨Module.compHom M q,fun r x ↦ LinearMap.congr_fun (DFunLike.congr_fun hq r) x⟩

open scoped ModuleCat.Algebra

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R] [Algebra k B]

/-- An inverting finite module over the source of a finite-dimensional
localization is the restriction of a finite module over the target. -/
theorem IsUniversalLocalization.exists_finite_lift [Module.Finite k B] (g : R →ₐ[k] B)
    (h : IsUniversalLocalization φ g.toRingHom) (X : FGModuleCat.{u} R)
    (hi : ∀ i, (φ i).InvertedOn X.obj) :
    ∃ Y : FGModuleCat.{u} B, Nonempty ((finiteRestriction k g).obj Y ≅ X) := by
  obtain ⟨m,hm⟩ := h.exists_module X.obj hi
  let := m
  have : IsScalarTower k B X := ⟨fun a b x ↦ by
    rw [Algebra.smul_def,mul_smul,← g.commutes]
    exact (hm _ (b • x)).trans (IsScalarTower.algebraMap_smul R a (b • x))⟩
  have : Module.Finite k (X.obj : Type u) := Module.Finite.trans R _
  let := Module.Finite.of_restrictScalars_finite k B X
  let Y := FGModuleCat.of B X
  let e : ((finiteRestriction k g).obj Y) ≃ₗ[R] X :=
    { toEquiv := Equiv.refl _, map_add' := fun _ _ ↦ rfl, map_smul' := hm }
  exact ⟨Y,⟨(forget₂ (FGModuleCat R) (ModuleCat R)).preimageIso e.toModuleIso⟩⟩

/-- Stable modules of the Euler weight of a differential, restricted to
the locus where that differential is inverted. -/
def TwoTerm.stableInvertingClasses [IsNoetherianRing R] (P : TwoTerm R) :
    Set (Skeleton (FGModuleCat.{u} R)) :=
  {c | ∃ X : FGModuleCat.{u} R, toSkeleton X = c ∧ (P.eulerWeight k).IsStable X ∧ P.InvertedOn X.obj}

theorem TwoTerm.eulerWeight_zero_of_inverted [IsNoetherianRing R] (P : TwoTerm R)
    (X : FGModuleCat.{u} R) (h : P.InvertedOn X.obj) : (P.eulerWeight k).eval X = 0 := by
  let e (A : FGModuleCat.{u} R) : (A ⟶ X) ≃ (A.obj ⟶ X.obj) := InducedCategory.homEquiv
  let l := Linear.leftComp k X P.differential
  have hb : Function.Bijective l := (e _).symm.bijective.comp (h.comp (e _).bijective)
  rw [P.eulerWeight_eval k,homFinrank_eq_finrank,homFinrank_eq_finrank,sub_eq_zero]
  exact_mod_cast (LinearEquiv.ofBijective l hb).finrank_eq

/-- Stability makes the lifted action simple, even for an
infinite-dimensional localization. -/
theorem IsUniversalLocalization.exists_simple_action [IsNoetherianRing R]
    (P : TwoTerm R) (g : R →ₐ[k] B)
    (h : IsUniversalLocalization (fun _ : Unit ↦ P) g.toRingHom)
    (X : FGModuleCat.{u} R) (hs : (P.eulerWeight k).IsStable X)
    (hi : P.InvertedOn X.obj) :
    ∃ m : Module B X, letI := m
      IsSimpleModule B X ∧ IsScalarTower k B X ∧
        ∀ (r : R) (x : X), g r • x = r • x := by
  obtain ⟨m,hm⟩ := h.exists_module X.obj (fun _ ↦ hi)
  let := m
  refine ⟨m,?_,?_,hm⟩
  · have : Nontrivial X := not_subsingleton_iff_nontrivial.mp
      (hs.1 ∘ (FGModuleCat.isZero_iff_subsingleton X).2)
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun U ↦ ?_ }
    by_cases hu : U = ⊥
    · exact Or.inl hu
    right
    let := Module.compHom U g.toRingHom
    let j : U →ₗ[R] X :=
      { U.subtype.toAddHom with map_smul' := fun r x ↦ hm r x.val }
    have hj : Function.Injective j := Subtype.val_injective
    have := X.property
    have : Module.Finite R U := Module.Finite.of_injective j hj
    let Y := FGModuleCat.of R U
    let i : Y ⟶ X := FGModuleCat.ofHom j
    have : Mono i := (FGModuleCat.mono_iff_injective _).2 hj
    have hY : ¬ Limits.IsZero Y := by
      intro hz
      have : Subsingleton U := (FGModuleCat.isZero_iff_subsingleton Y).1 hz
      exact hu (Submodule.eq_bot_of_subsingleton (p := U))
    have hinv : P.InvertedOn Y.obj :=
      (P.invertedOn_induce_iff g.toRingHom (ModuleCat.of B U)).1
        (((P.induce g.toRingHom).isIso_iff_invertedOn_all).1 (h.inverts ()) _)
    have hiso : IsIso i := by
      by_contra hn
      exact (hs.2.2 i hY hn).ne (P.eulerWeight_zero_of_inverted k Y hinv)
    apply top_unique
    intro x _
    obtain ⟨y,hy⟩ := ((FGModuleCat.isIso_iff_bijective i).1 hiso).2 x
    exact hy ▸ y.property
  · refine ⟨fun a b x ↦ ?_⟩
    rw [Algebra.smul_def,mul_smul,← g.commutes]
    exact (hm _ (b • x)).trans (IsScalarTower.algebraMap_smul R a (b • x))

/-- Over a finite-dimensional localization every stable inverting module is
the restriction of a simple module. In particular there are only finitely
many stable isomorphism classes on a single inversion chart. -/
theorem TwoTerm.finite_stableInvertingClasses_of_finite_localization
    [IsNoetherianRing R] [Module.Finite k B] (P : TwoTerm R) (g : R →ₐ[k] B)
    (h : IsUniversalLocalization (fun _ : Unit ↦ P) g.toRingHom) :
    (P.stableInvertingClasses k).Finite := by
  let := IsNoetherianRing.of_finite k B
  let := IsArtinianRing.of_finite k B
  let F := finiteRestriction k g
  have hinv (Y : FGModuleCat.{u} B) : P.InvertedOn (F.obj Y).obj :=
    (P.invertedOn_induce_iff g.toRingHom Y.obj).1
      (((P.induce g.toRingHom).isIso_iff_invertedOn_all).1 (h.inverts ()) Y.obj)
  apply ((finite_simpleIsomorphismClasses (R := B) k).image F.mapSkeleton.obj).subset
  rintro _ ⟨X,rfl,hX,hp⟩
  obtain ⟨Y,⟨e⟩⟩ := h.exists_finite_lift k g X fun _ ↦ hp
  have hy := hX.of_iso e.symm
  have hsimple : Simple Y := by
    constructor
    intro U i hi
    have hi' : Mono (F.map i) := (FGModuleCat.mono_iff_injective _).2 ((FGModuleCat.mono_iff_injective i).1 hi)
    constructor
    · intro hIso hz
      apply hy.1
      have hid : 𝟙 Y = 0 := (IsIso.inv_hom_id i).symm.trans ((congrArg (inv i ≫ ·) hz).trans comp_zero)
      exact (Limits.IsZero.iff_id_eq_zero _).2 (by simpa using congrArg F.map hid)
    · intro hn
      have hn' : ¬ Limits.IsZero (F.obj U) := fun hz ↦ hn (F.map_injective ((hz.eq_of_src _ _).trans (F.map_zero U Y).symm))
      have hiso : IsIso (F.map i) := by
        by_contra hni
        exact (hy.2.2 _ hn' hni).ne (P.eulerWeight_zero_of_inverted k _ (hinv U))
      exact (FGModuleCat.isIso_iff_bijective i).2 ((FGModuleCat.isIso_iff_bijective (F.map i)).1 hiso)
  refine ⟨toSkeleton Y,⟨Y,rfl,hsimple⟩,?_⟩
  simpa only [Functor.mapSkeleton_obj_toSkeleton] using congr_toSkeleton_of_iso e

end EFiniteCharacterizations
