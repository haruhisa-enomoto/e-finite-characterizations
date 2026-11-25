module

public import EFiniteCharacterizations.Subcategories.GeneratedModules

/-! # Semistability and shrunk subspaces of a projective matrix space -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

/-- For any subspace of maps out of the target projective, take the sum of
their images. Every map from the source projective to this sum lifts through
a finite sum of target projectives. -/
theorem exists_trace_of_hom_subspace (P : TwoTerm R) (M : FGModuleCat.{u} R)
    (U : Submodule k (P.target ⟶ M)) (V : Submodule k (P.source ⟶ M))
    (hUV : ∀ (p : P.source ⟶ P.target) (f : U), p ≫ f.val ∈ V) :
    ∃ (T : FGModuleCat.{u} R) (i : T ⟶ M), Mono i ∧
      U ≤ LinearMap.range (Linear.rightComp k P.target i) ∧
      LinearMap.range (Linear.rightComp k P.source i) ≤ V := by
  classical
  have := finiteModuleHom_isFinite k P.target M
  let b := Module.finBasis k U
  let A := fun _ : Fin (Module.finrank k U) ↦ P.target
  let a : (⨁ A) ⟶ M := biproduct.desc (fun j ↦ (b j).val)
  let i := Abelian.image.ι a
  let q := Abelian.factorThruImage a
  have hqi : q ≫ i = a := Abelian.image.fac a
  have hb (j) : biproduct.ι A j ≫ a = (b j).val := biproduct.ι_desc _ _
  refine ⟨_,i,inferInstance,?_,?_⟩
  · intro f hf
    let x : U := ⟨f,hf⟩
    have hx := congrArg U.subtype (b.sum_repr x)
    change f ∈ _
    rw [show f = ∑ j, b.repr x j • (b j).val by rw [map_sum] at hx; simp only [map_smul] at hx; exact hx.symm]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact ⟨biproduct.ι A j ≫ q,by change (_ ≫ q) ≫ i = _; rw [Category.assoc,hqi,hb]⟩
  · rintro _ ⟨g,rfl⟩
    have := P.projective_source
    obtain ⟨l,hl⟩ := FGModuleCat.exists_lift_of_projective q g
    change g ≫ i ∈ V
    rw [← hl,Category.assoc,hqi]
    have he : l ≫ a = ∑ j, (l ≫ biproduct.π A j) ≫ (b j).val := by
      conv_lhs => rw [← Category.id_comp a,← biproduct.total (f := A)]
      simp only [Preadditive.sum_comp,Preadditive.comp_sum,Category.assoc,hb]
    rw [he]
    exact V.sum_mem (fun j _ ↦ hUV _ (b j))

/-- The Hom spaces of a semistable module are balanced, and the full space
of projective differentials has no shrunk subspace. These two numerical
conditions also imply semistability. -/
theorem isSemistable_iff_no_shrunk_subspace (P : TwoTerm R) (M : FGModuleCat.{u} R) :
    (P.eulerWeight k).IsSemistable M ↔
      homFinrank k P.target M = homFinrank k P.source M ∧
      ∀ (U : Submodule k (P.target ⟶ M)) (V : Submodule k (P.source ⟶ M)),
        (∀ (p : P.source ⟶ P.target) (f : U), p ≫ f.val ∈ V) →
        Module.finrank k U ≤ Module.finrank k V := by
  have := finiteModuleHom_isFinite k P.target M
  have := finiteModuleHom_isFinite k P.source M
  have hr {T : FGModuleCat.{u} R} (i : T ⟶ M) [Mono i] (X : FGModuleCat.{u} R) :
      Module.finrank k (LinearMap.range (Linear.rightComp k X i)) = homFinrank k X T := by
    rw [homFinrank_eq_finrank]
    exact LinearMap.finrank_range_of_inj (fun _ _ h ↦ (cancel_mono i).mp h)
  constructor
  · intro hs
    refine ⟨?_,fun U V h ↦ ?_⟩
    · have hz := hs.1
      rw [P.eulerWeight_eval k] at hz
      omega
    · obtain ⟨T,i,hi,hU,hV⟩ := P.exists_trace_of_hom_subspace k M U V h
      have ht := hs.2 i
      rw [P.eulerWeight_eval k] at ht
      have ha := Submodule.finrank_mono hU
      have hb := Submodule.finrank_mono hV
      rw [hr] at ha hb
      omega
  · rintro ⟨he,h⟩
    refine ⟨by rw [P.eulerWeight_eval k,he,sub_self], fun {T} i hi ↦ ?_⟩
    have H := h (LinearMap.range (Linear.rightComp k P.target i))
      (LinearMap.range (Linear.rightComp k P.source i)) (fun p ⟨_,g,hg⟩ ↦
        ⟨p ≫ g,by change (p ≫ g) ≫ i = _; rw [Category.assoc]; exact congrArg (p ≫ ·) hg⟩)
    rw [hr,hr] at H
    rw [P.eulerWeight_eval k]
    omega

/-- For a stable module, the image of each proper nonzero Hom subspace
under all differentials spans a strictly larger space. -/
theorem strict_expansion_of_stable {P : TwoTerm R} {M : FGModuleCat.{u} R}
    (hs : (P.eulerWeight k).IsStable M)
    (U : Submodule k (P.target ⟶ M)) (V : Submodule k (P.source ⟶ M))
    (hne : U ≠ ⊥) (hproper : U ≠ ⊤)
    (hUV : ∀ (p : P.source ⟶ P.target) (f : U), p ≫ f.val ∈ V) :
    Module.finrank k U < Module.finrank k V := by
  have := finiteModuleHom_isFinite k P.target M
  have := finiteModuleHom_isFinite k P.source M
  obtain ⟨T,i,hi,hU,hV⟩ := P.exists_trace_of_hom_subspace k M U V hUV
  have hT : ¬ IsZero T := by
    intro hz
    apply hne
    apply eq_bot_iff.mpr
    intro f hf
    obtain ⟨g,hg⟩ := hU hf
    have hg' : g = 0 := hz.eq_of_tgt _ _
    rw [← hg,hg',map_zero]
    exact Submodule.zero_mem _
  have hr (X : FGModuleCat.{u} R) :
      Module.finrank k (LinearMap.range (Linear.rightComp k X i)) = homFinrank k X T := by
    rw [homFinrank_eq_finrank]
    exact LinearMap.finrank_range_of_inj (fun _ _ h ↦ (cancel_mono i).mp h)
  by_cases hiso : IsIso i
  · have hfull : LinearMap.range (Linear.rightComp k P.source i) = ⊤ :=
      LinearMap.range_eq_top.mpr fun f ↦ ⟨f ≫ inv i,by change (f ≫ inv i) ≫ i = f; simp⟩
    have hEq := ((P.isSemistable_iff_no_shrunk_subspace k M).1 hs.isSemistable).1
    rw [homFinrank_eq_finrank,homFinrank_eq_finrank] at hEq
    rw [hfull] at hV
    rw [top_unique hV,finrank_top,← hEq]
    exact Submodule.finrank_lt hproper
  · have ht := hs.2.2 i hT hiso
    rw [P.eulerWeight_eval k] at ht
    have ha := Submodule.finrank_mono hU
    have hb := Submodule.finrank_mono hV
    rw [hr] at ha hb
    omega

end EFiniteCharacterizations.TwoTerm
