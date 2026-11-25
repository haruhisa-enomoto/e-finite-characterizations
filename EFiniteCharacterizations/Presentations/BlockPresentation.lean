module

public import EFiniteCharacterizations.Silting.ThickSubcategories.MaximalPresilting
public import EFiniteCharacterizations.Presentations.RigidPowers

/-! # A presentation on two-term projective representatives -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations.TwoTerm
set_option backward.isDefEq.respectTransparency false
variable (k : Type u) [Field k] {R : Type u} [Ring R] [IsNoetherianRing R] [Algebra k R] [Module.Finite k R]

include k in
/-- Enlarge the first term of the silting presentation to a finite sum of
copies of T. The new middle term is an actual block extension in add(T),
and its projective class is the sum of the two end classes. -/
theorem exists_block_presentation (T Y : TwoTerm R) (ht : T.IsPresilting)
    (hgen : ∀ X : TwoTerm R, InThick T X) (hy : Function.Surjective (homotopyBoundary T Y)) :
    ∃ (n : ℕ) (w : Y.source ⟶ (T.copies n).target),
      IsInAdd ((T.copies n).blockExtension Y w).homotopyObject T.homotopyObject := by
  have := homotopyHom_finite k T Y
  have htp := (isPresilting_iff_homotopy T).1 ht
  obtain ⟨A,D,i,p,δ,hK,hA,hD⟩ := Presilting.exists_presentation k T.homotopyObject Y.homotopyObject htp
    (hgen Y) ((surjective_boundary_iff_homotopy T Y).1 hy) (fun _ hn ↦ subsingleton_hom_shift_of_one_lt Y T hn)
  obtain ⟨n,⟨r⟩⟩ := exists_retract_copies T hA
  let W := T.copies n
  obtain ⟨w, hw⟩ := exists_blockTriangle_of_connecting W Y (δ ≫ r.i⟦(1 : ℤ)⟧')
  let Z := W.blockExtension Y w
  let L := blockTriangle W Y w
  let K := Triangle.mk i p δ
  have hL := blockTriangle_distinguished W Y w
  have hWT : IsInAdd W.homotopyObject T.homotopyObject :=
    (isInAdd_copies T n).map (doubleFunctor ⋙ HomotopyCategory.quotient _ _)
  have hpos : T.shiftedHomFinrank k Z = 0 := by
    have (X V : FGModuleCat.{u} R) : Module.Finite k (X ⟶ V) := finiteModuleHom_isFinite k X V
    have h := LinearMap.finrank_le_finrank_of_surjective
      (blockCokernelInclusion_surjective k W.differential Y.differential w T.differential hy)
    apply Nat.eq_zero_of_le_zero (h.trans _)
    change T.shiftedHomFinrank k (T.copies n) ≤ 0
    rw [shiftedHomFinrank_copies_target, (shiftedHomFinrank_eq_zero_iff k T T).2 ht, Nat.mul_zero]
  refine ⟨n,w,Presilting.isInAdd_of_mem_thick _ htp (hgen Z)
    ((surjective_boundary_iff_homotopy T Z).1 ((shiftedHomFinrank_eq_zero_iff k T Z).1 hpos)) ?_⟩
  intro t h
  have hz (f : Z.homotopyObject ⟶ T.homotopyObject⟦t⟧) : f = 0 := by
    obtain ⟨g,hg⟩ := Triangle.yoneda_exact₂ L hL f ((subsingleton_from_add hWT (htp t h)).elim _ _)
    obtain ⟨b,hb⟩ := Triangle.yoneda_exact₃ K hK g ((subsingleton_from_add hD (htp t h)).elim _ _)
    have hδ : L.mor₂ ≫ δ = 0 := by
      have hh := congrArg (fun q ↦ q ≫ r.r⟦(1 : ℤ)⟧') (comp_distTriang_mor_zero₂₃ L hL)
      rw [show L.mor₃ = _ from hw, Category.assoc, Category.assoc,
        ← Functor.map_comp, r.retract, (shiftFunctor _ (1 : ℤ)).map_id, Category.comp_id, zero_comp] at hh
      exact hh
    change g = δ ≫ b at hb
    rw [hg,hb,← Category.assoc,hδ,zero_comp]
  exact ⟨fun f g ↦ (hz f).trans (hz g).symm⟩

include k in
/-- When V in add(T) has the class of Y, the presentation has middle term
isomorphic to W ⊕ V for a finite sum W of copies of T. -/
theorem exists_biprod_presentation (T Y V : TwoTerm R) (ht : T.IsPresilting)
    (hgen : ∀ X : TwoTerm R, InThick T X) (hy : Function.Surjective (homotopyBoundary T Y))
    (hv : IsInAdd V.homotopyObject T.homotopyObject) (hc : Y.projectiveClass = V.projectiveClass) :
    ∃ n : ℕ, let W := (T.copies n).homotopyObject
      ∃ (i : W ⟶ W ⊞ V.homotopyObject) (p : W ⊞ V.homotopyObject ⟶ Y.homotopyObject)
        (δ : Y.homotopyObject ⟶ W⟦(1 : ℤ)⟧), Triangle.mk i p δ ∈ distTriang _ := by
  obtain ⟨n,w,hz⟩ := exists_block_presentation k T Y ht hgen hy
  let W := T.copies n
  let Z := W.blockExtension Y w
  have hw : IsInAdd W.homotopyObject T.homotopyObject :=
    (isInAdd_copies T n).map (doubleFunctor ⋙ HomotopyCategory.quotient _ _)
  obtain ⟨e⟩ := nonempty_homotopyIso_of_isPresilting_of_class_eq k Z (W.directSum V)
    (isPresilting_of_homotopy_isInAdd ht hz)
    (isPresilting_of_homotopy_isInAdd ht (isInAdd_homotopy_directSum hw hv))
    (by rw [projectiveClass_directSum, ← hc]; exact projectiveClass_blockExtension W Y w)
  let j := e ≪≫ directSumHomotopyIso W V
  let L := blockTriangle W Y w
  refine ⟨n, L.mor₁ ≫ j.hom, j.inv ≫ L.mor₂, L.mor₃,
    isomorphic_distinguished L (blockTriangle_distinguished W Y w) _ ?_⟩
  exact Triangle.isoMk _ _ (Iso.refl _) j.symm (Iso.refl _) (by simp [Category.assoc])
    (by simp) (by simp)

end EFiniteCharacterizations.TwoTerm
