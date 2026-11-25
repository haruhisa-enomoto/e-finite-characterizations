module

public import EFiniteCharacterizations.LinearAlgebra.ArrowHom
public import EFiniteCharacterizations.Presentations.BoundaryRank
public import Mathlib.RingTheory.Flat.Equalizer

/-! # Scalar extension of spaces of commuting squares -/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

namespace EFiniteCharacterizations.ScalarCategory

variable {k : Type*} [Field k] (F : Type*) [Field F] [Algebra k F]
  {C : Type*} [Category C] [Preadditive C] [Linear k C]

/-- The two components of a scalar-extended commuting square. -/
def arrowComponents {p q : Arrow C} :
    (F ⊗[k] (p ⟶ q)) →ₗ[F]
      (F ⊗[k] (p.left ⟶ q.left)) × (F ⊗[k] (p.right ⟶ q.right)) :=
  (TensorProduct.prodRight k F F (p.left ⟶ q.left) (p.right ⟶ q.right)).toLinearMap.comp
    ((ArrowHom.pairLinear k p q).baseChange F)

@[simp] theorem arrowComponents_tmul {p q : Arrow C} (s : F) (f : p ⟶ q) :
    arrowComponents F (s ⊗ₜ[k] f) = (s ⊗ₜ[k] f.left, s ⊗ₜ[k] f.right) := rfl

/-- Regard a scalar-extended commuting square as a square in the extended category. -/
def arrowMap {p q : Arrow C} (f : F ⊗[k] (p ⟶ q)) :
    (of (k := k) (S := F)).mapArrow.obj p ⟶ (of (k := k) (S := F)).mapArrow.obj q :=
  Arrow.homMk (arrowComponents F f).1 (arrowComponents F f).2 (by
    change compLinear (arrowComponents F f).1 ((1 : F) ⊗ₜ[k] q.hom) =
      compLinear ((1 : F) ⊗ₜ[k] p.hom) (arrowComponents F f).2
    refine TensorProduct.inductionOn f ?_ ?_
    · intro s a
      simp [compLinear]
    · intro a b ha hb
      simp only [map_add, Prod.fst_add, Prod.snd_add, LinearMap.add_apply, ha, hb])

@[simp] theorem arrowMap_left {p q : Arrow C} (f : F ⊗[k] (p ⟶ q)) :
    (arrowMap F f).left = (arrowComponents F f).1 := rfl

@[simp] theorem arrowMap_right {p q : Arrow C} (f : F ⊗[k] (p ⟶ q)) :
    (arrowMap F f).right = (arrowComponents F f).2 := rfl

theorem arrowMap_add {p q : Arrow C} (f g : F ⊗[k] (p ⟶ q)) :
    arrowMap F (f + g) = arrowMap F f + arrowMap F g := by
  apply Arrow.hom_ext
  · change (arrowComponents F (f + g)).1 = (arrowComponents F f).1 + (arrowComponents F g).1
    simp
  · change (arrowComponents F (f + g)).2 = (arrowComponents F f).2 + (arrowComponents F g).2
    simp

/-- Extending the Hom spaces of the arrow category maps to the arrow category
of the scalar extension. -/
def arrowComparison : ScalarCategory k F (Arrow C) ⥤ Arrow (ScalarCategory k F C) where
  obj p := (of (k := k) (S := F)).mapArrow.obj p.obj
  map f := arrowMap F f
  map_id p := by
    apply Arrow.hom_ext <;> rfl
  map_comp {p q r} f g := by
    change arrowMap F (compLinear f g) = arrowMap F f ≫ arrowMap F g
    revert g
    refine TensorProduct.inductionOn f ?_ ?_
    · intro a f g
      refine TensorProduct.inductionOn g ?_ ?_
      · intro b g
        apply Arrow.hom_ext
        · change (arrowComponents F (compLinear (a ⊗ₜ[k] f) (b ⊗ₜ[k] g))).1 =
            compLinear (arrowComponents F (a ⊗ₜ[k] f)).1 (arrowComponents F (b ⊗ₜ[k] g)).1
          simp [compLinear]
        · change (arrowComponents F (compLinear (a ⊗ₜ[k] f) (b ⊗ₜ[k] g))).2 =
            compLinear (arrowComponents F (a ⊗ₜ[k] f)).2 (arrowComponents F (b ⊗ₜ[k] g)).2
          simp [compLinear]
      · intro g h hg hh
        simp only [map_add, arrowMap_add, Preadditive.comp_add, hg, hh]
    · intro f f' hf hf' g
      simp only [map_add, LinearMap.add_apply, arrowMap_add, Preadditive.add_comp, hf g, hf' g]

instance : (arrowComparison F (k := k) (C := C)).Faithful where
  map_injective {p q} {f g} h := by
    change arrowMap F f = arrowMap F g at h
    have hi := Module.Flat.lTensor_preserves_injective_linearMap (M := F) (ArrowHom.pairLinear k p.obj q.obj)
      (ArrowHom.pairAddHom_injective p.obj q.obj)
    apply hi
    apply (TensorProduct.prodRight k F F (p.obj.left ⟶ q.obj.left) (p.obj.right ⟶ q.obj.right)).injective
    exact Prod.ext (congrArg Arrow.Hom.left h) (congrArg Arrow.Hom.right h)

instance : (arrowComparison F (k := k) (C := C)).Full where
  map_surjective {p q} f := by
    let p := p.obj
    let q := q.obj
    let E := TensorProduct.prodRight k F F (p.left ⟶ q.left) (p.right ⟶ q.right)
    let D := boundaryLinear k p.hom q.hom
    let G : C ⥤ ScalarCategory k F C := of
    let z := E.symm (f.left, f.right)
    have hz : D.baseChange F z = 0 := by
      have h := LinearMap.congr_fun (boundaryLinear_scalarExtension k F p.hom q.hom) z
      change boundaryLinear F (G.map p.hom) (G.map q.hom) (E z) = D.baseChange F z at h
      rw [show E z = (f.left, f.right) from E.apply_symm_apply _] at h
      exact h.symm.trans (sub_eq_zero.mpr f.w)
    have he : (D.baseChange F).ker = (D.ker.subtype.baseChange F).range :=
      Module.Flat.ker_lTensor_eq F F D
    obtain ⟨u, hu⟩ := he ▸ (show z ∈ (D.baseChange F).ker from hz)
    let d := (ArrowHom.equivKernel k p q).symm.toLinearMap
    let v := d.baseChange F u
    have hd : (ArrowHom.pairLinear k p q).comp d = D.ker.subtype := by
      apply LinearMap.ext
      intro y
      exact congrArg Subtype.val ((ArrowHom.equivKernel k p q).apply_symm_apply y)
    have hv : arrowComponents F v = (f.left, f.right) := by
      change E (((ArrowHom.pairLinear k p q).baseChange F) (d.baseChange F u)) = _
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hd, hu]
      exact E.apply_symm_apply _
    exact ⟨v, Arrow.hom_ext _ _ (congrArg Prod.fst hv) (congrArg Prod.snd hv)⟩

end EFiniteCharacterizations.ScalarCategory
