module

public import EFiniteCharacterizations.Silting.Fans.SectorGenerators
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! # Cokernels of presilting complexes and finite additive covers -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations

section Preadditive

variable {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]

theorem IsInAdd.map {X Y : C} (h : IsInAdd X Y) (F : C ⥤ D) [F.Additive] : IsInAdd (F.obj X) (F.obj Y) := by
  obtain ⟨l, hl⟩ := h
  refine ⟨l.map (fun p ↦ (F.map p.1, F.map p.2)), ?_⟩
  have hm := congrArg (F.mapAddHom : (X ⟶ X) →+ (F.obj X ⟶ F.obj X)) hl
  rw [map_list_sum, List.map_map] at hm
  change _ = F.map (𝟙 X) at hm
  rw [F.map_id] at hm
  rw [List.map_map]
  change (l.map (fun p ↦ F.map p.1 ≫ F.map p.2)).sum = 𝟙 (F.obj X)
  simpa only [Function.comp_def, Functor.mapAddHom_apply, Functor.map_comp] using hm

variable (C) [HasCokernels C]

/-- Taking the cokernel is a functor on commuting squares. -/
noncomputable def arrowCokernel : Arrow C ⥤ C where
  obj p := cokernel p.hom
  map {p q} f := cokernel.map p.hom q.hom f.left f.right f.w.symm
  map_id p := cokernel.map_id p.hom _ _
  map_comp {p q r} f g := by
    apply (cancel_epi (cokernel.π p.hom)).mp
    simp [cokernel.map, Category.assoc]

instance : (arrowCokernel C).Additive where
  map_add {p q} f g := by
    apply (cancel_epi (cokernel.π p.hom)).mp
    unfold arrowCokernel
    rw [Preadditive.comp_add]
    simp [cokernel.map, Preadditive.add_comp]

end Preadditive

namespace TwoTerm

variable {R : Type u} [Ring R]

/-- The cokernel of an identity differential is zero. -/
theorem isZero_cokernel_contractible (T : FiniteProjective R) : IsZero (cokernel (contractible T).differential) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  have hz : cokernel.π (contractible T).differential = 0 := by
    have h := cokernel.condition (contractible T).differential
    change (𝟙 T.val) ≫ cokernel.π (contractible T).differential = 0 at h
    exact (Category.id_comp _).symm.trans h
  apply (cancel_epi (cokernel.π (contractible T).differential)).mp
  simp [hz]

theorem isInAdd_cokernel_of_isInStableAdd {P Q : TwoTerm R} (h : P.IsInStableAdd Q) :
    IsInAdd (cokernel P.differential) (cokernel Q.differential) := by
  obtain ⟨T, hT⟩ := h
  let F := arrowCokernel (FGModuleCat.{u} R)
  let I := contractible T
  have hz : IsZero (F.obj I.asArrow) := isZero_cokernel_contractible T
  have hzero : F.map (sndDirectSum Q I ≫ inrDirectSum Q I) = 0 := by
    rw [F.map_comp, hz.eq_of_src (F.map (inrDirectSum Q I)) 0, comp_zero]
  have hcomp := congrArg (F.map (X := (Q.directSum I).asArrow) (Y := (Q.directSum I).asArrow)) (totalDirectSum Q I)
  rw [Functor.map_add, hzero, add_zero, F.map_comp, F.map_id] at hcomp
  exact (hT.map F).trans (IsInAdd.of_retraction _ _ hcomp)

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
/-- In rank at most two, the cokernels of all presilting differentials of an
E-finite algebra belong to the additive closures of a finite list of modules. -/
theorem exists_finite_cokernel_generators_of_rank_le_two
    (hr : (simpleIsomorphismClasses R).ncard ≤ 2) (hR : IsEFinite R) :
    ∃ s : List (FGModuleCat.{u} R), ∀ P : TwoTerm R, P.IsPresilting →
      ∃ M ∈ s, IsInAdd (cokernel P.differential) M := by
  obtain ⟨s, _, hs⟩ := exists_finite_stable_add_generators_of_rank_le_two k hr hR
  refine ⟨s.map (fun Q ↦ cokernel Q.differential), fun P hP ↦ ?_⟩
  obtain ⟨Q, hQ, hpq⟩ := hs P hP
  exact ⟨cokernel Q.differential, List.mem_map.mpr ⟨Q, hQ, rfl⟩, isInAdd_cokernel_of_isInStableAdd hpq⟩

end TwoTerm

end EFiniteCharacterizations
