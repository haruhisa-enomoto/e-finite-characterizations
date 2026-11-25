module

public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import Mathlib.RingTheory.Idempotents
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Primitive projections and indecomposable module summands -/

@[expose] public section

namespace EFiniteCharacterizations

namespace PrimitiveSummand

open CategoryTheory CategoryTheory.Limits

/-- An idempotent with simple image has no proper nonzero subprojection. -/
private theorem subprojection_of_simple_image {D T : Type*} [Ring D] [AddCommGroup T] [Module D T]
    (q b : Module.End D T) (hb : IsIdempotentElem b) (hqb : q*b = b) (hbq : b*q = b)
    (hq : IsAtom (LinearMap.range q)) : b = 0 ∨ b = q := by
  have le : LinearMap.range b ≤ LinearMap.range q := by
    rintro _ ⟨z,rfl⟩
    exact ⟨b z,LinearMap.congr_fun hqb z⟩
  by_cases h : LinearMap.range b = LinearMap.range q
  · right
    ext z
    rw [← LinearMap.congr_fun hbq z]
    exact (LinearMap.IsIdempotentElem.mem_range_iff hb).1 (h ▸ LinearMap.mem_range_self q z)
  · exact Or.inl (LinearMap.range_eq_bot.mp (hq.2 _ (lt_of_le_of_ne le h)))

/-- Given a lift of a projection with simple image through a homomorphism
with nil kernel, every subprojection of the lift is zero or the whole lift. -/
theorem trivial_subprojections_of_lift {A D T : Type*} [Ring A] [Ring D] [AddCommGroup T]
    [Module D T] (p : A →+* Module.End D T) (hk : ∀ a ∈ RingHom.ker p, IsNilpotent a)
    {e : A} (he : IsIdempotentElem e) (hr : IsAtom (LinearMap.range (p e))) (b : A)
    (hb : IsIdempotentElem b) (heb : e*b = b) (hbe : b*e = b) : b = 0 ∨ b = e := by
  have hb' : IsIdempotentElem (p b) := by simpa [IsIdempotentElem] using congrArg p hb.eq
  rcases subprojection_of_simple_image (p e) (p b) hb' (by simpa using congrArg p heb)
    (by simpa using congrArg p hbe) hr with hz | heq
  · exact Or.inl (hb.eq_zero_of_isNilpotent (hk b (RingHom.mem_ker.mpr hz)))
  · exact Or.inr (eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute hb he
      (hk _ (RingHom.mem_ker.mpr (by simp [heq]))) (hbe.trans heb.symm))

/-- In a semisimple module, a projection onto a simple submodule detects any
prescribed nonzero vector. -/
theorem exists_simple_projection {D T : Type*} [Ring D] [AddCommGroup T] [Module D T]
    [IsSemisimpleModule D T] (v : T) (hv : v ≠ 0) :
    ∃ q : Module.End D T, IsIdempotentElem q ∧ IsAtom (LinearMap.range q) ∧ q v ≠ 0 := by
  let U := Submodule.span D {v}
  have hvU : v ∈ U := Submodule.subset_span (Set.mem_singleton v)
  obtain ⟨L,hL,hS⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le U).resolve_left (fun h ↦
    hv ((Submodule.mem_bot D).mp (h ▸ hvU)))
  obtain ⟨W,hW⟩ := exists_isCompl L
  let q := L.projection W hW
  have hr : LinearMap.range q = L := Submodule.range_projection hW
  have hat := isSimpleModule_iff_isAtom.mp hS
  refine ⟨q,Submodule.isIdempotentElem_projection hW,hr ▸ hat,fun hz ↦ hat.1 ?_⟩
  have hker : U ≤ LinearMap.ker q := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hz)
  apply le_antisymm _ bot_le
  intro w hw
  have hzero : q w = 0 := hker (hL hw)
  exact (Submodule.projection_apply_of_mem_left hW hw).symm.trans hzero

private theorem indecomposable_of_trivial_idempotents {R : Type*} [Ring R] (G : ModuleCat R)
    (hne : ¬ IsZero G) (h : ∀ a : Module.End R G, IsIdempotentElem a → a = 0 ∨ a = 1) :
    Indecomposable G := by
  refine ⟨hne,fun Y Z iso ↦ ?_⟩
  let d := (iso ≪≫ ModuleCat.biprodIsoProd Y Z).toLinearEquiv
  let f := (LinearMap.inl R Y Z).comp (LinearMap.fst R Y Z)
  let a := d.symm.toLinearMap.comp (f.comp d.toLinearMap)
  have apply_a (x : G) : d (a x) = ((d x).1, 0) := d.apply_symm_apply _
  have ha : IsIdempotentElem a := by
    ext x
    apply d.injective
    change d (a (a x)) = d (a x)
    rw [apply_a, apply_a]
  rcases h a ha with hz | ho
  · left
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro y
    have eq := congrArg Prod.fst (apply_a (d.symm (y,0)))
    simpa [hz] using eq.symm
  · right
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro z
    have eq := congrArg Prod.snd (apply_a (d.symm (0,z)))
    simpa [ho] using eq

/-- The image of a nonzero primitive idempotent is indecomposable. -/
theorem indecomposable_range {R : Type*} [Ring R] {N : ModuleCat R}
    (e : Module.End R N) (he : IsIdempotentElem e) (hne : e ≠ 0)
    (hprim : ∀ b : Module.End R N, IsIdempotentElem b → e*b = b → b*e = b → b = 0 ∨ b = e) :
    Indecomposable (ModuleCat.of R (LinearMap.range e)) := by
  let G := ModuleCat.of R (LinearMap.range e)
  let i : G →ₗ[R] N := (LinearMap.range e).subtype
  let r : N →ₗ[R] G := e.rangeRestrict
  have ri (x : G) : r (i x) = x :=
    Subtype.ext ((LinearMap.IsIdempotentElem.mem_range_iff he).1 x.property)
  apply indecomposable_of_trivial_idempotents G
  · intro hzero
    have : Subsingleton G := ModuleCat.isZero_iff_subsingleton.mp hzero
    exact hne (LinearMap.ext fun x ↦ congrArg i (Subsingleton.elim (r x) 0))
  · intro a ha
    let b := i.comp (a.comp r)
    have hb : IsIdempotentElem b := LinearMap.ext fun x ↦ by
      change i (a (r (i (a (r x))))) = i (a (r x))
      rw [ri, ← Module.End.mul_apply,ha.eq]
    have eb : e*b = b := LinearMap.ext fun x ↦ (LinearMap.IsIdempotentElem.mem_range_iff he).1 (a (r x)).property
    have be : b*e = b := LinearMap.ext fun x ↦ congrArg (fun z ↦ i (a z)) (ri (r x))
    rcases hprim b hb eb be with hz | ho
    · left
      exact LinearMap.ext fun x ↦ Subtype.ext (by
        have eq := LinearMap.congr_fun hz (i x)
        change i (a (r (i x))) = 0 at eq
        rwa [ri] at eq)
    · right
      exact LinearMap.ext fun x ↦ Subtype.ext (by
        have eq := LinearMap.congr_fun ho (i x)
        change i (a (r (i x))) = i (r (i x)) at eq
        rwa [ri] at eq)

/-- A nonzero test vector for the action modulo a nil kernel yields an
indecomposable summand on which the original vector has nonzero projection. -/
theorem exists_retract_detecting {R D T : Type*} [Ring R] {N : ModuleCat R} [Ring D]
    [AddCommGroup T] [Module D T] [IsSemisimpleModule D T]
    (p : Module.End R N →+* Module.End D T) (hs : Function.Surjective p)
    (hk : ∀ a ∈ RingHom.ker p, IsNilpotent a) (x : N) (v : T) (hv : v ≠ 0)
    (test : ∀ e : Module.End R N, e x = 0 → p e v = 0) :
    ∃ (G : ModuleCat R) (r : Retract G N), Indecomposable G ∧ r.r.hom x ≠ 0 := by
  obtain ⟨q,hq,hat,hv⟩ := exists_simple_projection (D := D) v hv
  obtain ⟨e,he,heq⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent p hk q (hs q) hq
  have hne : e x ≠ 0 := fun h ↦ hv (heq ▸ test e h)
  have hp := trivial_subprojections_of_lift p hk he (heq.symm ▸ hat)
  have hind := indecomposable_range e he (fun h ↦ hne (by simp [h])) hp
  let G := ModuleCat.of R (LinearMap.range e)
  let r : Retract G N :=
    ⟨ModuleCat.ofHom (LinearMap.range e).subtype,ModuleCat.ofHom e.rangeRestrict,
      ModuleCat.hom_ext (LinearMap.ext fun z ↦ Subtype.ext
        ((LinearMap.IsIdempotentElem.mem_range_iff he).1 z.property))⟩
  exact ⟨G,r,hind,fun h ↦ hne (congrArg Subtype.val h)⟩

end PrimitiveSummand
end EFiniteCharacterizations
