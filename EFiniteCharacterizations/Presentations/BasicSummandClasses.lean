module

public import EFiniteCharacterizations.Silting.ThickSubcategories.ThickInversion
public import EFiniteCharacterizations.Presentations.StrictSummands

/-! # The projective classes contributed by a basic decomposition -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
universe u

namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R] [IsNoetherianRing R]
private noncomputable abbrev F := doubleFunctor (C := FGModuleCat.{u} R) ⋙ HomotopyCategory.quotient _ _

private theorem nonzero_of_class_ne {X : TwoTerm R} (hx : X.projectiveClass ≠ 0) : ¬ IsZero X.homotopyObject := by
  intro hz
  let Z := contractible (ProjectiveClass.zeroProjective R)
  have ht : InThick Z X := (ObjectProperty.singleton Z.homotopyObject).triangEnvelope.prop_of_isZero hz
  have : IsIso X.differential := isIso_map_of_inThick (𝟭 _) ht (inferInstanceAs (IsIso (𝟙 _)))
  exact hx (sub_eq_zero.mpr (ProjectiveClass.of_eq_of_iso _ _ (asIso X.differential).symm))

private noncomputable def realizeEnd (X : TwoTerm R) : End X.asArrow →+* End X.homotopyObject where
  toFun := F.map
  map_zero' := F.map_zero _ _
  map_one' := F.map_id _
  map_add' _ _ := F.map_add
  map_mul' a b := F.map_comp b a

private theorem class_eq_of_local_homotopy_iso {X Y : TwoTerm R}
    [IsLocalRing (End X.asArrow)] [IsLocalRing (End Y.asArrow)]
    (hx : X.projectiveClass ≠ 0) (hy : Y.projectiveClass ≠ 0) (e : X.homotopyObject ≅ Y.homotopyObject) :
    X.projectiveClass = Y.projectiveClass := by
  obtain ⟨a,ha⟩ := F.map_surjective (show F.obj X.asArrow ⟶ F.obj Y.asArrow from e.hom)
  obtain ⟨b,hb⟩ := F.map_surjective (show F.obj Y.asArrow ⟶ F.obj X.asArrow from e.inv)
  have unit {T : TwoTerm R} [IsLocalRing (End T.asArrow)] (ht : T.projectiveClass ≠ 0)
      (z : End T.asArrow) (hz : F.map z = 𝟙 _) : IsIso z := by
    let _ : Nontrivial (End T.homotopyObject) := nontrivial_of_ne 1 0
      (fun h ↦ nonzero_of_class_ne ht ((IsZero.iff_id_eq_zero _).2 h))
    apply (isUnit_iff_isIso _).1
    refine (IsLocalRing.isUnit_or_isUnit_one_sub_self z).resolve_right (fun h ↦ ?_)
    have bad := h.map (realizeEnd T)
    have he : realizeEnd T z = 1 := hz
    rw [map_sub,map_one,he,sub_self] at bad
    exact not_isUnit_zero bad
  have hu : IsIso (a ≫ b) := unit hx _ (by rw [Functor.map_comp,ha,hb]; exact e.hom_inv_id)
  have hv : IsIso (b ≫ a) := unit hy _ (by rw [Functor.map_comp,hb,ha]; exact e.inv_hom_id)
  let c := b ≫ inv (a ≫ b)
  have hc : a ≫ c = 𝟙 _ := (Category.assoc a b _).symm.trans (IsIso.hom_inv_id _)
  have hd : c ≫ a = 𝟙 _ := (cancel_mono (b ≫ a)).1 (by
    calc
      (c ≫ a) ≫ (b ≫ a) = b ≫ (inv (a ≫ b) ≫ (a ≫ b)) ≫ a := by simp only [c,Category.assoc]
      _ = 𝟙 _ ≫ (b ≫ a) := by rw [IsIso.inv_hom_id]; simp)
  exact class_eq_of_arrow_iso ⟨a,c,hc,hd⟩

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
/-- The classes of all strict summands in add(P) lie in a subgroup generated
by at most one class for each member of a basic homotopy decomposition. -/
theorem exists_basic_summand_coordinates (P : TwoTerm R) {l} (hl : BasicDecomposition P l) :
    ∃ v : Fin l.length → ProjectiveClass R, ∀ X : TwoTerm R, IsInAdd X.asArrow P.asArrow →
      X.projectiveClass ∈ Submodule.span ℤ (Set.range v) := by
  classical
  let rep (i : Fin l.length) (X : TwoTerm R) := X.projectiveClass ≠ 0 ∧ IsLocalRing (End X.asArrow) ∧
    Nonempty (X.homotopyObject ≅ l[i])
  let v (i : Fin l.length) := if h : ∃ X, rep i X then h.choose.projectiveClass else 0
  refine ⟨v,?_⟩
  let W := Submodule.span ℤ (Set.range v)
  have loc (X : TwoTerm R) (hadd : IsInAdd X.asArrow P.asArrow) (hx : X.projectiveClass ≠ 0)
      [IsLocalRing (End X.asArrow)] : X.projectiveClass ∈ W := by
    let _ : Nontrivial (End X.homotopyObject) := nontrivial_of_ne 1 0
      (fun h ↦ nonzero_of_class_ne hx ((IsZero.iff_id_eq_zero _).2 h))
    let _ : IsLocalRing (End X.homotopyObject) := IsLocalRing.of_surjective' (realizeEnd X)
      (fun a ↦ F.map_surjective (show F.obj X.asArrow ⟶ F.obj X.asArrow from a))
    obtain ⟨D,hD,⟨e⟩⟩ := iso_mem_basic_of_local (nonzero_of_class_ne hx) hl (hadd.map F)
    obtain ⟨j,hj,h⟩ := List.mem_iff_getElem.mp hD
    let i : Fin l.length := ⟨j,hj⟩
    have hrep : rep i X := ⟨hx,inferInstance,⟨e ≪≫ eqToIso h.symm⟩⟩
    have ex : ∃ T, rep i T := ⟨X,hrep⟩
    have spec := ex.choose_spec
    let _ : IsLocalRing (End ex.choose.asArrow) := spec.2.1
    apply Submodule.subset_span
    refine ⟨i,?_⟩
    rw [show v i = ex.choose.projectiveClass from dite_eq_left ex]
    exact class_eq_of_local_homotopy_iso spec.1 hx (spec.2.2.some ≪≫ hrep.2.2.some.symm)
  intro X hX
  change X.projectiveClass ∈ W
  generalize hn : X.arrowEndDim k = n
  induction n using Nat.strong_induction_on generalizing X with
  | h n ih =>
    by_cases hz : X.projectiveClass = 0
    · rw [hz]; exact W.zero_mem
    obtain ⟨A,r,ha,hlocal⟩ := exists_local_summand k hz
    obtain ⟨B,s,_,hclass,hlt⟩ := strict_complement k r
    rw [hclass]
    exact W.add_mem (loc A ((IsInAdd.of_retraction _ _ r.retract).trans hX) ha)
      (ih _ (hn ▸ hlt ha) B ((IsInAdd.of_retraction _ _ s.retract).trans hX) rfl)

end EFiniteCharacterizations.TwoTerm
