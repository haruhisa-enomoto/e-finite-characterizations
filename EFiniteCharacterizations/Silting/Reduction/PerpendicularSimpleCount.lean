module

public import EFiniteCharacterizations.Silting.Reduction.BongartzCounting
public import EFiniteCharacterizations.Silting.Reduction.BasicBongartzCompletion
public import EFiniteCharacterizations.Stability.SemistableSimples
public import EFiniteCharacterizations.Stability.SemistableApproximations
public import EFiniteCharacterizations.LargeModules.LargePerpendicular
public import EFiniteCharacterizations.Stability.StableSeparationWeights
public import EFiniteCharacterizations.Stability.StableFiniteness
public import EFiniteCharacterizations.Silting.ThickSubcategories.ThickGeneration
public import EFiniteCharacterizations.Silting.ThickSubcategories.ThickInversion

/-!
# Rank of the `τ`-perpendicular category and basic silting summand count

Completes Lemma 2.2 (`lem:perpendicular`) over an arbitrary field:

* `perpendicular_simple_count` and `basic_perpendicular_reduction`: for a basic
  two-term presilting complex `P` with `r` indecomposable summands, the reduction
  category `J(P)` has `n - r` isomorphism classes of simple objects.
* `basic_silting_summand_count`: in particular, a basic two-term silting complex has
  exactly `n` indecomposable summands.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations.TwoTerm

private theorem independent_with_diagonal_tests {A I J : Type*} [AddCommGroup A] [Fintype I] [Fintype J]
    (a : I → A) (b : J → A) (f : J → A →+ ℤ) (ha : LinearIndependent ℤ a)
    (hz : ∀ i j, f j (a i) = 0) (hd : ∀ i, f i (b i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → f j (b i) = 0) : LinearIndependent ℤ (Sum.elim a b) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [Fintype.sum_sum_type] at hc
  have hr (j : J) : c (.inr j) = 0 := by
    have h := congrArg (f j) hc
    simp only [map_add,map_sum,map_zsmul,map_zero,Sum.elim_inl,Sum.elim_inr,hz,zsmul_zero,
      Finset.sum_const_zero,zero_add] at h
    rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [hoff i j hij,zsmul_zero])
      (fun h ↦ (h (Finset.mem_univ _)).elim)] at h
    exact (mul_eq_zero.mp (by simpa using h)).resolve_right (hd j)
  simp only [Sum.elim_inl,Sum.elim_inr,hr,zero_smul,Finset.sum_const_zero,add_zero] at hc
  exact Sum.rec (Fintype.linearIndependent_iff.mp ha _ hc) hr

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

omit [IsArtinianRing R] in
/-- The basic summands and the stable simples contribute independent
projective weights, giving the upper bound in the perpendicular rank formula. -/
theorem summand_count_add_stable_count_le (P : TwoTerm R) (hp : P.IsPresilting) {l}
    (hl : BasicDecomposition P l) :
    l.length + (stableClasses (P.eulerWeight k)).ncard ≤ (simpleIsomorphismClasses R).ncard := by
  classical
  let J := ↥(stableClasses (P.eulerWeight k))
  let _ : Fintype J := (P.finite_stableClasses_eulerWeight k hp).fintype
  let S (j : J) := (fromSkeleton _).obj j.val
  have hs (j : J) : (P.eulerWeight k).IsStable (S j) := j.property
  obtain ⟨a,hadd,hi⟩ := independent_basic_family k P hp l hl
  choose b hb hsep using fun j ↦ P.exists_stable_separating_projective_weight k hp (hs j)
  let f (j : J) : ProjectiveClass R →+ ℤ :=
    { toFun := fun g ↦ (projectiveClassWeight k g).eval (S j)
      map_zero' := by simp [Weight.eval]
      map_add' := by intros; simp [Weight.eval] }
  have hz (i : Fin l.length) (j : J) : f j (a i).projectiveClass = 0 := by
    have h := invertedOn_of_inThick (inThick_of_isInAdd P (a i) (hadd i)) (S j).obj
      ((P.invertedOn_iff_semistable k hp (S j)).2 (hs j).isSemistable)
    have hw := (((a i).invertedOn_iff_semistable k (isPresilting_of_homotopy_isInAdd hp (hadd i)) (S j)).1 h).1
    change (projectiveClassWeight k (a i).projectiveClass).eval _ = 0
    rwa [projectiveClassWeight_eq_eulerWeight]
  have hoff (i j : J) (h : i ≠ j) : f j (b i) = 0 := by
    apply hsep i (S j) (hs j)
    rintro ⟨e⟩
    exact h (Subtype.ext ((toSkeleton_fromSkeleton_obj i.val).symm.trans
      ((congr_toSkeleton_of_iso e).trans (toSkeleton_fromSkeleton_obj j.val))))
  have ind := independent_with_diagonal_tests (fun i ↦ (a i).projectiveClass) b f hi hz
    (fun i ↦ (hb i).ne') hoff
  simpa [J] using card_le_simple_count_of_independent_projective_classes k _ ind

/-- The number of simple objects in the semistable perpendicular category
is the ambient simple count minus the number of basic summands. -/
theorem perpendicular_simple_count (P : TwoTerm R) (hp : P.IsPresilting) {l}
    (hl : BasicDecomposition P l) :
    (semistableSimpleClasses (P.eulerWeight k)).ncard = (simpleIsomorphismClasses R).ncard - l.length := by
  classical
  let _ := (P.finite_stableClasses_eulerWeight k hp).fintype
  obtain ⟨w,hw⟩ := P.exists_spanning_weights_for_perpendicular k hp hl
  have lo := simple_count_le_card_of_spanning_projectives k w hw
  have hi := P.summand_count_add_stable_count_le k hp hl
  rw [ncard_semistableSimpleClasses]
  simp only [Fintype.card_sum,Fintype.card_fin,Set.fintypeCard_eq_ncard] at lo
  omega

include k in
/-- A two-term basic silting complex has exactly the ambient number of simple modules
as its number of indecomposable summands. -/
theorem basic_silting_summand_count (P : TwoTerm R) (hp : P.IsPresilting) {l}
    (hl : BasicDecomposition P l) (gen : ∀ X : TwoTerm R, InThick P X) :
    l.length = (simpleIsomorphismClasses R).ncard := by
  classical
  have empty : stableClasses (P.eulerWeight k) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    have hs : (P.eulerWeight k).IsStable ((fromSkeleton _).obj x) := hx
    exact hs.1 (isZero_semistable_of_silting k P hp gen _ hs.isSemistable)
  have hc := P.perpendicular_simple_count k hp hl
  rw [ncard_semistableSimpleClasses,empty,Set.ncard_empty] at hc
  have upper := basicDecomposition_length_le k P hp hl
  omega

/-- The perpendicular reduction lemma for a basic presilting complex, with
the simple count taken inside the Hom-perpendicular category itself. -/
theorem basic_perpendicular_reduction (P T : TwoTerm R) (hp : P.IsPresilting) {l}
    (hl : BasicDecomposition P l) (ht : T.IsPresilting)
    (bongartz : ∀ M : FGModuleCat.{u} R, IsGeneratedBy (cokernel T.differential) M ↔
      Subsingleton (M ⟶ P.nakayamaKernel k)) :
    let W : ObjectProperty (FGModuleCat.{u} R) := fun M ↦ Subsingleton (cokernel P.differential ⟶ M) ∧
      Subsingleton (M ⟶ P.nakayamaKernel k)
    IsWideClass W ∧ FunctoriallyFinite W ∧
      {x : Skeleton W.FullSubcategory | Simple ((fromSkeleton _).obj x)}.ncard =
        (simpleIsomorphismClasses R).ncard - l.length ∧
      ∃ (I : Ideal (End (cokernel T.differential))) (_ : I.IsTwoSided),
        (∀ f, f ∈ I ↔ ∃ (n : ℕ) (a : cokernel T.differential ⟶ ⨁ fun _ : Fin n ↦ cokernel P.differential)
          (b : (⨁ fun _ : Fin n ↦ cokernel P.differential) ⟶ cokernel T.differential), a ≫ b = f) ∧
        Nonempty (W.FullSubcategory ≌ FGModuleCat.{u} (End (cokernel T.differential) ⧸ I)ᵐᵒᵖ) := by
  let θ := P.eulerWeight k
  let W : ObjectProperty (FGModuleCat.{u} R) := fun M ↦ Subsingleton (cokernel P.differential ⟶ M) ∧
    Subsingleton (M ⟶ P.nakayamaKernel k)
  have eq : W = θ.IsSemistable := funext fun M ↦ (propext (P.isSemistable_eulerWeight_iff_perpendicular k hp M)).symm
  have hw : IsWideClass W := by rw [eq]; exact θ.isWideClass_semistable
  have hf : FunctoriallyFinite W := by rw [eq]; exact P.functoriallyFinite_semistable k hp
  refine ⟨hw,hf,?_,
    perpendicular_equivalence_of_bongartz k P T hp ht bongartz⟩
  change {x : Skeleton W.FullSubcategory | Simple ((fromSkeleton _).obj x)}.ncard = _
  rw [eq]
  exact P.perpendicular_simple_count k hp hl

end EFiniteCharacterizations.TwoTerm
