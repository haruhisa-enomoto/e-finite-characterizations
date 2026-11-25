module

public import EFiniteCharacterizations.Presentations.TwoTermFitting
public import EFiniteCharacterizations.Silting.ThickSubcategories.MaximalPresilting

/-! # Removing common summands of projective differentials -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R] [IsNoetherianRing R]
variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

noncomputable abbrev arrowEndDim (P : TwoTerm R) := Module.finrank k (End P.asArrow)

omit [IsNoetherianRing R] in
theorem finite_arrow_end (P : TwoTerm R) : Module.Finite k (End P.asArrow) := by
  have (X Y : FGModuleCat.{u} R) : Module.Finite k (X ⟶ Y) := finiteModuleHom_isFinite k X Y
  exact Module.Finite.of_injective (ArrowHom.pairLinear k P.asArrow P.asArrow)
    (ArrowHom.pairAddHom_injective _ _)

omit [IsNoetherianRing R] in
theorem class_eq_of_arrow_iso {A B : TwoTerm R} (i : A.asArrow ≅ B.asArrow) :
    A.projectiveClass = B.projectiveClass := by
  unfold projectiveClass
  exact congrArg₂ (· - ·) (ProjectiveClass.of_eq_of_iso _ _ (Arrow.rightFunc.mapIso i))
    (ProjectiveClass.of_eq_of_iso _ _ (Arrow.leftFunc.mapIso i))

/-- Splitting a strict retract splits its class. A summand with nonzero class
leaves a complement of strictly smaller endomorphism dimension. -/
theorem strict_complement {X W : TwoTerm R} (r : Retract X.asArrow W.asArrow) :
    ∃ (Y : TwoTerm R) (s : Retract Y.asArrow W.asArrow),
      s.r ≫ s.i = 𝟙 W.asArrow - (r.r ≫ r.i) ∧
      W.projectiveClass = X.projectiveClass + Y.projectiveClass ∧
      (X.projectiveClass ≠ 0 → Y.arrowEndDim k < W.arrowEndDim k) := by
  let e : End W.asArrow := r.r ≫ r.i
  have he : IsIdempotentElem e := by
    change (r.r ≫ r.i) ≫ r.r ≫ r.i = r.r ≫ r.i
    simp [Category.assoc, r.retract_assoc]
  obtain ⟨Y,s,hs⟩ := split_strict_idempotent W (1-e) he.one_sub
  have cross {A B : TwoTerm R} (p : Retract A.asArrow W.asArrow) (q : Retract B.asArrow W.asArrow)
      (h : (p.r ≫ p.i) ≫ q.r ≫ q.i = 0) : p.i ≫ q.r = 0 := by
    have hh := congrArg (fun z ↦ p.i ≫ z ≫ q.r) h
    simpa [Category.assoc, p.retract_assoc, q.retract] using hh
  have hc : r.i ≫ s.r = 0 := cross r s (by
    rw [hs]; change (1-e)*e = 0; rw [sub_mul, one_mul, he, sub_self])
  have hc' : s.i ≫ r.r = 0 := cross s r (by
    rw [hs]; change e*(1-e) = 0; rw [mul_sub, mul_one, he, sub_self])
  have total : r.r ≫ r.i + s.r ≫ s.i = 𝟙 _ := by rw [hs]; change e + (1-e) = 1; abel
  let f := r.r ≫ inlDirectSum X Y + s.r ≫ inrDirectSum X Y
  let g := fstDirectSum X Y ≫ r.i + sndDirectSum X Y ≫ s.i
  have h₁ : inlDirectSum X Y ≫ sndDirectSum X Y = 0 := by apply Arrow.hom_ext <;> exact biprod.inl_snd
  have h₂ : inrDirectSum X Y ≫ fstDirectSum X Y = 0 := by apply Arrow.hom_ext <;> exact biprod.inr_fst
  have j : W.asArrow ≅ (X.directSum Y).asArrow := {
    hom := f, inv := g
    hom_inv_id := by simpa [f,g,Preadditive.add_comp,Preadditive.comp_add,Category.assoc,
      reassoc_of% h₁,reassoc_of% h₂,reassoc_of% (inlDirectSum_fstDirectSum X Y),
      reassoc_of% (inrDirectSum_sndDirectSum X Y)] using total
    inv_hom_id := by simpa [f,g,Preadditive.add_comp,Preadditive.comp_add,Category.assoc,
      reassoc_of% hc,reassoc_of% hc',r.retract_assoc,s.retract_assoc] using totalDirectSum X Y }
  refine ⟨Y,s,hs,(class_eq_of_arrow_iso j).trans (projectiveClass_directSum X Y),fun hx ↦ ?_⟩
  have : Module.Finite k (W.asArrow ⟶ W.asArrow) := finite_arrow_end k W
  apply corner_rank_lt k s
  intro h
  have hi : r.i = 0 := by simpa [← Category.assoc, hc] using (congrArg (r.i ≫ ·) h).symm
  have hz : IsZero X.asArrow := (IsZero.iff_id_eq_zero _).2 (by rw [← r.retract, hi, zero_comp])
  apply hx
  have hsrc := Arrow.leftFunc.map_isZero hz
  have htgt := Arrow.rightFunc.map_isZero hz
  exact sub_eq_zero.mpr (ProjectiveClass.of_eq_of_iso _ _ (htgt.iso hsrc))

omit [IsNoetherianRing R] in
set_option backward.isDefEq.respectTransparency false in
private theorem class_eq_zero_of_contractible_retract {X : TwoTerm R} {T : FiniteProjective R}
    (r : Retract X.asArrow (contractible T).asArrow) : X.projectiveClass = 0 := by
  have hr := r.i.w
  have hs := r.r.w
  change r.i.left ≫ 𝟙 _ = X.differential ≫ r.i.right at hr
  change r.r.left ≫ X.differential = 𝟙 _ ≫ r.r.right at hs
  let e : X.source ≅ X.target := {
    hom := X.differential, inv := r.i.right ≫ r.r.left
    hom_inv_id := by rw [← Category.assoc, ← hr, Category.comp_id]; exact congrArg (fun f : End X.asArrow ↦ f.left) r.retract
    inv_hom_id := by rw [Category.assoc, hs, Category.id_comp]; exact congrArg (fun f : End X.asArrow ↦ f.right) r.retract }
  exact sub_eq_zero.mpr (ProjectiveClass.of_eq_of_iso _ _ e.symm)

include k in
/-- A differential with nonzero projective class has a strict summand of
nonzero class with local endomorphism ring. -/
theorem exists_local_summand {B : TwoTerm R} (hb : B.projectiveClass ≠ 0) :
    ∃ (X : TwoTerm R) (_ : Retract X.asArrow B.asArrow),
      X.projectiveClass ≠ 0 ∧ IsLocalRing (End X.asArrow) := by
  classical
  let F (n : ℕ) := ∃ X : TwoTerm R, Nonempty (Retract X.asArrow B.asArrow) ∧
    X.projectiveClass ≠ 0 ∧ X.arrowEndDim k = n
  have hn : ∃ n, F n := ⟨_,B,⟨.refl _⟩,hb,rfl⟩
  obtain ⟨X,⟨r⟩,hx,hnx⟩ := Nat.find_spec hn
  refine ⟨X,r,hx,?_⟩
  have hmin (Y : TwoTerm R) (s : Retract Y.asArrow X.asArrow) (hy : Y.projectiveClass ≠ 0) :
      X.arrowEndDim k ≤ Y.arrowEndDim k :=
    hnx ▸ Nat.find_min' hn ⟨Y,⟨s.trans r⟩,hy,rfl⟩
  have : Module.Finite k (X.asArrow ⟶ X.asArrow) := finite_arrow_end k X
  have idem (e : End X.asArrow) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
    by_contra! h
    obtain ⟨A,s,hs⟩ := split_strict_idempotent X e he
    obtain ⟨D,t,ht,hclass,_⟩ := strict_complement k s
    have hA := corner_rank_lt k s (fun hi ↦ h.2 (hs.symm.trans hi))
    have hD := corner_rank_lt k t (by
      intro hi
      rw [hs, hi] at ht
      apply h.1
      change 1 = 1 - e at ht
      exact (sub_eq_self.mp ht.symm))
    by_cases ha : A.projectiveClass = 0
    · exact (hmin D t (fun hd ↦ hx (by simp [hclass,ha,hd]))).not_gt hD
    · exact (hmin A s ha).not_gt hA
  have : Nontrivial (End X.asArrow) := nontrivial_of_ne 0 1 (by
    intro he
    have hz := (IsZero.iff_id_eq_zero X.asArrow).2 he.symm
    exact hx (sub_eq_zero.mpr (ProjectiveClass.of_eq_of_iso _ _
      ((Arrow.rightFunc.map_isZero hz).iso (Arrow.leftFunc.map_isZero hz)))))
  have : Module.Finite k (End X.asArrow) := finite_arrow_end k X
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  obtain ⟨e,c,m,he,hz,hc,ht⟩ := exists_fitting_idempotent k a
  rcases idem e he with rfl | rfl
  · rw [zero_add] at ht
    exact Or.inl ⟨⟨a,c,ht,hc.trans ht⟩,rfl⟩
  · rw [one_mul] at hz
    exact Or.inr (IsNilpotent.isUnit_one_sub ⟨m,hz⟩)

/-- A local noncontractible summand of a stable additive closure retracts
from the original differential. -/
theorem retract_of_local_stableAdd {X W : TwoTerm R} [IsLocalRing (End X.asArrow)]
    (hx : X.projectiveClass ≠ 0) (ha : X.IsInStableAdd W) : Nonempty (Retract X.asArrow W.asArrow) := by
  obtain ⟨T,pairs,he⟩ := ha
  have unitPart (l : List (End X.asArrow)) (h : IsUnit l.sum) : ∃ x ∈ l, IsUnit x := by
    induction l with
    | nil => exact (not_isUnit_zero h).elim
    | cons a l ih =>
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
      · exact ⟨a,List.mem_cons_self,h⟩
      · obtain ⟨b,hb,hu⟩ := ih h
        exact ⟨b,List.mem_cons_of_mem _ hb,hu⟩
  let l : List (End X.asArrow) := pairs.map (fun p ↦ p.1 ≫ p.2)
  obtain ⟨a,ha,hu⟩ := unitPart l ((show l.sum = 1 from he) ▸ isUnit_one)
  obtain ⟨⟨i,p⟩,_,rfl⟩ := List.mem_map.mp ha
  let c := contractible T
  let b : End X.asArrow := (i ≫ fstDirectSum W c) ≫ inlDirectSum W c ≫ p
  let d : End X.asArrow := (i ≫ sndDirectSum W c) ≫ inrDirectSum W c ≫ p
  have hab : b+d = i ≫ p := by
    simpa [b,d,c,Category.assoc,Preadditive.comp_add,Preadditive.add_comp] using
      congrArg (fun z ↦ i ≫ z ≫ p) (totalDirectSum W c)
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (hab ▸ hu) with h | h
  · have : IsIso b := (isUnit_iff_isIso _).mp h
    exact ⟨⟨inv b ≫ i ≫ fstDirectSum W c, inlDirectSum W c ≫ p, by
      simpa [b, Category.assoc] using IsIso.inv_hom_id b⟩⟩
  · have : IsIso d := (isUnit_iff_isIso _).mp h
    exact (hx (class_eq_zero_of_contractible_retract (T := T)
      ⟨inv d ≫ i ≫ sndDirectSum W c, inrDirectSum W c ≫ p, by
        simpa [d,Category.assoc] using IsIso.inv_hom_id d⟩)).elim

end EFiniteCharacterizations.TwoTerm
