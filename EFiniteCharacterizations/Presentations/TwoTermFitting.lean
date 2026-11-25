module

public import EFiniteCharacterizations.LinearAlgebra.FittingIdempotent
public import EFiniteCharacterizations.Presentations.RigidPowers
public import Mathlib.CategoryTheory.Idempotents.Basic

/-! # Fitting decomposition on two-term projective representatives -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra

namespace EFiniteCharacterizations.TwoTerm

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]

set_option backward.isDefEq.respectTransparency false in
instance : (doubleFunctor (C := C)).Full where
  map_surjective {A B} f := by
    let s (A : Arrow C) := doubleXIso₀ A.hom adjacent
    let t (A : Arrow C) := doubleXIso₁ A.hom adjacent (by decide)
    let l := (s A).inv ≫ f.f (-1) ≫ (s B).hom
    let r := (t A).inv ≫ f.f 0 ≫ (t B).hom
    have h : l ≫ B.hom = A.hom ≫ r := by
      have eq := congrArg (fun z ↦ (s A).inv ≫ z ≫ (t B).hom) (f.comm (-1) 0)
      simpa [s,t,l,r,doubleFunctor,double_d _ adjacent (by decide),Category.assoc] using eq
    refine ⟨Arrow.homMk l r h, from_double_hom_ext (hi₀₁ := adjacent) ?_ ?_⟩ <;> simp [doubleFunctor,doubleMap,s,t,l,r]

universe u
variable {R : Type u} [Ring R] [IsNoetherianRing R]
variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

private noncomputable abbrev realize := doubleFunctor (C := FGModuleCat.{u} R) ⋙ HomotopyCategory.quotient _ _

theorem split_strict_idempotent (W : TwoTerm R) (e : End W.asArrow) (he : e*e = e) :
    ∃ (N : TwoTerm R) (r : Retract N.asArrow W.asArrow), r.r ≫ r.i = e := by
  let : IsIdempotentComplete (Arrow (FGModuleCat.{u} R)) :=
    (Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent _).2 (fun _ _ _ ↦ inferInstance)
  obtain ⟨A,i,p,h₁,h₂⟩ := IsIdempotentComplete.idempotents_split W.asArrow e he
  have hs : Module.Projective R W.asArrow.left := W.projective_source
  have ht : Module.Projective R W.asArrow.right := W.projective_target
  have ps : Module.Projective R A.left := Module.Projective.of_split i.left.hom.hom p.left.hom.hom
    (congrArg (fun f : A ⟶ A ↦ f.left.hom.hom) h₁)
  have pt : Module.Projective R A.right := Module.Projective.of_split i.right.hom.hom p.right.hom.hom
    (congrArg (fun f : A ⟶ A ↦ f.right.hom.hom) h₁)
  exact ⟨⟨A.left,A.right,ps,pt,A.hom⟩,⟨i,p,h₁⟩,h₂⟩

include k in
/-- Every endomorphism of a two-term projective complex has a Fitting
idempotent that splits through an actual two-term projective complex. -/
theorem exists_fitting_retract (W : TwoTerm R) (a : End W.homotopyObject) :
    ∃ (N : TwoTerm R) (r : Retract N.homotopyObject W.homotopyObject) (c : End W.homotopyObject)
      (m : ℕ), (a ^ m : End W.homotopyObject) ≫ r.r = 0 ∧ c ≫ a = a ≫ c ∧ r.r ≫ r.i + c ≫ a = 𝟙 _ := by
  let H := realize (R := R)
  obtain ⟨v,hv⟩ := H.map_surjective (show H.obj W.asArrow ⟶ H.obj W.asArrow from a)
  let z : End W.asArrow := v
  have (X Y : FGModuleCat.{u} R) : Module.Finite k (X ⟶ Y) := finiteModuleHom_isFinite k X Y
  have : Module.Finite k (End W.asArrow) := Module.Finite.of_injective
    (ArrowHom.pairLinear k W.asArrow W.asArrow) (ArrowHom.pairAddHom_injective _ _)
  obtain ⟨e,c,m,he,hz,hcomm,hid⟩ := exists_fitting_idempotent k z
  obtain ⟨N,r,hr⟩ := split_strict_idempotent W e he
  have hkill : (z ^ m : End W.asArrow) ≫ r.r = 0 := by
    have h : (z ^ m : End W.asArrow) ≫ r.r ≫ r.i = 0 := by rw [hr]; exact hz
    have hh := congrArg (fun f ↦ f ≫ r.r) h
    simpa [Category.assoc,r.retract] using hh
  let φ := H.mapEnd W.asArrow
  have ha : φ z = a := hv
  rw [← ha]
  refine ⟨N,r.map H,φ c,m,?_,?_,?_⟩
  · change ((φ z)^m : End (H.obj W.asArrow)) ≫ H.map r.r = 0
    rw [← map_pow φ z m]
    exact (H.map_comp _ _).symm.trans ((congrArg H.map hkill).trans (H.map_zero _ _))
  · exact (H.map_comp _ _).symm.trans ((congrArg H.map hcomm.symm).trans (H.map_comp _ _))
  · have ht := congrArg H.map (show r.r ≫ r.i + c ≫ z = 𝟙 W.asArrow by rw [hr]; exact hid)
    change H.map r.r ≫ H.map r.i + H.map c ≫ H.map z = 𝟙 (H.obj W.asArrow)
    simpa only [H.map_add,H.map_comp,H.map_id] using ht

include k in
/-- Every homotopy idempotent splits through a two-term projective representative. -/
theorem split_homotopy_idempotent (W : TwoTerm R) (e : End W.homotopyObject)
    (he : IsIdempotentElem e) :
    ∃ (N : TwoTerm R) (r : Retract N.homotopyObject W.homotopyObject), r.r ≫ r.i = e := by
  let a : End W.homotopyObject := 1 - e
  have ha : IsIdempotentElem a := he.one_sub
  obtain ⟨N,r,c,m,hz,hc,ht⟩ := exists_fitting_retract k W a
  have hzero : a ≫ r.r = 0 := by
    rw [← ha.pow_succ_eq m, pow_succ]
    change (a ≫ (a ^ m : End W.homotopyObject)) ≫ r.r = 0
    simp [Category.assoc, hz]
  have haa : a ≫ a = a := ha
  have h := congrArg (fun z : End W.homotopyObject ↦ a ≫ z) ht
  change a ≫ (r.r ≫ r.i + c ≫ a) = a ≫ 𝟙 _ at h
  rw [Preadditive.comp_add, ← Category.assoc, hzero, zero_comp, zero_add, ← Category.assoc,
    ← hc, Category.assoc, haa, Category.comp_id] at h
  refine ⟨N,r,?_⟩
  rw [h] at ht
  let q : End W.homotopyObject := r.r ≫ r.i
  change q + (1 - e) = 1 at ht
  change q = e
  exact add_right_cancel (ht.trans (show 1 = e + (1 - e) by abel))

include k in
/-- The two-term projective representatives are closed under ambient retracts
up to homotopy isomorphism. -/
theorem exists_twoTerm_iso_of_retract (W : TwoTerm R) {L}
    (s : Retract L W.homotopyObject) : ∃ N : TwoTerm R, Nonempty (L ≅ N.homotopyObject) := by
  let e : End W.homotopyObject := s.r ≫ s.i
  have he : IsIdempotentElem e := by
    change (s.r ≫ s.i) ≫ s.r ≫ s.i = s.r ≫ s.i
    simp [Category.assoc, s.retract_assoc]
  obtain ⟨N,r,hr⟩ := split_homotopy_idempotent k W e he
  refine ⟨N, ⟨⟨s.i ≫ r.r, r.i ≫ s.r, ?_, ?_⟩⟩⟩
  · simp only [Category.assoc]
    rw [← Category.assoc r.r, hr]
    simp [e, Category.assoc, s.retract]
  · simp only [Category.assoc]
    rw [← Category.assoc s.r, ← show r.r ≫ r.i = s.r ≫ s.i from hr]
    simp [Category.assoc, r.retract]

/-- Endomorphisms modulo homotopy form a finite-dimensional vector space. -/
theorem finite_homotopy_end (W : TwoTerm R) : Module.Finite k (End W.homotopyObject) := by
  let D := W.toCochainComplex
  have (M N : FGModuleCat.{u} R) : Module.Finite k (M ⟶ N) := finiteModuleHom_isFinite k M N
  let ev (j : ℤ) : End D →ₗ[k] (D.X j ⟶ D.X j) :=
    { toFun := fun f ↦ f.f j, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have : Module.Finite k (D ⟶ D) := Module.Finite.of_injective ((ev (-1)).prod (ev 0))
    (fun _ _ h ↦ from_double_hom_ext (hi₀₁ := adjacent) (congrArg Prod.fst h) (congrArg Prod.snd h))
  let F := HomotopyCategory.quotient (FGModuleCat.{u} R) (ComplexShape.up ℤ)
  exact Module.Finite.of_surjective (F.mapLinearMap k (X := D) (Y := D)) F.map_surjective

section
variable {C : Type*} [Category* C] [Preadditive C] [Linear k C]

private noncomputable def cornerMap {L W : C} (r : Retract L W) :
    (L ⟶ L) →ₗ[k] (W ⟶ W) :=
  (Linear.rightComp k W r.i).comp (Linear.leftComp k L r.r)

private theorem corner_injective {L W : C} (r : Retract L W) :
    Function.Injective (cornerMap k r) := by
  intro x y h
  have hh := congrArg (fun z ↦ r.i ≫ z ≫ r.r) h
  simpa [cornerMap, Category.assoc, r.retract, r.retract_assoc] using hh

theorem corner_rank_lt {L W : C} [Module.Finite k (W ⟶ W)] (r : Retract L W)
    (h : r.r ≫ r.i ≠ 𝟙 W) : Module.finrank k (L ⟶ L) < Module.finrank k (W ⟶ W) := by
  have hi := corner_injective k r
  have := Module.Finite.of_injective _ hi
  apply lt_of_le_of_ne (LinearMap.finrank_le_finrank_of_injective hi)
  intro heq
  obtain ⟨x,hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hi (𝟙 W)
  change (r.r ≫ x) ≫ r.i = 𝟙 W at hx
  apply h
  calc
    r.r ≫ r.i = ((r.r ≫ x) ≫ r.i) ≫ r.r ≫ r.i := by rw [hx, Category.id_comp]
    _ = 𝟙 W := by simpa [Category.assoc, r.retract_assoc] using hx

private theorem proper_of_disjoint {A B W : C} (r : Retract A W) (s : Retract B W)
    (hs : ¬ IsZero B) (h : s.i ≫ r.r = 0) : r.r ≫ r.i ≠ 𝟙 W := by
  intro he
  apply hs
  apply (IsZero.iff_id_eq_zero _).2
  calc
    𝟙 B = s.i ≫ (r.r ≫ r.i) ≫ s.r := by rw [he, Category.id_comp, s.retract]
    _ = 0 := by simp [← Category.assoc, h]

private theorem exists_indecomposable_retract_aux [HasBinaryBiproducts C]
    (W U : C) [Module.Finite k (W ⟶ W)] (hout : ¬ IsInAdd W U) :
    ∃ D : C, Indecomposable D ∧ Nonempty (Retract D W) ∧ ¬ IsInAdd D U := by
  classical
  generalize hn : Module.finrank k (W ⟶ W) = n
  induction n using Nat.strong_induction_on generalizing W with
  | h n ih =>
    by_cases hd : Indecomposable W
    · exact ⟨W,hd,⟨.refl W⟩,hout⟩
    have hnz : ¬ IsZero W := fun hz ↦ hout ⟨[],hz.eq_of_src _ _⟩
    have hs : ¬ ∀ A B : C, (W ≅ A ⊞ B) → IsZero A ∨ IsZero B := fun hh ↦ hd ⟨hnz,hh⟩
    push Not at hs
    obtain ⟨A,B,e,ha,hb⟩ := hs
    let r : Retract A W := ⟨biprod.inl ≫ e.inv,e.hom ≫ biprod.fst,by simp⟩
    let s : Retract B W := ⟨biprod.inr ≫ e.inv,e.hom ≫ biprod.snd,by simp⟩
    have descend {L : C} (t : Retract L W) (ht : t.r ≫ t.i ≠ 𝟙 W) (ho : ¬ IsInAdd L U) :
        ∃ D : C, Indecomposable D ∧ Nonempty (Retract D W) ∧ ¬ IsInAdd D U := by
      have := Module.Finite.of_injective _ (corner_injective k t)
      obtain ⟨D,hD,⟨v⟩,hDU⟩ := ih _ (hn ▸ corner_rank_lt k t ht) L ho rfl
      exact ⟨D,hD,⟨v.trans t⟩,hDU⟩
    by_cases hA : IsInAdd A U
    · apply descend s (proper_of_disjoint s r ha (by simp [r,s]))
      intro hB
      apply hout
      apply IsInAdd.of_total hA hB r.r r.i s.r s.i
      simpa only [r,s,Category.assoc,Preadditive.comp_add,Preadditive.add_comp,Category.id_comp,Iso.hom_inv_id] using
        congrArg (fun z ↦ e.hom ≫ z ≫ e.inv) (biprod.total (X := A) (Y := B))
    · exact descend r (proper_of_disjoint r s hb (by simp [r,s])) hA

end

include k in
/-- A complex outside add(U) has an indecomposable two-term retract outside add(U). -/
theorem exists_indecomposable_outside_add (W U : TwoTerm R)
    (hout : ¬ IsInAdd W.homotopyObject U.homotopyObject) :
    ∃ V : TwoTerm R, Indecomposable V.homotopyObject ∧
      Nonempty (Retract V.homotopyObject W.homotopyObject) ∧
      ¬ IsInAdd V.homotopyObject U.homotopyObject := by
  have : Module.Finite k (W.homotopyObject ⟶ W.homotopyObject) := finite_homotopy_end k W
  obtain ⟨D,hd,⟨r⟩,ho⟩ := exists_indecomposable_retract_aux k _ _ hout
  obtain ⟨V,⟨e⟩⟩ := exists_twoTerm_iso_of_retract k W r
  exact ⟨V,⟨fun hz ↦ hd.1 (hz.of_iso e),fun A B j ↦ hd.2 A B (e ≪≫ j)⟩,
    ⟨e.symm.retract.trans r⟩,fun h ↦ ho ((IsInAdd.of_retraction _ _ e.hom_inv_id).trans h)⟩

include k in
/-- An indecomposable two-term complex has no nontrivial homotopy idempotents. -/
theorem homotopy_idempotent_zero_or_one (W : TwoTerm R) (hW : Indecomposable W.homotopyObject)
    (e : End W.homotopyObject) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  obtain ⟨A,r,hr⟩ := split_homotopy_idempotent k W e he
  obtain ⟨B,s,hs⟩ := split_homotopy_idempotent k W (1-e) he.one_sub
  have hcross {X Y : TwoTerm R} (p : Retract X.homotopyObject W.homotopyObject)
      (q : Retract Y.homotopyObject W.homotopyObject) (h : (p.r ≫ p.i) ≫ q.r ≫ q.i = 0) :
      p.i ≫ q.r = 0 := by
    have hh := congrArg (fun z ↦ p.i ≫ z ≫ q.r) h
    simpa [Category.assoc, p.retract_assoc, q.retract] using hh
  have hrs : r.i ≫ s.r = 0 := hcross r s (by
    rw [hr,hs]; change (1-e)*e = 0; rw [sub_mul, one_mul, he, sub_self])
  have hsr : s.i ≫ r.r = 0 := hcross s r (by
    rw [hs,hr]; change e*(1-e) = 0; rw [mul_sub, mul_one, he, sub_self])
  let i : W.homotopyObject ≅ A.homotopyObject ⊞ B.homotopyObject :=
    ⟨biprod.lift r.r s.r, biprod.desc r.i s.i, by
      rw [biprod.lift_desc,hr,hs]; change e + (1-e) = 1; abel, by
      ext <;> simp [Category.assoc, r.retract, s.retract, hrs, hsr]⟩
  rcases hW.2 _ _ i with hz | hz
  · left
    rw [← hr,hz.eq_of_src r.i 0,comp_zero]
  · right
    have h : 1 - e = 0 := hs.symm.trans (by rw [hz.eq_of_src s.i 0,comp_zero])
    exact (sub_eq_zero.mp h).symm

include k in
/-- The endomorphism ring of an indecomposable two-term complex is local. -/
theorem isLocalRing_homotopy_end (W : TwoTerm R) (hW : Indecomposable W.homotopyObject) :
    IsLocalRing (End W.homotopyObject) := by
  have : Nontrivial (End W.homotopyObject) := nontrivial_of_ne 0 1
    (fun h ↦ hW.1 ((IsZero.iff_id_eq_zero _).2 h.symm))
  have := finite_homotopy_end k W
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  obtain ⟨e,c,m,he,hz,hc,ht⟩ := exists_fitting_idempotent k a
  rcases homotopy_idempotent_zero_or_one k W hW e he with rfl | rfl
  · rw [zero_add] at ht
    exact Or.inl ⟨⟨a,c,ht,hc.trans ht⟩,rfl⟩
  · rw [one_mul] at hz
    exact Or.inr (IsNilpotent.isUnit_one_sub ⟨m,hz⟩)

end EFiniteCharacterizations.TwoTerm
