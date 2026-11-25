module

public import EFiniteCharacterizations.LargeModules.EndofiniteInterpolation
public import EFiniteCharacterizations.Modules.PrimitiveSummand
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Idempotents

/-! # Endomorphisms of an indecomposable endofinite module -/

@[expose] public section

namespace EFiniteCharacterizations

variable {R : Type*} [Ring R] {N : ModuleCat R}

namespace EndofiniteLayers

variable (s : CompositionSeries (Submodule (Module.End R N) N))

private abbrev lower (i : Fin s.length) : Submodule (Module.End R N) (s i.succ) := (s i.castSucc).comap (s i.succ).subtype
private abbrev Layer (i : Fin s.length) := (s i.succ) ⧸ lower s i
private abbrev Layers := (i : Fin s.length) → Layer s i

private instance : Module (Module.End R N) (Layers s) := Pi.module _ _ _

private instance (i : Fin s.length) : IsSimpleModule (Module.End R N) (Layer s i) :=
  (covBy_iff_quot_is_simple (s.step i).le).mp (s.step i)

private abbrev action := Module.toModuleEnd (Module.End (Module.End R N) (Layers s)) (S := (Module.End R N)) (Layers s)

private noncomputable def representative (i : Fin s.length) (v : Layer s i) : s i.succ :=
  ((lower s i).mkQ_surjective v).choose

private theorem mk_representative (i : Fin s.length) (v : Layer s i) :
    (lower s i).mkQ (representative s i v) = v :=
  ((lower s i).mkQ_surjective v).choose_spec

/-- Jacobson density on the semisimple layers prescribes any finite family of
values. Algebraic compactness realizes them all simultaneously. -/
private theorem action_surjective (hN : IsEndofinite N) : Function.Surjective (action s) := by
  classical
  intro f
  let J := Layers s × Fin s.length
  let x (j : J) := representative s j.2 (j.1 j.2)
  let y (j : J) := representative s j.2 (f j.1 j.2)
  have test (j : J) (e : (Module.End R N)) :
      e (x j).val - (y j).val ∈ s j.2.castSucc ↔ e • j.1 j.2 = f j.1 j.2 := by
    change (e • x j - y j) ∈ lower s j.2 ↔ _
    rw [← Submodule.Quotient.mk_eq_zero, ← (lower s j.2).mkQ_apply, map_sub, sub_eq_zero,
      map_smul]
    simp only [x,y,mk_representative]
  obtain ⟨e,he⟩ := hN.exists_endomorphism_of_finite_congruences
    (fun j : J ↦ (x j).val) (fun j ↦ (y j).val) (fun j ↦ s j.2.castSucc) (by
      intro t
      obtain ⟨a,ha⟩ := jacobson_density (R := Module.End R N) (M := Layers s) f (t.image Prod.fst)
      exact ⟨a,fun j hj ↦ (test j a).2 (congrFun (ha j.1 (Finset.mem_image_of_mem _ hj)).symm j.2)⟩)
  exact ⟨e,LinearMap.ext fun v ↦ funext fun i ↦ (test (v,i) e).1 (he (v,i))⟩

private theorem action_ker_nil (h₀ : s.head = ⊥) (h₁ : s.last = ⊤)
    (e : (Module.End R N)) (he : e ∈ RingHom.ker (action s)) : IsNilpotent e := by
  classical
  have lower_step (i : Fin s.length) (z : N) (hz : z ∈ s i.succ) :
      e z ∈ s i.castSucc := by
    let t : Layers s := Pi.single i ((lower s i).mkQ ⟨z,hz⟩)
    have h := congrFun (LinearMap.congr_fun (RingHom.mem_ker.mp he) t) i
    change e • t i = 0 at h
    rw [show t i = (lower s i).mkQ ⟨z,hz⟩ from Pi.single_eq_same .., ← map_smul] at h
    exact (Submodule.Quotient.mk_eq_zero (lower s i)).mp h
  have dies (i : Fin (s.length+1)) (z : N) (hz : z ∈ s i) : (e ^ i.val) z = 0 := by
    induction i using Fin.induction generalizing z with
    | zero =>
      change z ∈ s.head at hz
      simpa [h₀] using hz
    | succ i ih =>
      rw [Fin.val_succ, pow_succ]
      exact ih _ (lower_step i z hz)
  refine ⟨s.length,LinearMap.ext fun z ↦ dies (Fin.last _) z ?_⟩
  change z ∈ s.last
  simp [h₁]

open CategoryTheory CategoryTheory.Limits

private theorem trivial_idempotents (hi : Indecomposable N) (e : Module.End R N)
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  let A := ModuleCat.of R (LinearMap.range e)
  let B := ModuleCat.of R (LinearMap.ker e)
  let dec : N ≅ A ⊞ B := (Submodule.prodEquivOfIsCompl _ _ (LinearMap.IsIdempotentElem.isCompl he)).symm.toModuleIso ≪≫
    (ModuleCat.biprodIsoProd A B).symm
  rcases hi.2 A B dec with ha | hb
  · let : Subsingleton (LinearMap.range e) := ModuleCat.isZero_iff_subsingleton.mp ha
    exact Or.inl (LinearMap.ext fun z ↦ congrArg Subtype.val
      (Subsingleton.elim (e.rangeRestrict z) 0))
  · let : Subsingleton (LinearMap.ker e) := ModuleCat.isZero_iff_subsingleton.mp hb
    right
    ext z
    apply sub_eq_zero.mp
    have h : e z - z ∈ LinearMap.ker e := by
      change e (e z - z) = 0
      rw [map_sub, ← Module.End.mul_apply, he.eq, sub_self]
    exact congrArg Subtype.val (Subsingleton.elim (⟨_,h⟩ : LinearMap.ker e) 0)

private theorem isUnit_or_zero_of_trivial_projections {D M : Type*} [Ring D] [AddCommGroup M]
    [Module D M] [IsSemisimpleModule D M]
    (ht : ∀ p : Module.End D M, IsIdempotentElem p → p = 0 ∨ p = 1)
    (f : Module.End D M) : IsUnit f ∨ f = 0 := by
  cases subsingleton_or_nontrivial M with
  | inl h => exact Or.inr (Subsingleton.elim ..)
  | inr h =>
    let : IsSimpleModule D M := (isSimpleModule_iff D M).2 (by
      constructor
      intro U
      obtain ⟨V,hc⟩ := exists_isCompl U
      have hr := Submodule.range_projection hc
      rcases ht _ (Submodule.isIdempotentElem_projection hc) with hz | ho
      · exact Or.inl (by simpa [hz] using hr.symm)
      · exact Or.inr (by rw [ho] at hr; exact hr.symm.trans LinearMap.range_id))
    exact f.bijective_or_eq_zero.imp (Module.End.isUnit_iff _).2 id

private theorem unit_of_unit_image {A B : Type*} [Ring A] [Ring B] (p : A →+* B)
    (hs : Function.Surjective p) (hk : ∀ x ∈ RingHom.ker p, IsNilpotent x)
    (a : A) (h : IsUnit (p a)) : IsUnit a := by
  obtain ⟨v,h₁,h₂⟩ := isUnit_iff_exists.mp h
  obtain ⟨b,rfl⟩ := hs v
  have unitAtOne (x : A) (hx : p x = 1) : IsUnit x := by
    have hn := hk (1-x) (RingHom.mem_ker.mpr (by simp [hx]))
    simpa using hn.isUnit_one_sub
  obtain ⟨c,hc,_⟩ := isUnit_iff_exists.mp (unitAtOne (a*b) (by simpa using h₁))
  obtain ⟨d,_,hd⟩ := isUnit_iff_exists.mp (unitAtOne (b*a) (by simpa using h₂))
  exact isUnit_iff_exists_and_exists.mpr
    ⟨⟨b*c,by rwa [← mul_assoc]⟩,⟨d*b,by rwa [mul_assoc]⟩⟩

private theorem local_of_layer_action {A D M : Type*} [Ring A] [Nontrivial A] [Ring D]
    [AddCommGroup M] [Module D M] [IsSemisimpleModule D M]
    (p : A →+* Module.End D M) (hs : Function.Surjective p)
    (hk : ∀ x ∈ RingHom.ker p, IsNilpotent x)
    (hi : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing A := by
  have ht (q : Module.End D M) (hq : IsIdempotentElem q) : q = 0 ∨ q = 1 := by
    obtain ⟨e,he,rfl⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent p hk q (hs q) hq
    rcases hi e he with rfl | rfl
    · exact Or.inl (map_zero p)
    · exact Or.inr (map_one p)
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  rcases isUnit_or_zero_of_trivial_projections ht (p a) with hu | hz
  · exact Or.inl (unit_of_unit_image p hs hk a hu)
  · exact Or.inr ((hk a (RingHom.mem_ker.mpr hz)).isUnit_one_sub)

private theorem exists_detecting_layer (h₀ : s.head = ⊥) (h₁ : s.last = ⊤) (x : N) (hx : x ≠ 0) :
    ∃ v : Layers s, v ≠ 0 ∧ ∀ e : Module.End R N, e x = 0 → action s e v = 0 := by
  classical
  have first (j : Fin (s.length + 1)) (hj : x ∈ s j) :
      ∃ i : Fin s.length, x ∈ s i.succ ∧ x ∉ s i.castSucc := by
    induction j using Fin.induction with
    | zero =>
      change x ∈ s.head at hj
      exact (hx ((Submodule.mem_bot _).mp (h₀ ▸ hj))).elim
    | succ i ih =>
      by_cases h : x ∈ s i.castSucc
      · exact ih h
      · exact ⟨i,hj,h⟩
  obtain ⟨i,hi,hn⟩ := first (Fin.last _) (show x ∈ s.last by simp [h₁])
  let u : Layer s i := (lower s i).mkQ ⟨x,hi⟩
  have hu : u ≠ 0 := fun h ↦ hn ((Submodule.Quotient.mk_eq_zero (lower s i)).mp h)
  refine ⟨Pi.single i u,fun h ↦ hu (by simpa using congrFun h i),fun e he ↦ ?_⟩
  funext j
  change e • (Pi.single i u j) = 0
  by_cases h : j = i
  · subst j
    rw [Pi.single_eq_same]
    change e • (lower s i).mkQ _ = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero (lower s i)).mpr (show e x ∈ s i.castSucc by simp [he])
  · simp [Pi.single_eq_of_ne h]

end EndofiniteLayers

open EndofiniteLayers CategoryTheory CategoryTheory.Limits in
/-- The endomorphism ring of an indecomposable endofinite module is local. -/
theorem IsEndofinite.isLocalRing_end (hN : IsEndofinite N) (hi : Indecomposable N) :
    IsLocalRing (Module.End R N) := by
  classical
  let : Nontrivial N := not_subsingleton_iff_nontrivial.mp (hi.1 ∘ ModuleCat.isZero_iff_subsingleton.2)
  obtain ⟨s,h₀,h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp hN
  let D := Module.End (Module.End R N) (Layers s)
  let : IsSemisimpleRing D := IsSemisimpleRing.moduleEnd (Module.End R N) (Layers s)
  exact local_of_layer_action (D := D) (M := Layers s) (action s)
    (action_surjective s hN) (action_ker_nil s h₀ h₁) (trivial_idempotents hi)

open EndofiniteLayers CategoryTheory CategoryTheory.Limits in
/-- Every nonzero vector in an endofinite module has a nonzero projection
to an indecomposable direct summand. -/
theorem IsEndofinite.exists_indecomposable_retract (hN : IsEndofinite N) (x : N) (hx : x ≠ 0) :
    ∃ (G : ModuleCat R) (r : Retract G N), Indecomposable G ∧ r.r.hom x ≠ 0 := by
  obtain ⟨s,h₀,h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp hN
  let : IsSemisimpleRing (Module.End (Module.End R N) (Layers s)) := IsSemisimpleRing.moduleEnd (Module.End R N) (Layers s)
  apply (exists_detecting_layer s h₀ h₁ x hx).elim
  intro v h
  refine PrimitiveSummand.exists_retract_detecting (R := R) (N := N) (D := Module.End (Module.End R N) (Layers s)) (T := Layers s)
    (action s) ?_ ?_ x v ?_ ?_
  · exact action_surjective s hN
  · exact action_ker_nil s h₀ h₁
  · exact h.1
  · exact h.2

end EFiniteCharacterizations
