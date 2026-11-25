module

public import EFiniteCharacterizations.Presentations.ProjectiveHomWeight
public import EFiniteCharacterizations.Modules.CompositionLength
public import Mathlib.Data.Set.Finite.List

/-! # Composition factors and bounded Grothendieck classes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u v

namespace EFiniteCharacterizations

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem exists_proper_subobject {X : C} (hX : ¬ IsZero X) (hs : ¬ Simple X) :
    ∃ (Y : C) (f : Y ⟶ X), Mono f ∧ ¬ IsZero Y ∧ ¬ IsIso f := by
  classical
  by_contra hn
  apply hs
  constructor
  intro Y f _
  constructor
  · intro hi hz
    apply hX
    apply (IsZero.iff_id_eq_zero X).mpr
    calc
      𝟙 X = inv f ≫ f := (IsIso.inv_hom_id f).symm
      _ = inv f ≫ (0 : Y ⟶ X) := congrArg (fun g ↦ inv f ≫ g) hz
      _ = 0 := comp_zero
  · intro hne
    by_contra hi
    have hY : ¬ IsZero Y := fun h ↦ hne (h.eq_of_src _ _)
    exact hn ⟨Y, f, inferInstance, hY, hi⟩

end Abelian

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]
  [Module.Finite k R] [IsNoetherianRing R]

private noncomputable abbrev dim (M : FGModuleCat.{u} R) : ℕ := Module.finrank k (M.obj : Type u)

private theorem exists_composition_factors (M : FGModuleCat.{u} R) :
    ∃ L : List (FGModuleCat.{u} R), (∀ X ∈ L, Simple X) ∧ (L.map GrothendieckGroup.of).sum = GrothendieckGroup.of M ∧
      L.length ≤ dim k M ∧ ∀ (Y : FGModuleCat.{u} R) [Simple Y] (f : M ⟶ Y), f ≠ 0 →
        ∃ X ∈ L, Nonempty (X ≅ Y) := by
  classical
  generalize hn : dim k M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
    by_cases hz : IsZero M
    · refine ⟨[], by simp, (GrothendieckGroup.of_isZero hz).symm, by simp, ?_⟩
      intro Y _ f hf
      exact (hf (hz.eq_of_src _ _)).elim
    by_cases hs : Simple M
    · have hpos := dimensionWeight_pos k M hz
      rw [dimensionWeight_eval, Int.natCast_pos] at hpos
      refine ⟨[M], by simpa, by simp, ?_, ?_⟩
      · exact Nat.succ_le_iff.mpr (hn ▸ hpos)
      · intro Y hY f hf
        have : IsIso f := Weight.isIso_of_nonzero
          ((Weight.isStable_zero_iff_simple M).mpr hs) ((Weight.isStable_zero_iff_simple Y).mpr hY) f hf
        exact ⟨M, by simp, ⟨asIso f⟩⟩
    obtain ⟨A, i, hm, hA, hi⟩ := exists_proper_subobject hz hs
    let Q := cokernel i
    have hQ : ¬ IsZero Q := by
      intro hz'
      have : Epi i := Abelian.epi_of_cokernel_π_eq_zero i (hz'.eq_of_tgt _ _)
      exact hi (isIso_of_mono_of_epi i)
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel i)
      (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
    have hd : dim k M = dim k A + dim k Q := by
      have hd := (dimensionWeight (R := R) k).eval_shortExact S hS
      change (dimensionWeight (R := R) k).eval M =
        (dimensionWeight (R := R) k).eval A + (dimensionWeight (R := R) k).eval Q at hd
      simp only [dimensionWeight_eval] at hd
      exact_mod_cast hd
    have hdim (X : FGModuleCat.{u} R) (hX : ¬ IsZero X) : 0 < dim k X := by
      have h := dimensionWeight_pos k X hX
      rwa [dimensionWeight_eval, Int.natCast_pos] at h
    obtain ⟨L, hLs, hLclass, hLlen, hLquot⟩ :=
      ih (dim k A) (by have := hdim Q hQ; omega) A rfl
    obtain ⟨T, hTs, hTclass, hTlen, hTquot⟩ :=
      ih (dim k Q) (by have := hdim A hA; omega) Q rfl
    refine ⟨L ++ T, ?_, ?_, ?_, ?_⟩
    · intro X hx
      exact (List.mem_append.mp hx).elim (hLs X) (hTs X)
    · rw [List.map_append, List.sum_append, hLclass, hTclass]
      exact (GrothendieckGroup.of_shortExact S hS).symm
    · rw [List.length_append, ← hn, hd]
      exact Nat.add_le_add hLlen hTlen
    · intro Y _ f hf
      by_cases hif : i ≫ f = 0
      · have hq : cokernel.desc i f hif ≠ 0 := by
          intro hg
          apply hf
          rw [← cokernel.π_desc i f hif, hg, comp_zero]
        obtain ⟨X, hX, e⟩ := hTquot Y (cokernel.desc i f hif) hq
        exact ⟨X, List.mem_append_right _ hX, e⟩
      · obtain ⟨X, hX, e⟩ := hLquot Y (i ≫ f) hif
        exact ⟨X, List.mem_append_left _ hX, e⟩

omit [IsNoetherianRing R] in
private theorem exists_for_regular_simple (Y : FGModuleCat.{u} R) [Simple Y] :
    ∃ f : FGModuleCat.of R R ⟶ Y, f ≠ 0 := by
  have hY : Nontrivial (Y.obj : Type u) :=
    not_subsingleton_iff_nontrivial.mp (Simple.not_isZero Y ∘ (FGModuleCat.isZero_iff_subsingleton Y).2)
  obtain ⟨y, hy⟩ := exists_ne (0 : (Y.obj : Type u))
  let f := LinearMap.toSpanSingleton R (Y.obj : Type u) y
  refine ⟨ObjectProperty.homMk (ModuleCat.ofHom f), ?_⟩
  intro hz
  apply hy
  have hg := congrArg (fun g : FGModuleCat.of R R ⟶ Y ↦ g.hom.hom 1) hz
  simpa [f] using hg

noncomputable def regularGroundDimension : ℕ :=
  (fun M : FGModuleCat.{u} R ↦ Module.finrank k (M.obj : Type u)) (FGModuleCat.of R R)

/-- Each simple factor is a quotient of the regular module, so composition
length controls ground dimension uniformly. -/
theorem groundFinrank_le_regular_mul_length [IsArtinianRing R] (M : FGModuleCat.{u} R) :
    Module.finrank k (M.obj : Type u) ≤ regularGroundDimension (R := R) k * FGModuleCat.moduleLength M := by
  let w := (regularGroundDimension (R := R) k : ℤ) • FGModuleCat.lengthWeight R - dimensionWeight (R := R) k
  have eval (X : FGModuleCat.{u} R) : w.eval X =
      (regularGroundDimension (R := R) k : ℤ) * FGModuleCat.moduleLength X - Module.finrank k (X.obj : Type u) := by
    change (regularGroundDimension (R := R) k : ℤ) • (FGModuleCat.lengthWeight R).eval X - (dimensionWeight (R := R) k).eval X = _
    simp
  have hsimple (X : FGModuleCat.{u} R) (hX : Simple X) : 0 ≤ w.eval X := by
    obtain ⟨p, hp⟩ := exists_for_regular_simple X
    have := epi_of_nonzero_to_simple hp
    have hd : Module.finrank k (X.obj : Type u) ≤ regularGroundDimension (R := R) k := groundFinrank_le_of_epi k p
    have hl : 1 ≤ FGModuleCat.moduleLength X := Nat.pos_of_ne_zero
      (mt (FGModuleCat.moduleLength_eq_zero_iff_isZero X).mp (Simple.not_isZero X))
    rw [eval, sub_nonneg]
    exact_mod_cast hd.trans ((Nat.mul_one _).symm.trans_le (Nat.mul_le_mul_left _ hl))
  obtain ⟨L, hs, he, _, _⟩ := exists_composition_factors k M
  have hn : 0 ≤ (L.map (fun X ↦ w.eval X)).sum :=
    List.sum_nonneg (by intro a ha; obtain ⟨X, hX, rfl⟩ := List.mem_map.mp ha; exact hsimple X (hs X hX))
  have hw := congrArg w he
  simp only [map_list_sum, List.map_map] at hw
  change (L.map (fun X ↦ w.eval X)).sum = w.eval M at hw
  rw [hw, eval, sub_nonneg] at hn
  exact_mod_cast hn

/-- The isomorphism classes of simple finite modules. -/
def simpleIsomorphismClasses (R : Type u) [Ring R] : Set (Skeleton (FGModuleCat.{u} R)) :=
  {x | ∃ M : FGModuleCat.{u} R, toSkeleton M = x ∧ Simple M}

include k in
theorem finite_simpleIsomorphismClasses : (simpleIsomorphismClasses R).Finite := by
  obtain ⟨L, _, _, _, hL⟩ := exists_composition_factors k (FGModuleCat.of R R)
  refine (L.map toSkeleton).finite_toSet.subset ?_
  rintro x ⟨M, rfl, hM⟩
  obtain ⟨f, hf⟩ := exists_for_regular_simple M
  obtain ⟨X, hX, ⟨e⟩⟩ := hL M f hf
  exact List.mem_map.mpr ⟨X, hX, congr_toSkeleton_of_iso e⟩

include k in
theorem simpleIsomorphismClasses_nonempty_of_not_isZero {M : FGModuleCat.{u} R}
    (hM : ¬ IsZero M) : (simpleIsomorphismClasses R).Nonempty := by
  obtain ⟨L, hL, hsum, _, _⟩ := exists_composition_factors k M
  cases L with
  | nil =>
    have hz : GrothendieckGroup.of M = 0 := by simpa using hsum.symm
    have hpos := dimensionWeight_pos k M hM
    simp [Weight.eval, hz] at hpos
  | cons X L => exact ⟨toSkeleton X, X, rfl, hL X List.mem_cons_self⟩

include k in
/-- Every ambient class is an integral combination of the simple classes. -/
theorem exists_simple_class_coefficients [Fintype ↥(simpleIsomorphismClasses R)]
    (z : GrothendieckGroup (FGModuleCat.{u} R)) :
    ∃ c : simpleIsomorphismClasses R → ℤ, z = ∑ i, c i • GrothendieckGroup.of ((fromSkeleton _).obj i.val) := by
  classical
  let I := ↥(simpleIsomorphismClasses R)
  let v (i : I) := GrothendieckGroup.of ((fromSkeleton _).obj i.val)
  let P (x : GrothendieckGroup (FGModuleCat.{u} R)) := ∃ c : I → ℤ, x = ∑ i, c i • v i
  have hz : P 0 := ⟨0, by simp⟩
  have hadd {x y} : P x → P y → P (x + y) := by
    rintro ⟨c, rfl⟩ ⟨d, rfl⟩
    exact ⟨fun i ↦ c i + d i, by simp [add_smul, Finset.sum_add_distrib]⟩
  have hs (X : FGModuleCat.{u} R) (hX : Simple X) : P (GrothendieckGroup.of X) := by
    let j : I := ⟨toSkeleton X, X, rfl, hX⟩
    refine ⟨fun i ↦ if i = j then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)]
    simpa [v, j] using (GrothendieckGroup.of_eq_of_iso (fromSkeletonToSkeletonIso X)).symm
  have hM (M : FGModuleCat.{u} R) : P (GrothendieckGroup.of M) := by
    obtain ⟨L, hL, he, hlen, hquot⟩ := exists_composition_factors k M
    rw [← he]
    clear he hlen hquot
    induction L with
    | nil => exact hz
    | cons X L ih => exact hadd (hs X (hL X List.mem_cons_self)) (ih fun Y hy ↦ hL Y (List.mem_cons_of_mem _ hy))
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ z
  change P (QuotientAddGroup.mk' _ a)
  induction a using FreeAbelianGroup.induction_on with
  | zero => simpa using hz
  | of X => exact hM X
  | neg X ih =>
    obtain ⟨c, hc⟩ := ih
    rw [map_neg, hc]
    exact ⟨fun i ↦ -c i, by simp [Finset.sum_neg_distrib]⟩
  | add a b ha hb => rw [map_add]; exact hadd ha hb

/-- Composition multiplicities are natural coefficients bounded by ground dimension. -/
theorem exists_simple_multiplicities [Fintype ↥(simpleIsomorphismClasses R)] (M : FGModuleCat.{u} R) :
    ∃ a : simpleIsomorphismClasses R → ℕ, (∀ i, a i ≤ Module.finrank k (M.obj : Type u)) ∧
      ∑ i, a i • GrothendieckGroup.of ((fromSkeleton _).obj i.val) = GrothendieckGroup.of M := by
  classical
  let I := ↥(simpleIsomorphismClasses R)
  let : BEq I := instBEqOfDecidableEq
  let v (i : I) := GrothendieckGroup.of ((fromSkeleton _).obj i.val)
  obtain ⟨L, hs, hsum, hlen, _⟩ := exists_composition_factors k M
  let t : List I := L.attach.map fun X ↦ ⟨toSkeleton X.val, X.val, rfl, hs _ X.property⟩
  refine ⟨fun i ↦ t.count i, fun i ↦ List.count_le_length.trans (by simpa [t] using hlen), ?_⟩
  change (∑ i, t.count i • v i) = _
  calc
    _ = ∑ i ∈ t.toFinset, t.count i • v i := (Finset.sum_subset (Finset.subset_univ _) (by
      intro i _ hi
      simp [List.count_eq_zero.mpr (by simpa using hi)])).symm
    _ = (t.map v).sum := (Finset.sum_list_map_count t v).symm
    _ = _ := by
      have hv (X : FGModuleCat.{u} R) :
          GrothendieckGroup.of ((fromSkeleton _).obj (toSkeleton X)) = GrothendieckGroup.of X :=
        GrothendieckGroup.of_eq_of_iso (fromSkeletonToSkeletonIso X)
      simp only [t, v, List.map_map, Function.comp_def, hv, List.map_subtype, List.unattach_attach]
      exact hsum

include k in
/-- Each simple multiplicity is bounded by the composition length, independently
of the dimensions of the simple modules over the ground field. -/
theorem exists_length_bounded_multiplicities [Fintype ↥(simpleIsomorphismClasses R)]
    (M : FGModuleCat.{u} R) :
    ∃ a : simpleIsomorphismClasses R → ℕ, (∀ i, a i ≤ FGModuleCat.moduleLength M) ∧
      ∑ i, a i • GrothendieckGroup.of ((fromSkeleton _).obj i.val) = GrothendieckGroup.of M := by
  classical
  let := IsArtinianRing.of_finite k R
  obtain ⟨a, _, he⟩ := exists_simple_multiplicities k M
  let S (i : simpleIsomorphismClasses R) := (fromSkeleton _).obj i.val
  have length_eq (X : FGModuleCat.{u} R) :
      FGModuleCat.lengthWeight R (GrothendieckGroup.of X) = (FGModuleCat.moduleLength X : ℤ) :=
    FGModuleCat.lengthWeight_eval X
  have hsum : ∑ i, a i * FGModuleCat.moduleLength (S i) = FGModuleCat.moduleLength M := by
    have hh := congrArg (FGModuleCat.lengthWeight R) he
    simp only [map_sum, map_nsmul, length_eq, nsmul_eq_mul] at hh
    exact_mod_cast hh
  refine ⟨a, fun i ↦ ?_, he⟩
  obtain ⟨X,hX,hs⟩ := i.property
  have hp : 0 < FGModuleCat.moduleLength (S i) := by
    change 0 < FGModuleCat.moduleLength ((fromSkeleton _).obj i.val)
    rw [← hX, FGModuleCat.moduleLength_eq_of_iso (fromSkeletonToSkeletonIso X)]
    exact Nat.pos_of_ne_zero fun hz ↦ Simple.not_isZero X ((FGModuleCat.moduleLength_eq_zero_iff_isZero X).1 hz)
  rw [← hsum]
  exact (Nat.le_mul_of_pos_right _ hp).trans (Finset.single_le_sum (f := fun j ↦ a j * FGModuleCat.moduleLength (S j)) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i))

/-- In dimension at most `d`, the ambient class is determined by a vector
of simple multiplicities with coordinates between zero and `d`. -/
theorem exists_bounded_class_cover (d : ℕ) :
    ∃ S : Finset (GrothendieckGroup (FGModuleCat.{u} R)),
      S.card ≤ (d + 1) ^ (simpleIsomorphismClasses R).ncard ∧
      ∀ M : FGModuleCat.{u} R, Module.finrank k (M.obj : Type u) ≤ d → GrothendieckGroup.of M ∈ S := by
  classical
  let I := ↥(simpleIsomorphismClasses R)
  let : Fintype I := (finite_simpleIsomorphismClasses (R := R) k).fintype
  let : BEq I := instBEqOfDecidableEq
  let v (i : I) := GrothendieckGroup.of ((fromSkeleton _).obj i.val)
  let eval (a : I → Fin (d + 1)) := ∑ i, (a i).val • v i
  refine ⟨Finset.univ.image eval, ?_, ?_⟩
  · calc
      _ ≤ _ := Finset.card_image_le
      _ = _ := by simp [I]
  · intro M hM
    obtain ⟨a, ha, he⟩ := exists_simple_multiplicities k M
    exact Finset.mem_image.mpr ⟨fun i ↦ ⟨a i, Nat.lt_succ_of_le ((ha i).trans hM)⟩, Finset.mem_univ _, he⟩

include k in
/-- Modules of composition length at most d occupy at most (d+1)^n classes,
where n is the number of simple isomorphism classes. -/
theorem exists_length_bounded_class_cover (d : ℕ) :
    ∃ S : Finset (GrothendieckGroup (FGModuleCat.{u} R)),
      S.card ≤ (d + 1) ^ (simpleIsomorphismClasses R).ncard ∧
      ∀ M : FGModuleCat.{u} R, FGModuleCat.moduleLength M ≤ d → GrothendieckGroup.of M ∈ S := by
  classical
  let I := ↥(simpleIsomorphismClasses R)
  let : Fintype I := (finite_simpleIsomorphismClasses (R := R) k).fintype
  let : BEq I := instBEqOfDecidableEq
  let v (i : I) := GrothendieckGroup.of ((fromSkeleton _).obj i.val)
  let eval (a : I → Fin (d + 1)) := ∑ i, (a i).val • v i
  refine ⟨Finset.univ.image eval, ?_, ?_⟩
  · calc
      _ ≤ _ := Finset.card_image_le
      _ = _ := by simp [I]
  · intro M hM
    obtain ⟨a, ha, he⟩ := exists_length_bounded_multiplicities k M
    exact Finset.mem_image.mpr ⟨fun i ↦ ⟨a i, Nat.lt_succ_of_le ((ha i).trans hM)⟩, Finset.mem_univ _, he⟩

/-- Only finitely many ambient Grothendieck classes occur in bounded
ground-field dimension. -/
theorem finite_classes_of_groundFinrank_le (d : ℕ) :
    {c : GrothendieckGroup (FGModuleCat.{u} R) | ∃ M : FGModuleCat.{u} R, Module.finrank k (M.obj : Type u) ≤ d ∧ GrothendieckGroup.of M = c}.Finite := by
  obtain ⟨S, _, hS⟩ := exists_bounded_class_cover (R := R) k d
  exact S.finite_toSet.subset fun _ ⟨M, hM, he⟩ ↦ he ▸ hS M hM

end EFiniteCharacterizations
