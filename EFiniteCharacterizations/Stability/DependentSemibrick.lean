module

public import EFiniteCharacterizations.Modules.FamilyExtraction
public import EFiniteCharacterizations.Stability.JointStability

/-! # A finite semibrick with a relation among its ambient classes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Multiset

universe u

namespace EFiniteCharacterizations.FamilyExtraction

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]

private noncomputable def supportWithMultiplicity (L : Family R) :
    Multiset (Skeleton (FGModuleCat.{u} R)) := by
  classical
  exact (L.filter fun X ↦ ¬ IsZero X).map toSkeleton

omit [IsNoetherianRing R] [IsArtinianRing R] in
private theorem mem_support {L : Family R} {x : Skeleton (FGModuleCat.{u} R)} :
    x ∈ supportWithMultiplicity L ↔ ∃ X ∈ L, ¬ IsZero X ∧ toSkeleton X = x := by
  classical
  simp [supportWithMultiplicity, and_assoc]

omit [IsArtinianRing R] in
private theorem support_sum (L : Family R) :
    ((supportWithMultiplicity L).map (fun x ↦ GrothendieckGroup.of ((fromSkeleton _).obj x))).sum =
      totalClass L := by
  classical
  induction L using Multiset.induction_on with
  | empty => simp [supportWithMultiplicity, totalClass]
  | cons X L ih =>
    by_cases hz : IsZero X
    · simpa [supportWithMultiplicity, totalClass, hz, GrothendieckGroup.of_isZero hz] using ih
    · simp only [supportWithMultiplicity, Multiset.filter_cons_of_pos (p := fun X ↦ ¬ IsZero X) L hz, map_cons, sum_cons, totalClass]
      exact congrArg₂ (· + ·) (GrothendieckGroup.of_eq_of_iso (fromSkeletonToSkeletonIso X)) ih

private theorem Minimal.iso_of_nonzero {L M : Family R} (hm : Minimal L M)
    {X Y : FGModuleCat.{u} R} (hx : X ∈ L ∨ X ∈ M) (hy : Y ∈ L ∨ Y ∈ M)
    (f : X ⟶ Y) (hf : f ≠ 0) : IsIso f := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hm.isIso hx hy f hf
  · exact (hf (hm.1.orthogonal X hx Y hy f)).elim
  · exact (hf (hm.reverse X hx Y hy f)).elim
  · exact hm.swap.isIso hx hy f hf

private theorem Minimal.support_semibrick {L M : Family R} (hm : Minimal L M) :
    IsSemibrick {x | x ∈ supportWithMultiplicity L ∨ x ∈ supportWithMultiplicity M} := by
  have rep {x : Skeleton (FGModuleCat.{u} R)} (hx : x ∈ supportWithMultiplicity L ∨ x ∈ supportWithMultiplicity M) :
      ∃ X, (X ∈ L ∨ X ∈ M) ∧ ¬ IsZero X ∧ Nonempty (X ≅ (fromSkeleton _).obj x) := by
    rcases hx with hl | hr
    · obtain ⟨X, hX, hn, he⟩ := mem_support.mp hl
      exact ⟨X, Or.inl hX, hn, toSkeleton_eq_iff.mp he⟩
    · obtain ⟨X, hX, hn, he⟩ := mem_support.mp hr
      exact ⟨X, Or.inr hX, hn, toSkeleton_eq_iff.mp he⟩
  have iso {x y} (hx : x ∈ supportWithMultiplicity L ∨ x ∈ supportWithMultiplicity M)
      (hy : y ∈ supportWithMultiplicity L ∨ y ∈ supportWithMultiplicity M)
      (f : (fromSkeleton _).obj x ⟶ (fromSkeleton _).obj y) (hf : f ≠ 0) : IsIso f := by
    obtain ⟨_, hX, _, ⟨e⟩⟩ := rep hx
    obtain ⟨_, hY, _, ⟨d⟩⟩ := rep hy
    let g := e.hom ≫ f ≫ d.inv
    have he : e.inv ≫ g ≫ d.hom = f := by simp [g]
    have := hm.iso_of_nonzero hX hY g (fun hz ↦ hf (by simpa [hz] using he.symm))
    rw [← he]
    infer_instance
  constructor
  · intro x hx
    obtain ⟨_, _, hn, ⟨e⟩⟩ := rep hx
    exact ⟨fun hz ↦ hn (hz.of_iso e), iso hx hx⟩
  · intro x hx y hy hne f
    by_contra hf
    have := iso hx hy f hf
    exact hne ((toSkeleton_fromSkeleton_obj x).symm.trans
      ((congr_toSkeleton_of_iso (asIso f)).trans (toSkeleton_fromSkeleton_obj y)))

omit [IsNoetherianRing R] [IsArtinianRing R] in
private theorem Minimal.disjoint_support {L M : Family R} (hm : Minimal L M)
    {x} (hx : x ∈ supportWithMultiplicity L) : x ∉ supportWithMultiplicity M := by
  obtain ⟨X, hX, hn, rfl⟩ := mem_support.mp hx
  intro hy
  obtain ⟨Y, hY, _, he⟩ := mem_support.mp hy
  let e := (Skeleton.isoOfEq he).symm
  have hz := hm.1.orthogonal X hX Y hY e.hom
  exact hn ((IsZero.iff_id_eq_zero X).2 (by simpa using congrArg (fun f : X ⟶ Y ↦ f ≫ e.inv) hz))

/-- Extraction preserves the maximal-length members of the input families:
each output class is represented by an input member or a strictly shorter module. -/
theorem Relation.exists_dependent_semibrick_below {A₀ B₀ : Family R} (hr : Relation A₀ B₀) :
    ∃ s : Finset (Skeleton (FGModuleCat.{u} R)), IsSemibrick (C := FGModuleCat.{u} R) ↑s ∧
      (∀ x ∈ s, ∃ X, toSkeleton X = x ∧ Below A₀ B₀ X) ∧
      ¬ LinearIndependent ℤ (fun x : s ↦ GrothendieckGroup.of ((fromSkeleton _).obj x.val)) := by
  classical
  obtain ⟨L, M, hm, hb⟩ := hr.exists_minimal_below
  let A := supportWithMultiplicity L
  let B := supportWithMultiplicity M
  let s := A.toFinset ∪ B.toFinset
  let v (x : Skeleton (FGModuleCat.{u} R)) := GrothendieckGroup.of ((fromSkeleton _).obj x)
  refine ⟨s, ?_, ?_, ?_⟩
  · convert hm.support_semibrick using 1
    ext x
    simp [s, A, B]
  · intro x hx
    rcases Finset.mem_union.mp hx with hl | hr
    · obtain ⟨X, hX, _, he⟩ := mem_support.mp (Multiset.mem_toFinset.mp hl)
      exact ⟨X, he, hb X (Or.inl hX)⟩
    · obtain ⟨X, hX, _, he⟩ := mem_support.mp (Multiset.mem_toFinset.mp hr)
      exact ⟨X, he, hb X (Or.inr hX)⟩
  intro hi
  have sumCounts (T : Multiset (Skeleton (FGModuleCat.{u} R))) (ht : T.toFinset ⊆ s) :
      (∑ x : s, (T.count x.val : ℤ) • v x.val) = (T.map v).sum := by
    rw [Finset.sum_coe_sort s (fun x ↦ (T.count x : ℤ) • v x)]
    simp only [natCast_zsmul]
    exact (Finset.sum_subset ht (fun x _ hx ↦ by simp [Multiset.count_eq_zero.mpr (by simpa using hx)])).symm.trans
      (Finset.sum_multiset_map_count T v).symm
  let c (x : s) : ℤ := A.count x.val - (B.count x.val : ℤ)
  have hc : ∑ x : s, c x • v x.val = 0 := by
    simp only [c, sub_smul, Finset.sum_sub_distrib]
    rw [sumCounts A Finset.subset_union_left, sumCounts B Finset.subset_union_right]
    exact sub_eq_zero.mpr ((support_sum L).trans (hm.1.classes.trans (support_sum M).symm))
  have eqc (x : s) : A.count x.val = B.count x.val := by
    have hz := linearIndependent_iff'.mp hi Finset.univ c hc x (Finset.mem_univ x)
    exact_mod_cast sub_eq_zero.mp hz
  have noA {x} (hx : x ∈ A) : False := by
    let y : s := ⟨x, Finset.mem_union_left _ (Multiset.mem_toFinset.mpr hx)⟩
    have hy := eqc y
    exact hm.disjoint_support hx (Multiset.count_pos.mp (hy ▸ Multiset.count_pos.mpr hx))
  rcases hm.1.nonzero with ⟨X, hX, hn⟩ | ⟨Y, hY, hn⟩
  · exact noA (mem_support.mpr ⟨X, hX, hn, rfl⟩)
  · have hy : toSkeleton Y ∈ B := mem_support.mpr ⟨Y, hY, hn, rfl⟩
    let y : s := ⟨_, Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hy)⟩
    exact noA (Multiset.count_pos.mp ((eqc y).symm ▸ Multiset.count_pos.mpr hy))

/-- A failure of equal-class Hom produces a finite semibrick with a
nontrivial integral dependence among its Grothendieck classes. -/
theorem exists_dependent_semibrick (h : ¬ EqualClassHom (FGModuleCat.{u} R)) :
    ∃ s : Finset (Skeleton (FGModuleCat.{u} R)), IsSemibrick (C := FGModuleCat.{u} R) (↑s) ∧
      ¬ LinearIndependent ℤ (fun x : s ↦ GrothendieckGroup.of ((fromSkeleton _).obj x.val)) := by
  classical
  obtain ⟨L, M, hm⟩ := exists_minimal h
  obtain ⟨s, hs, _, hd⟩ := hm.1.exists_dependent_semibrick_below
  exact ⟨s, hs, hd⟩

/-- Replace integral multiplicities by the two multisets of positive and
negative occurrences. -/
noncomputable def weightedFamily {I : Type*} [Fintype I]
    (X : I → FGModuleCat.{u} R) (a : I → ℕ) : Family R :=
  ∑ i, Multiset.replicate (a i) (X i)

omit [IsNoetherianRing R] [IsArtinianRing R] in
theorem mem_weightedFamily {I : Type*} [Fintype I]
    {X : I → FGModuleCat.{u} R} {a : I → ℕ} {Y : FGModuleCat.{u} R} :
    Y ∈ weightedFamily X a ↔ ∃ i, a i ≠ 0 ∧ Y = X i := by
  classical
  simp [weightedFamily, Multiset.mem_sum, Multiset.mem_replicate]

omit [IsNoetherianRing R] [IsArtinianRing R] in
theorem totalClass_weightedFamily {I : Type*} [Fintype I]
    (X : I → FGModuleCat.{u} R) (a : I → ℕ) :
    totalClass (weightedFamily X a) = ∑ i, a i • GrothendieckGroup.of (X i) := by
  classical
  unfold weightedFamily totalClass
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => simp [Finset.sum_insert hi, ih]

/-- Equal-class Hom forces the ambient classes of every finite semibrick to
be integrally linearly independent. -/
theorem independent_semibrick_of_equalClassHom (h : EqualClassHom (FGModuleCat.{u} R))
    (s : Finset (Skeleton (FGModuleCat.{u} R))) (hs : IsSemibrick (C := FGModuleCat.{u} R) ↑s) :
    LinearIndependent ℤ (fun x : s ↦ GrothendieckGroup.of ((fromSkeleton _).obj x.val)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_contra hi
  let X (j : s) := (fromSkeleton (FGModuleCat.{u} R)).obj j.val
  let a (j : s) := (c j).toNat
  let b (j : s) := (-c j).toNat
  have hd (j : s) : (a j : ℤ) - b j = c j := by dsimp [a,b]; omega
  apply Relation.not_equalClassHom (L := weightedFamily X a) (M := weightedFamily X b) _ h
  constructor
  · rw [totalClass_weightedFamily, totalClass_weightedFamily, ← sub_eq_zero, ← Finset.sum_sub_distrib]
    simpa only [← natCast_zsmul, ← sub_smul, hd, X] using hc
  · have hn := (hs.1 i.property).1
    by_cases hp : 0 < c i
    · exact Or.inl ⟨X i, mem_weightedFamily.mpr ⟨i, by dsimp [a]; omega, rfl⟩, hn⟩
    · exact Or.inr ⟨X i, mem_weightedFamily.mpr ⟨i, by dsimp [b]; omega, rfl⟩, hn⟩
  · intro A hA B hB
    obtain ⟨p, hp, rfl⟩ := mem_weightedFamily.mp hA
    obtain ⟨q, hq, rfl⟩ := mem_weightedFamily.mp hB
    apply hs.2 p.val p.property q.val q.property
    intro he
    have := Subtype.ext he
    subst q
    dsimp [a,b] at hp hq
    omega

/-- Equal-class Hom is equivalent to integral independence of the ambient
classes in each finite semibrick. -/
theorem equalClassHom_iff_independent_semibricks :
    EqualClassHom (FGModuleCat.{u} R) ↔
      ∀ s : Finset (Skeleton (FGModuleCat.{u} R)), IsSemibrick (C := FGModuleCat.{u} R) ↑s →
        LinearIndependent ℤ (fun x : s ↦ GrothendieckGroup.of ((fromSkeleton _).obj x.val)) := by
  refine ⟨independent_semibrick_of_equalClassHom, fun h ↦ ?_⟩
  by_contra hn
  obtain ⟨s, hs, hd⟩ := exists_dependent_semibrick hn
  exact hd (h s hs)

/-- If the weights vanishing on a subfamily already vanish on the entire
semibrick, failure of joint stability gives a new relation supported on the
subfamily and strictly shorter modules. -/
theorem joint_weight_or_shorter_relation (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]
    (s t : Finset (Skeleton (FGModuleCat.{u} R))) (hts : t ⊆ s)
    (hs : IsSemibrick (C := FGModuleCat.{u} R) ↑s)
    (hspan : ∀ w : Weight (FGModuleCat.{u} R), (∀ x ∈ t, w.eval ((fromSkeleton _).obj x) = 0) →
      ∀ x ∈ s, w.eval ((fromSkeleton _).obj x) = 0) :
    (∃ g : ProjectiveClass R, (s : Set _) ⊆ stableClasses (C := FGModuleCat.{u} R) (projectiveClassWeight k g)) ∨
    ∃ A B : Family R, Relation A B ∧ ∀ Z, Z ∈ A ∨ Z ∈ B →
      toSkeleton Z ∈ t ∨ ∃ j ∈ s, FGModuleCat.moduleLength Z < FGModuleCat.moduleLength ((fromSkeleton _).obj j) := by
  classical
  let U := ⋃ x ∈ (s : Set _), properSubobjectClasses ((fromSkeleton (FGModuleCat.{u} R)).obj x)
  let := (finite_joint_subobject_classes k s.finite_toSet).fintype
  rcases joint_projective_stability_or_relation_on k s hs t hspan with hw | ⟨a, c, ha, ⟨j₀, hp⟩, he⟩
  · exact Or.inl hw
  right
  let X (i : s) := (fromSkeleton (FGModuleCat.{u} R)).obj i.val
  have witness (j : U) : ∃ (i : s) (V : FGModuleCat.{u} R) (m : V ⟶ X i),
      Mono m ∧ ¬ IsZero V ∧ ¬ IsIso m ∧ GrothendieckGroup.of V = j.val := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp j.property
    obtain ⟨his, V, m, hm, hn, hni, hc⟩ := Set.mem_iUnion.mp hi
    exact ⟨⟨i, his⟩, V, m, hm, hn, hni, hc⟩
  choose owner V m hm hn hni hc using witness
  let pos (i : t) := (c i).toNat
  let neg (i : t) := (-c i).toNat
  have hd (i : t) : (pos i : ℤ) - neg i = c i := by dsimp [pos,neg]; omega
  let mult (j : U) := (a j).toNat
  have ht (j : U) : (mult j : ℤ) = a j := Int.toNat_of_nonneg (ha j)
  let Y (i : t) := (fromSkeleton (FGModuleCat.{u} R)).obj i.val
  refine ⟨weightedFamily Y pos, weightedFamily V mult + weightedFamily Y neg, ?_, ?_⟩
  swap
  · intro Z hz
    rcases hz with h | h
    · obtain ⟨i, _, rfl⟩ := mem_weightedFamily.mp h
      exact Or.inl ((toSkeleton_fromSkeleton_obj i.val).symm ▸ i.property)
    · rcases Multiset.mem_add.mp h with h | h
      · obtain ⟨j, _, rfl⟩ := mem_weightedFamily.mp h
        exact Or.inr ⟨_, (owner j).property, FGModuleCat.moduleLength_lt_of_mono (m j) (hni j)⟩
      · obtain ⟨i, _, rfl⟩ := mem_weightedFamily.mp h
        exact Or.inl ((toSkeleton_fromSkeleton_obj i.val).symm ▸ i.property)
  constructor
  · have hadd (L M : Family R) : totalClass (L + M) = totalClass L + totalClass M := by simp [totalClass]
    rw [hadd, ← sub_eq_iff_eq_add]
    simp only [totalClass_weightedFamily, ← Finset.sum_sub_distrib, ← natCast_zsmul, ← sub_smul, hd, ht, hc]
    exact he.symm
  · right
    refine ⟨V j₀, Multiset.mem_add.mpr (Or.inl (mem_weightedFamily.mpr ⟨j₀, ?_, rfl⟩)), hn j₀⟩
    dsimp [mult]
    omega
  · intro A hA B hB
    obtain ⟨i, hi, rfl⟩ := mem_weightedFamily.mp hA
    rcases Multiset.mem_add.mp hB with hV | hX
    · obtain ⟨j, _, rfl⟩ := mem_weightedFamily.mp hV
      exact hs.hom_to_proper_subobject (hts i.property) (owner j).property (m j) (hni j)
    · obtain ⟨q, hq, rfl⟩ := mem_weightedFamily.mp hX
      apply hs.2 _ (hts i.property) _ (hts q.property)
      intro hij
      have := Subtype.ext hij
      subst q
      dsimp [pos,neg] at hi hq
      omega

/-- Equal-class Hom gives a common projective stability weight for every finite semibrick. -/
theorem exists_joint_weight_of_equalClassHom (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]
    (h : EqualClassHom (FGModuleCat.{u} R)) (s : Finset (Skeleton (FGModuleCat.{u} R)))
    (hs : IsSemibrick (C := FGModuleCat.{u} R) ↑s) :
    ∃ g : ProjectiveClass R, (s : Set _) ⊆ stableClasses (C := FGModuleCat.{u} R) (projectiveClassWeight k g) := by
  rcases joint_weight_or_shorter_relation k s s Finset.Subset.rfl hs (fun _ h ↦ h) with hw | ⟨_, _, hr, _⟩
  · exact hw
  · exact (hr.not_equalClassHom h).elim

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
theorem finite_semibricks_of_equalClassHom (h : EqualClassHom (FGModuleCat.{u} R))
    {s : Set (Skeleton (FGModuleCat.{u} R))} (hs : IsSemibrick s) : s.Finite := by
  classical
  by_contra hn
  obtain ⟨t, ht, hc⟩ := (show s.Infinite from hn).exists_subset_card_eq ((simpleIsomorphismClasses R).ncard + 1)
  have hle := card_le_simple_count_of_independent_classes k (independent_semibrick_of_equalClassHom h t (hs.subset ht))
  simp only [Fintype.card_coe] at hle
  omega

private theorem independent_with_nonzero_weight {G : Type*} [AddCommGroup G] {I : Type*}
    [Fintype I] {v : I → G} (hv : LinearIndependent ℤ v) (w : G →+ ℤ)
    (hzero : ∀ i, w (v i) = 0) {x : G} (hx : w x ≠ 0) :
    LinearIndependent ℤ (fun i : Option I ↦ i.elim x v) := by
  classical
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro c hc
  rw [Fintype.sum_option] at hc
  simp only [Option.elim_none, Option.elim_some] at hc
  have hz := congrArg w hc
  simp [map_sum, map_zsmul, hzero] at hz
  have hn : c none = 0 := hz.resolve_right hx
  rw [hn, zero_smul, zero_add] at hc
  rintro (_ | i)
  · exact hn
  · exact hv _ hc i

include k in
theorem fullSize_semibrick_eq_simples_of_equalClassHom (h : EqualClassHom (FGModuleCat.{u} R))
    {s : Set (Skeleton (FGModuleCat.{u} R))} (hs : IsSemibrick s)
    (hc : s.ncard = (simpleIsomorphismClasses R).ncard) : s = simpleIsomorphismClasses R := by
  classical
  have hf := finite_semibricks_of_equalClassHom k h hs
  let t := hf.toFinset
  have ht : (t : Set _) = s := hf.coe_toFinset
  have hs' : IsSemibrick (C := FGModuleCat.{u} R) ↑t := ht ▸ hs
  obtain ⟨g, hg⟩ := exists_joint_weight_of_equalClassHom k h t hs'
  let w := projectiveClassWeight k g
  let v (i : t) := GrothendieckGroup.of ((fromSkeleton _).obj i.val)
  have hzero (i : t) : w (v i) = 0 := (hg i.property).2.1
  have hw : w = 0 := by
    ext x
    by_contra hn
    have hi := independent_with_nonzero_weight (independent_semibrick_of_equalClassHom h t hs') w hzero hn
    have hle := card_le_simple_count_of_independent_classes k hi
    simp only [Fintype.card_option, Fintype.card_coe] at hle
    have hcard : t.card = s.ncard := by rw [← ht, Set.ncard_coe_finset]
    omega
  change ↑t ⊆ stableClasses w at hg
  rw [hw, stableClasses_zero, ht] at hg
  exact Set.eq_of_subset_of_ncard_le hg hc.ge (finite_simpleIsomorphismClasses k)

end EFiniteCharacterizations.FamilyExtraction
