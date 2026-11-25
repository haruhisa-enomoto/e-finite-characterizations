module

public import EFiniteCharacterizations.GrothendieckGroups.WideGrothendieckEquivalence
public import EFiniteCharacterizations.Stability.StableSeparationWeights
public import EFiniteCharacterizations.Characterizations.FixedClassFiniteness

/-! # Stable composition factors and polystable modules at a fixed class -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

namespace EFiniteCharacterizations

section Sums

variable {C : Type u} [Category.{v} C] [Abelian C] (θ : Weight C)

/-- The direct sum of a list of stable isomorphism classes, with repetitions. -/
noncomputable def Weight.stableSum : List (stableClasses θ) → C
  | [] => 0
  | a :: l => (fromSkeleton C).obj a.val ⊞ stableSum l

/-- A polystable object is a finite direct sum of stable objects. -/
def Weight.IsPolystable (X : C) : Prop :=
  ∃ l, Nonempty (θ.stableSum l ≅ X)

theorem Weight.IsStable.isPolystable {θ : Weight C} {X : C} (h : θ.IsStable X) : θ.IsPolystable X := by
  let a : stableClasses θ := ⟨toSkeleton X,h.of_iso (fromSkeletonToSkeletonIso X).symm⟩
  exact ⟨[a],⟨(isoBiprodZero (isZero_zero C)).symm ≪≫ fromSkeletonToSkeletonIso X⟩⟩

private theorem stableSum_perm {l m : List (stableClasses θ)} (h : l.Perm m) :
    Nonempty (θ.stableSum l ≅ θ.stableSum m) := by
  induction h with
  | nil => exact ⟨Iso.refl _⟩
  | cons _ _ ih => exact ih.map (biprod.mapIso (Iso.refl _))
  | swap a b l => exact ⟨(biprod.associator _ _ _).symm ≪≫
      biprod.mapIso (biprod.braiding _ _) (Iso.refl _) ≪≫ biprod.associator _ _ _⟩
  | trans _ _ ih jh => exact ⟨ih.some ≪≫ jh.some⟩

private theorem stableSum_perm_of_equal_class
    (hind : LinearIndependent ℤ (fun a : stableClasses θ ↦ GrothendieckGroup.of ((fromSkeleton C).obj a.val)))
    (l m : List (stableClasses θ)) (he : GrothendieckGroup.of (θ.stableSum l) = GrothendieckGroup.of (θ.stableSum m)) :
    l.Perm m := by
  classical
  let count (l : List (stableClasses θ)) := (l.map (fun a ↦ Finsupp.single a (1 : ℤ))).sum
  let v (a : stableClasses θ) := GrothendieckGroup.of ((fromSkeleton C).obj a.val)
  have hc (t : List (stableClasses θ)) : Finsupp.linearCombination ℤ v (count t) =
      GrothendieckGroup.of (θ.stableSum t) := by
    induction t with
    | nil => simp [count,Weight.stableSum,GrothendieckGroup.of_isZero (isZero_zero C)]
    | cons a t ih =>
      change Finsupp.linearCombination ℤ v (Finsupp.single a 1 + count t) = _
      rw [map_add,ih,Finsupp.linearCombination_single,one_smul]
      exact (GrothendieckGroup.of_shortExact _ (ShortComplex.Splitting.ofHasBinaryBiproduct ((fromSkeleton C).obj a.val) (θ.stableSum t)).shortExact).symm
  have hv := hind ((hc l).trans (he.trans (hc m).symm))
  have hx (a : stableClasses θ) (t : List (stableClasses θ)) : count t a = (t.count a : ℤ) := by
    induction t with
    | nil => simp [count]
    | cons b t ih =>
      change ((Finsupp.single b (1 : ℤ) + count t : stableClasses θ →₀ ℤ) a) = _
      by_cases hab : b = a <;> simp [hab,ih,add_comm]
  apply List.perm_iff_count.2
  intro a
  exact_mod_cast (hx a l).symm.trans ((DFunLike.congr_fun hv a).trans (hx a m))

end Sums

variable {R : Type u} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]
variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

/-- At each integral projective weight the ambient class determines a
polystable isomorphism class precisely for E-finite algebras. -/
theorem isEFinite_iff_unique_polystable_class :
    IsEFinite R ↔ ∀ (g : ProjectiveClass R) (X Y : FGModuleCat.{u} R),
      (projectiveClassWeight k g).IsPolystable X → (projectiveClassWeight k g).IsPolystable Y →
      GrothendieckGroup.of X = GrothendieckGroup.of Y → Nonempty (X ≅ Y) := by
  constructor
  · rintro h g X Y ⟨l,⟨e⟩⟩ ⟨m,⟨f⟩⟩ hxy
    have hh := (GrothendieckGroup.of_eq_of_iso e).trans (hxy.trans (GrothendieckGroup.of_eq_of_iso f).symm)
    have hp := stableSum_perm_of_equal_class _ (linearIndependent_stableClasses_of_isEFinite k h g) l m hh
    exact (stableSum_perm _ hp).map (fun i ↦ e.symm ≪≫ i ≪≫ f)
  · intro h
    by_contra hn
    obtain ⟨g,X,Y,hx,hy,hd,he⟩ := exists_equalClass_stable_pair_allFields k hn
    exact hd (h g X Y hx.isPolystable hy.isPolystable he)

include k in
open IsWideClass in
/-- Semistable objects of the same ambient class have identical stable
Jordan–Hölder factors, with multiplicity, under E-finiteness. -/
theorem stable_factors_eq_of_isEFinite (he : IsEFinite R) (θ : Weight (FGModuleCat.{u} R))
    (X Y : θ.semistableCategory) (hc : GrothendieckGroup.of X.obj = GrothendieckGroup.of Y.obj) :
    let W : ObjectProperty (FGModuleCat.{u} R) := θ.IsSemistable
    letI : Fact (IsWideClass W) := ⟨θ.isWideClass_semistable⟩
    ∀ l m, HasCompositionFactors X l → HasCompositionFactors Y m → l = m := by
  let W : ObjectProperty (FGModuleCat.{u} R) := θ.IsSemistable
  let : Fact (IsWideClass W) := ⟨θ.isWideClass_semistable⟩
  dsimp only
  intro l m hl hm
  have hxy : GrothendieckGroup.of X = GrothendieckGroup.of Y :=
    inclusionK₀_injective_of_isEFinite k he θ.isWideClass_semistable (by simpa only [inclusionK₀_of] using hc)
  let h := exists_intrinsic_factors (W := W)
  classical
  apply Multiset.ext.mpr
  intro a
  have heq := congrArg (simpleMultiplicity h a) hxy
  simp only [simpleMultiplicity,GrothendieckGroup.lift_of] at heq
  rw [hl.unique (h X).choose_spec,hm.unique (h Y).choose_spec]
  exact_mod_cast heq

/-- Polystable isomorphism classes of a prescribed ambient class. -/
def polystableClassesOfClass {C : Type u} [Category.{v} C] [Abelian C]
    (θ : Weight C) (c : GrothendieckGroup C) : Set (Skeleton C) :=
  {x | ∃ X : C, toSkeleton X = x ∧ θ.IsPolystable X ∧ GrothendieckGroup.of X = c}

theorem isEFinite_iff_subsingleton_polystableClassesOfVector :
    IsEFinite R ↔ ∀ (g : ProjectiveClass R) (d : simpleIsomorphismClasses R → ℕ),
      (polystableClassesOfClass (C := FGModuleCat.{u} R) (projectiveClassWeight k g) (classOfCompositionVector k d)).Subsingleton := by
  rw [isEFinite_iff_unique_polystable_class k]
  constructor
  · rintro h g d _ ⟨X,rfl,hX,hcX⟩ _ ⟨Y,rfl,hY,hcY⟩
    exact toSkeleton_eq_toSkeleton_iff.2 (h g X Y hX hY (hcX.trans hcY.symm))
  · intro h g X Y hX hY hc
    obtain ⟨d,hd⟩ := exists_compositionVector_of_module k X
    exact toSkeleton_eq_toSkeleton_iff.1 (h g d ⟨X,rfl,hX,hd.symm⟩ ⟨Y,rfl,hY,hc.symm.trans hd.symm⟩)

open IsWideClass in
/-- A single integral weight realizes each nonempty fixed-class slice of a
wide subcategory as the full semistable slice at that class. -/
theorem exists_weight_for_wide_class_slices (he : IsEFinite R)
    {W : ObjectProperty (FGModuleCat.{u} R)} (hw : IsWideClass W) :
    ∃ g : ProjectiveClass R, ∀ X Y, W X → GrothendieckGroup.of X = GrothendieckGroup.of Y →
      (W Y ↔ (projectiveClassWeight k g).IsSemistable Y) := by
  obtain ⟨g,hstab,hsem⟩ := exists_weight_stabilizing_wide_simples k he hw
  let θ := projectiveClassWeight k g
  let V : ObjectProperty (FGModuleCat.{u} R) := θ.IsSemistable
  let : Fact (IsWideClass V) := ⟨θ.isWideClass_semistable⟩
  let s := simpleMemberClasses W
  let T := supportedOn V s
  have ht : IsWideClass T := isWideClass_supportedOn s
  have hWT {X} (hx : W X) : T X := by
    apply hw.extension_induction T ht.zero_mem _ hx
    intro S hs hu _ hq
    have hv := hstab _ hu
    let U : V.FullSubcategory := ⟨_,hv.isSemistable⟩
    have hv' := (simple_iff_simpleMember U).1 ((θ.isStable_iff_simple U).1 hv)
    exact ht.extension_mem S hs ((supportedOn_iff_of_simpleMember s hv').2
      (IsSimpleMember.of_iso hw hu (fromSkeletonToSkeletonIso _).symm)) hq
  have hTW {Y} (hy : T Y) : W Y := by
    apply ht.extension_induction W hw.zero_mem _ hy
    intro S hs hu _ hq
    have hmem : IsSimpleMember W ((fromSkeleton _).obj (toSkeleton S.X₁)) :=
      ((simpleMember_supportedOn_iff s).1 hu).2
    exact hw.extension_mem S hs (hw.iso_mem (fromSkeletonToSkeletonIso _) hmem.1) hq
  refine ⟨g,fun X Y hx hc ↦ ⟨hsem Y,fun hy ↦ ?_⟩⟩
  obtain ⟨hx',l,hl,hs⟩ := hWT hx
  let Z : V.FullSubcategory := ⟨Y,hy⟩
  obtain ⟨m,hm⟩ := exists_intrinsic_factors Z
  have eq := stable_factors_eq_of_isEFinite k he θ ⟨X,hx'⟩ Z hc l m hl hm
  exact hTW ⟨hy,m,hm,eq ▸ hs⟩

end EFiniteCharacterizations
