module

public import EFiniteCharacterizations.Subcategories.WideSimpleSupport
public import EFiniteCharacterizations.Stability.SemistableSimples

/-! # Detecting E-finiteness on Grothendieck groups of wide subcategories -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

open IsWideClass

include k in
/-- Two nonisomorphic stable objects of the same ambient class give a
wide subcategory with exactly two simple classes and a noninjective inclusion on K₀. -/
theorem exists_twoSimple_wide_kernel_of_not_isEFinite (hn : ¬ IsEFinite R) :
    ∃ (V : ObjectProperty (FGModuleCat.{u} R)) (hv : IsWideClass V),
      (simpleMemberClasses V).ncard = 2 ∧ ¬ Function.Injective hv.inclusionK₀ := by
  classical
  obtain ⟨g,X,Y,hsX,hsY,hniso,hxy⟩ := exists_equalClass_stable_pair_allFields k hn
  let θ := projectiveClassWeight (R := R) k g
  let W : ObjectProperty (FGModuleCat.{u} R) := θ.IsSemistable
  let hw : IsWideClass W := θ.isWideClass_semistable
  let _ : Fact (IsWideClass W) := ⟨hw⟩
  let s := ({toSkeleton X,toSkeleton Y} : Set _)
  let V := supportedOn W s
  have hv : IsWideClass V := isWideClass_supportedOn s
  have sx : IsSimpleMember W X := (simple_iff_simpleMember (⟨X,hsX.isSemistable⟩ : W.FullSubcategory)).1
    ((θ.isStable_iff_simple _).1 hsX)
  have sy : IsSimpleMember W Y := (simple_iff_simpleMember (⟨Y,hsY.isSemistable⟩ : W.FullSubcategory)).1
    ((θ.isStable_iff_simple _).1 hsY)
  have vx : IsSimpleMember V X := (simpleMember_supportedOn_iff s).2 ⟨sx,by simp [s]⟩
  have vy : IsSimpleMember V Y := (simpleMember_supportedOn_iff s).2 ⟨sy,by simp [s]⟩
  have he : simpleMemberClasses V = s := by
    ext z
    change IsSimpleMember V ((fromSkeleton _).obj z) ↔ _
    refine ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
    · simpa only [toSkeleton_fromSkeleton_obj] using ((simpleMember_supportedOn_iff s).1 hz).2
    · rcases (show z = toSkeleton X ∨ z = toSkeleton Y by simpa [s] using hz) with rfl | rfl
      · exact vx.of_iso hv (fromSkeletonToSkeletonIso X).symm
      · exact vy.of_iso hv (fromSkeletonToSkeletonIso Y).symm
  have hne : toSkeleton X ≠ toSkeleton Y := hniso ∘ toSkeleton_eq_toSkeleton_iff.1
  refine ⟨V,hv,he ▸ Set.ncard_pair hne,fun hin ↦ ?_⟩
  let _ : Fact (IsWideClass V) := ⟨hv⟩
  let A : V.FullSubcategory := ⟨X,vx.1⟩
  let B : V.FullSubcategory := ⟨Y,vy.1⟩
  have : Simple A := (simple_iff_simpleMember A).2 vx
  have : Simple B := (simple_iff_simpleMember B).2 vy
  have hab : GrothendieckGroup.of A = GrothendieckGroup.of B :=
    hin (by simpa only [inclusionK₀_of] using hxy)
  have hdiff : toSkeleton A ≠ toSkeleton B := fun he ↦ hniso
    ((toSkeleton_eq_toSkeleton_iff.1 he).map (fun (e : A ≅ B) ↦ V.ι.mapIso e))
  have hh := congrArg (simpleMultiplicity (exists_intrinsic_factors (W := V)) (toSkeleton A)) hab
  simp [hdiff] at hh

include k in
theorem isEFinite_iff_injective_wideK₀_twoSimples :
    IsEFinite R ↔ ∀ (W : ObjectProperty (FGModuleCat.{u} R)) (h : IsWideClass W),
      (simpleMemberClasses W).ncard = 2 → Function.Injective h.inclusionK₀ := by
  refine ⟨fun he _ h _ ↦ inclusionK₀_injective_of_isEFinite k he h, fun hall ↦ ?_⟩
  by_contra hn
  obtain ⟨W,h,hc,hi⟩ := exists_twoSimple_wide_kernel_of_not_isEFinite k hn
  exact hi (hall W h hc)

include k in
theorem isEFinite_iff_injective_wideK₀ :
    IsEFinite R ↔ ∀ (W : ObjectProperty (FGModuleCat.{u} R)) (h : IsWideClass W),
      Function.Injective h.inclusionK₀ :=
  ⟨fun he _ h ↦ inclusionK₀_injective_of_isEFinite k he h,
    fun hall ↦ (isEFinite_iff_injective_wideK₀_twoSimples k).2 (fun W h _ ↦ hall W h)⟩

end EFiniteCharacterizations
