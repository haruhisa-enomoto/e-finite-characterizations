module

public import EFiniteCharacterizations.GrothendieckGroups.TorsionClassGroup

/-! # Simple coordinates in the Grothendieck group of a torsion-free class -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v
namespace EFiniteCharacterizations.ExactClassGroup
noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (F : ObjectProperty C) [F.IsClosedUnderExtensions] [F.IsClosedUnderSubobjects]

private def rowInPullback {S X Y V A : C} (s : ExtensionSequence A X S) {j : Y ⟶ S}
    {r : V ⟶ X} {b : V ⟶ Y} [Epi b] (sq : IsPullback b r j s.p) : ExtensionSequence A V Y := by
  let := isIso_kernel_map_of_isPullback sq
  let e := asIso (kernel.map _ _ _ _ sq.w) ≪≫
    (kernelIsKernel s.p).conePointUniqueUpToIso s.shortExact.fIsKernel
  let t : ExtensionSequence (kernel b) V Y := ⟨_,b,kernel.condition b,
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel b) (by dsimp; infer_instance) ‹Epi b›⟩
  exact t.ofIso e (.refl _) (.refl _)

private theorem quotient_difference_eq {S X Y A B : C} (s : ExtensionSequence A X S)
    (t : ExtensionSequence B Y S) (hx : F X) (hy : F Y) :
    of F X hx - of F A (F.prop_of_mono s.i hx) = of F Y hy - of F B (F.prop_of_mono t.i hy) := by
  let sq := IsPullback.of_hasPullback s.p t.p
  let a := rowInPullback s sq.flip
  let b := rowInPullback t sq
  have ha := F.prop_of_mono s.i hx
  have hb := F.prop_of_mono t.i hy
  have hv := F.prop_X₂_of_shortExact a.shortExact ha hy
  have h₁ := of_exact F a ha hv hy
  have h₂ := of_exact F b hb hv hx
  grind

private structure QuotientRow (F : ObjectProperty C) (S : C) where
  kernel : C
  middle : C
  row : ExtensionSequence kernel middle S
  mem : F middle

private def quotientScore (s : Skeleton C) : ExactClassGroup F := by
  classical
  let P := QuotientRow F ((fromSkeleton C).obj s)
  exact if h : Nonempty P then
    let p := Classical.choice h
    of F _ p.mem - of F _ (F.prop_of_mono p.row.i p.mem)
  else 0

private theorem quotientScore_eq {S X A : C} (s : ExtensionSequence A X S) (hx : F X) :
    quotientScore F (toSkeleton S) = of F X hx - of F A (F.prop_of_mono s.i hx) := by
  let t := s.ofIso (.refl _) (.refl _) (fromSkeletonToSkeletonIso S).symm
  let p : QuotientRow F ((fromSkeleton C).obj (toSkeleton S)) := ⟨A,X,t,hx⟩
  classical
  unfold quotientScore
  rw [dite_eq_left (show Nonempty (QuotientRow F _) from ⟨p⟩)]
  let c := Classical.choice (show Nonempty (QuotientRow F _) from ⟨p⟩)
  exact quotient_difference_eq F c.row t c.mem hx

private theorem simpleQuotient {X : C} {l} (h : HasCompositionFactors X l) (hn : ¬ IsZero X) :
    ∃ (S : C) (p : X ⟶ S), Simple S ∧ Epi p := by
  induction h with
  | zero hz => contradiction
  | @cons S X Q l s hs hq ih =>
    by_cases hz : IsZero Q
    · have := s.shortExact.isIso_f_iff.mpr hz
      exact ⟨_,inv s.i,hs,inferInstance⟩
    · obtain ⟨U,q,hu,h⟩ := ih hz
      exact ⟨U,s.p ≫ q,hu,inferInstance⟩

private theorem quotientScore_factors {X : C} {l} (hx : F X) (h : HasCompositionFactors X l) :
    (l.map (quotientScore F)).sum = of F X hx ∧
      ∀ S : C, toSkeleton S ∈ l → inclusion F (quotientScore F (toSkeleton S)) = GrothendieckGroup.of S := by
  classical
  by_cases hz : IsZero X
  · rw [h.eq_zero_of_isZero hz]
    simp [of,GrothendieckMonoid.of_isZero _ _ _ hz]
  obtain ⟨S,p,hs,hp⟩ := simpleQuotient h hz
  let s : ExtensionSequence (kernel p) X S := ⟨_,p,kernel.condition p,
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) (by dsimp; infer_instance) hp⟩
  obtain ⟨a,q,ha,hq,he⟩ := h.split s
  rw [hq.eq_singleton_of_simple] at he
  have dec : a.card < l.card := by simp [he]
  obtain ⟨ih,mem⟩ := quotientScore_factors (F.prop_of_mono s.i hx) ha
  rw [he]
  constructor
  · simp only [Multiset.map_add,Multiset.sum_add,ih,Multiset.map_singleton,Multiset.sum_singleton,
      quotientScore_eq F s hx]
    abel
  · intro Y hy
    rcases Multiset.mem_add.mp hy with hy | hy
    · exact mem Y hy
    · have heq := Multiset.mem_singleton.mp hy
      rw [heq,quotientScore_eq F s hx,map_sub,inclusion_of,inclusion_of,GrothendieckGroup.of_shortExact _ s.shortExact]
      have he' := GrothendieckGroup.of_eq_of_iso (toSkeleton_eq_toSkeleton_iff.mp heq).some
      grind
termination_by l.card

/-- The inclusion of a torsion-free class in a length abelian category
identifies its inherited Grothendieck group with its coordinate subgroup. -/
theorem torsionFree_identifies_support (h₀ : F 0) (length : ∀ X : C, ∃ l, HasCompositionFactors X l) :
    Function.Injective (inclusion F) ∧ (inclusion F).range = supportSubgroup F :=
  identifies_support_of_factor_sum F h₀ length (quotientScore F)
    (fun hx h ↦ (quotientScore_factors F hx h).1) (fun hx h ↦ (quotientScore_factors F hx h).2)

end
end EFiniteCharacterizations.ExactClassGroup
