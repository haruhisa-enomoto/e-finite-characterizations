module

public import EFiniteCharacterizations.GrothendieckGroups.ExactClassGroup
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono

/-! # Simple coordinates in the Grothendieck group of a torsion class -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v
namespace EFiniteCharacterizations.ExactClassGroup
noncomputable section
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (T : ObjectProperty C) [T.IsClosedUnderExtensions] [T.IsClosedUnderQuotients]

private def rowInPushout {S X Y V Q : C} (s : ExtensionSequence S X Q) {j : S ⟶ Y}
    {r : X ⟶ V} {b : Y ⟶ V} [Mono b] (sq : IsPushout s.i j r b) : ExtensionSequence Y V Q := by
  let := isIso_cokernel_map_of_isPushout sq
  let e := (asIso (cokernel.map _ _ _ _ sq.w)).symm ≪≫
    (cokernelIsCokernel s.i).coconePointUniqueUpToIso s.shortExact.gIsCokernel
  exact (ExtensionSequence.quotient b).ofIso (.refl _) (.refl _) e

/-- Amalgamating two embeddings of the same object identifies the two
differences of classes of a member and its quotient. -/
private theorem difference_eq {S X Y Q Z : C} (s : ExtensionSequence S X Q)
    (t : ExtensionSequence S Y Z) (hx : T X) (hy : T Y) :
    of T X hx - of T Q (T.prop_of_epi s.p hx) = of T Y hy - of T Z (T.prop_of_epi t.p hy) := by
  let sq := IsPushout.of_hasPushout s.i t.i
  let a := rowInPushout s sq
  let b := rowInPushout t sq.flip
  have hq := T.prop_of_epi s.p hx
  have hz := T.prop_of_epi t.p hy
  have hv := T.prop_X₂_of_shortExact a.shortExact hy hq
  have ha := of_exact T a hy hv hq
  have hb := of_exact T b hx hv hz
  grind

private structure EmbeddingRow (T : ObjectProperty C) (S : C) where
  middle : C
  quotient : C
  row : ExtensionSequence S middle quotient
  mem : T middle

private def embeddingScore (s : Skeleton C) : ExactClassGroup T := by
  classical
  let P := EmbeddingRow T ((fromSkeleton C).obj s)
  exact if h : Nonempty P then
    let p := Classical.choice h
    of T _ p.mem - of T _ (T.prop_of_epi p.row.p p.mem)
  else 0

private theorem embeddingScore_eq {S X Q : C} (s : ExtensionSequence S X Q) (hx : T X) :
    embeddingScore T (toSkeleton S) = of T X hx - of T Q (T.prop_of_epi s.p hx) := by
  let t := s.ofIso (fromSkeletonToSkeletonIso S).symm (.refl _) (.refl _)
  let p : EmbeddingRow T ((fromSkeleton C).obj (toSkeleton S)) := ⟨X,Q,t,hx⟩
  classical
  unfold embeddingScore
  rw [dite_eq_left (show Nonempty (EmbeddingRow T _) from ⟨p⟩)]
  let c := Classical.choice (show Nonempty (EmbeddingRow T _) from ⟨p⟩)
  exact difference_eq T c.row t c.mem hx

/-- In a length abelian category the inclusion of a torsion class identifies
its inherited Grothendieck group with the subgroup on its composition factors. -/
theorem torsion_identifies_support (h₀ : T 0)
    (length : ∀ X : C, ∃ l, HasCompositionFactors X l) :
    Function.Injective (inclusion T) ∧ (inclusion T).range = supportSubgroup T := by
  apply identifies_support_of_factor_sum T h₀ length (embeddingScore T)
  · intro X l hx h
    induction h with
    | zero hz =>
      simp only [Multiset.map_zero,Multiset.sum_zero,of,GrothendieckMonoid.of_isZero _ _ _ hz,map_zero]
    | cons s hs hq ih =>
      simp only [Multiset.map_cons,Multiset.sum_cons,embeddingScore_eq T s hx,ih (T.prop_of_epi s.p hx),
        sub_add_cancel]
  · intro X l hx h
    induction h with
    | zero => simp
    | @cons S X Q l s hs hq ih =>
      intro Y hy
      rcases Multiset.mem_cons.mp hy with he | hm
      · rw [he,embeddingScore_eq T s hx,map_sub,inclusion_of,inclusion_of,
          GrothendieckGroup.of_shortExact _ s.shortExact,add_sub_cancel_right]
        exact GrothendieckGroup.of_eq_of_iso (toSkeleton_eq_toSkeleton_iff.mp he).some.symm
      · exact ih (T.prop_of_epi s.p hx) Y hm

end
end EFiniteCharacterizations.ExactClassGroup
