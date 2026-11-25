module

public import EFiniteCharacterizations.Silting.Fans.RankTwoBricks
public import EFiniteCharacterizations.Silting.Fans.MediantCount
public import EFiniteCharacterizations.Silting.Fans.ConeSaturation
public import EFiniteCharacterizations.Silting.ThickSubcategories.BoundedProjectiveHomotopy

/-!
# Finite Stern–Brocot plane test and silting count in rank two

Proposition 8.3 (`cor:stern-brocot`) of the manuscript. For an algebra of rank two
with indecomposable projectives `P, Q` and `x = dim_k Hom(Q, P)`,
`y = dim_k Hom(P, Q)`, the `g`-vector fan covers the entire plane if and only if the
finitely many Stern–Brocot mediants of depths `x` and `y` in the two mixed quadrants
lie in `Σ(R)`, in which case there are at most `2^x + 2^y + 2` basic two-term silting
complexes (`sternBrocot_plane_test_and_count`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.TwoTerm

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

omit [IsArtinianRing R] in
include k in
private theorem spanning_pair_of_projectives (P Q : FiniteProjective R)
    (hPQ : ∀ T : FiniteProjective R, Indecomposable T.val →
      Nonempty (T.val ≅ P.val) ∨ Nonempty (T.val ≅ Q.val)) (v : RealProjectiveSpace R) :
    ∃ a b : ℝ, a • realProjectiveClass R (ProjectiveClass.of P) +
      b • realProjectiveClass R (ProjectiveClass.of Q) = v := by
  let g := realProjectiveClass R
  let W := Submodule.span ℝ {g (ProjectiveClass.of P), g (ProjectiveClass.of Q)}
  apply Submodule.mem_span_pair.mp
  suffices h : W = ⊤ by change v ∈ W; rw [h]; trivial
  apply top_unique
  rw [← span_realProjectiveClasses R]
  apply Submodule.span_le.mpr
  rintro _ ⟨T,rfl⟩
  apply ProjectiveClass.of_induction_on k T (motive := fun c ↦ g c ∈ W)
  · rw [map_zero]; exact W.zero_mem
  · intro a b ha hb
    rw [map_add]; exact W.add_mem ha hb
  · intro T hT
    rcases hPQ T hT with ⟨e⟩ | ⟨e⟩
    · rw [ProjectiveClass.of_eq_of_iso T P e.some]; exact Submodule.subset_span (by simp)
    · rw [ProjectiveClass.of_eq_of_iso T Q e.some]; exact Submodule.subset_span (by simp)

/-- A pair representing every indecomposable projective gives the plane
criterion. The depth in each mixed quadrant is the corresponding Hom dimension. -/
theorem plane_covered_iff_projective_mediants (P Q : FiniteProjective R)
    (hPQ : ∀ T : FiniteProjective R, Indecomposable T.val →
      Nonempty (T.val ≅ P.val) ∨ Nonempty (T.val ≅ Q.val)) :
    (∀ v : RealProjectiveSpace R, ∃ E L : TwoTerm R, (E.directSum L).IsPresilting ∧
      v ∈ sectorBetween (realProjectiveClass R E.projectiveClass) (realProjectiveClass R L.projectiveClass)) ↔
    ProjectiveMediantsCovered k P Q := by
  constructor
  · intro h c _
    exact isEFinite_of_integral_classes_in_presilting_sectors k (fun g ↦ h (realProjectiveClass R g)) c
  · intro h v
    obtain ⟨_, _, hs, hcov⟩ := exists_bounded_plane_cover_of_mediants k (realProjectiveClass R) P Q h
      (spanning_pair_of_projectives k P Q hPQ)
    obtain ⟨p,hp,hv⟩ := hcov v
    exact ⟨p.1,p.2,hs p hp,hv⟩

/-- The support of the g-vector fan is the whole real plane exactly when
the finitely many mixed-quadrant mediants have presilting representatives. -/
theorem fan_covers_plane_iff_projective_mediants (P Q : FiniteProjective R)
    (hPQ : ∀ T : FiniteProjective R, Indecomposable T.val →
      Nonempty (T.val ≅ P.val) ∨ Nonempty (T.val ≅ Q.val)) :
    (∀ v : RealProjectiveSpace R, ∃ T : TwoTerm R, T.IsPresilting ∧ v ∈ T.gVectorCone) ↔
      ProjectiveMediantsCovered k P Q := by
  constructor
  · intro h c _
    exact (mem_fanSupport_iff_exists_presilting k c).1 (h (realProjectiveClass R c))
  · intro h v
    obtain ⟨E,L,he,hv⟩ := (plane_covered_iff_projective_mediants k P Q hPQ).2 h v
    exact ⟨E.directSum L,he,sectorBetween_subset_gVectorCone E L hv⟩

/-- Isomorphism classes of basic two-term presilting complexes generating
the bounded homotopy category of finite projectives. -/
def basicSiltingClasses (R : Type u) [Ring R] [IsNoetherianRing R] :
    Set (Skeleton (HomotopyCategory (FGModuleCat.{u} R) (ComplexShape.up ℤ))) :=
  {c | ∃ U : TwoTerm R, toSkeleton U.homotopyObject = c ∧ U.IsPresilting ∧
    (∃ l, BasicDecomposition U l) ∧
    ∀ X : (boundedProjective R).FullSubcategory, (ObjectProperty.singleton U.inBoundedProjectives).triangEnvelope X}

omit [IsArtinianRing R] in
include k in
private theorem mutual_add_of_covered_silting {U E L : TwoTerm R}
    (hu : U.IsPresilting) (hgen : ∀ X : (boundedProjective R).FullSubcategory,
      (ObjectProperty.singleton U.inBoundedProjectives).triangEnvelope X)
    (hc : (E.directSum L).IsPresilting)
    (hs : realProjectiveClass R U.projectiveClass ∈
      sectorBetween (realProjectiveClass R E.projectiveClass) (realProjectiveClass R L.projectiveClass)) :
    IsInAdd U.homotopyObject (E.directSum L).homotopyObject ∧
      IsInAdd (E.directSum L).homotopyObject U.homotopyObject := by
  have ha := isInAdd_homotopy_of_stableAdd (isInStableAdd_of_class_mem_sector k U E L hu hc hs)
  have hvan := (isPresilting_iff_homotopy _).1 hc
  exact ⟨ha, Presilting.isInAdd_of_mem_thick _ ((isPresilting_iff_homotopy _).1 hu)
    ((bounded_thick_iff _ _).1 (hgen _)) (fun n hn ↦ subsingleton_from_add ha (hvan n hn))
    (fun n hn ↦ subsingleton_to_add (ha.map (shiftFunctor _ n)) (hvan n hn))⟩

omit [IsArtinianRing R] in
/-- Under the finite mediant test there are at most 2^x + 2^y + 2 basic
two-term silting complexes up to homotopy isomorphism. -/
theorem basicSiltingClasses_card_le_of_mediants (P Q : FiniteProjective R)
    (hPQ : ∀ T : FiniteProjective R, Indecomposable T.val →
      Nonempty (T.val ≅ P.val) ∨ Nonempty (T.val ≅ Q.val))
    (hc : ProjectiveMediantsCovered k P Q) :
    (basicSiltingClasses R).Finite ∧ (basicSiltingClasses R).ncard ≤
      2 ^ Module.finrank k (Q.val ⟶ P.val) + 2 ^ Module.finrank k (P.val ⟶ Q.val) + 2 := by
  classical
  obtain ⟨s, hslen, hs, hcov⟩ := exists_bounded_plane_cover_of_mediants k (realProjectiveClass R) P Q hc
    (spanning_pair_of_projectives k P Q hPQ)
  let C := basicSiltingClasses R
  choose U he hu hb hgen using fun c : C ↦ c.property
  choose l hl using hb
  have indexed (c : C) : ∃ i : Fin s.length,
      IsInAdd (U c).homotopyObject ((s.get i).1.directSum (s.get i).2).homotopyObject ∧
      IsInAdd ((s.get i).1.directSum (s.get i).2).homotopyObject (U c).homotopyObject := by
    obtain ⟨p,hp,hv⟩ := hcov (realProjectiveClass R (U c).projectiveClass)
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
    exact ⟨i, hi ▸ mutual_add_of_covered_silting k (hu c) (hgen c) (hs p hp) hv⟩
  choose idx hidx using indexed
  have hinj : Function.Injective idx := by
    intro c d h
    obtain ⟨hc₁,hc₂⟩ := hidx c
    rw [h] at hc₁ hc₂
    obtain ⟨hd₁,hd₂⟩ := hidx d
    apply Subtype.ext
    exact (he c).symm.trans ((congr_toSkeleton_of_iso
      (iso_of_basic_mutual_add k (hl c) (hl d) (hc₁.trans hd₂) (hd₁.trans hc₂)).some).trans (he d))
  have hfin : Finite C := Finite.of_injective idx hinj
  let _ := Fintype.ofFinite C
  refine ⟨hfin, ?_⟩
  change C.ncard ≤ _
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  exact (Fintype.card_le_of_injective idx hinj).trans (by simpa using hslen)

/-- The finite set of classes tested in the two mixed-sign quadrants. -/
def mixedQuadrantMediants (P Q : FiniteProjective R) : Set (ProjectiveClass R) :=
  sternBrocotMediants (Module.finrank k (Q.val ⟶ P.val)) (ProjectiveClass.of P) (-ProjectiveClass.of Q) ∪
  sternBrocotMediants (Module.finrank k (P.val ⟶ Q.val)) (ProjectiveClass.of Q) (-ProjectiveClass.of P)

/-- For the two projective directions in rank two, membership of the finitely
many mediants in the fan is equivalent to coverage of the whole plane. Under
this test the number of basic two-term silting complexes is at most 2^x + 2^y + 2. -/
theorem sternBrocot_plane_test_and_count (P Q : FiniteProjective R)
    (hPQ : ∀ T : FiniteProjective R, Indecomposable T.val →
      Nonempty (T.val ≅ P.val) ∨ Nonempty (T.val ≅ Q.val)) :
    let test := realProjectiveClass R '' mixedQuadrantMediants k P Q ⊆ gVectorFanSupport R
    (gVectorFanSupport R = Set.univ ↔ test) ∧
      (test → (basicSiltingClasses R).Finite ∧ (basicSiltingClasses R).ncard ≤
        2 ^ Module.finrank k (Q.val ⟶ P.val) + 2 ^ Module.finrank k (P.val ⟶ Q.val) + 2) := by
  have eqv : (realProjectiveClass R '' mixedQuadrantMediants k P Q ⊆ gVectorFanSupport R) ↔
      ProjectiveMediantsCovered k P Q := by
    rw [Set.image_subset_iff]
    exact forall₂_congr fun c _ ↦ mem_fanSupport_iff_exists_presilting k c
  refine ⟨?_,fun h ↦ basicSiltingClasses_card_le_of_mediants k P Q hPQ (eqv.mp h)⟩
  rw [Set.eq_univ_iff_forall]
  exact (fan_covers_plane_iff_projective_mediants k P Q hPQ).trans eqv.symm

end EFiniteCharacterizations.TwoTerm
