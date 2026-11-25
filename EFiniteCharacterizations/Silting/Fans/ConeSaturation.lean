module

public import EFiniteCharacterizations.Presentations.StrictSummands
public import EFiniteCharacterizations.Silting.Fans.ConeLatticePoints

/-!
# Lattice saturation of presilting cones and planar sector covers

Proves Lemma 2.1(1) (`lem:fan-lattice`) and Lemma 8.2 (`lem:sector`):

* `mem_gVectorCone_iff_exists_in_add`: the integral lattice points of a presilting
  cone `C(P)` are precisely the `g`-vectors of objects in `add(P)`.
* `exists_sector_cover_of_mediants_in_fan`: if two presilting complexes `E, L` satisfy
  `Hom(E, L[1]) = 0` and all Stern–Brocot mediants up to depth `dim_k Hom(L, E[1])`
  lie in `Σ(R)`, then the planar sector between `[E]` and `[L]` is covered by at most
  `2^j` compatible presilting sectors.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u
namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R] [IsNoetherianRing R] (k : Type u) [Field k] [Algebra k R]
  [Module.Finite k R]

private abbrev SAdd (X Y : TwoTerm R) := IsInAdd X.asArrow Y.asArrow
private abbrev HAdd (X Y : TwoTerm R) := IsInAdd X.homotopyObject Y.homotopyObject

omit [IsNoetherianRing R] in
private theorem leftSummand (X Y : TwoTerm R) : SAdd X (X.directSum Y) :=
  IsInAdd.of_retraction _ _ (inlDirectSum_fstDirectSum X Y)
omit [IsNoetherianRing R] in
private theorem rightSummand (X Y : TwoTerm R) : SAdd Y (X.directSum Y) :=
  IsInAdd.of_retraction _ _ (inrDirectSum_sndDirectSum X Y)

private theorem homotopyAdd {X Y : TwoTerm R} (h : SAdd X Y) : HAdd X Y :=
  h.map (doubleFunctor (C := FGModuleCat.{u} R) ⋙ HomotopyCategory.quotient _ _)

private theorem stableAdd_of_add {A B C D : TwoTerm R} (hAB : SAdd A B) (hBC : B.IsInStableAdd C)
    (hCD : SAdd C D) : A.IsInStableAdd D := by
  obtain ⟨K,hK⟩ := hBC
  let P := contractible K
  exact ⟨K, (hAB.trans hK).trans (isInAdd_directSum C P _ (hCD.trans (leftSummand D P)) (rightSummand D P))⟩

include k in
/-- Contractible terms can be discarded when representing the class of an
object of the stable additive closure. -/
theorem class_in_add_of_stableAdd (X W : TwoTerm R) (h : X.IsInStableAdd W) :
    ∃ Y : TwoTerm R, IsInAdd Y.asArrow W.asArrow ∧ Y.projectiveClass = X.projectiveClass := by
  classical
  generalize hm : X.arrowEndDim k = m
  induction m using Nat.strong_induction_on generalizing X with
  | h m ih =>
    by_cases hz : X.projectiveClass = 0
    · exact ⟨W.copies 0,isInAdd_copies W 0,by simp [hz]⟩
    obtain ⟨A,r,ha,hlocal⟩ := exists_local_summand k hz
    have har : SAdd A X := IsInAdd.of_retraction _ _ r.retract
    obtain ⟨t⟩ := retract_of_local_stableAdd ha (stableAdd_of_add har h (IsInAdd.refl _))
    obtain ⟨B,s,_,hclass,hlt⟩ := strict_complement k r
    have hB : B.IsInStableAdd W := stableAdd_of_add (IsInAdd.of_retraction _ _ s.retract) h (IsInAdd.refl _)
    obtain ⟨Y,hY,he⟩ := ih _ ((hlt ha).trans_eq hm) B hB rfl
    exact ⟨A.directSum Y,isInAdd_directSum _ _ _ (IsInAdd.of_retraction _ _ t.retract) hY,
      by rw [projectiveClass_directSum,he,hclass]⟩

include k in
private theorem generator_addClassGroup_top {T : TwoTerm R} (ht : T.IsPresilting)
    (hgen : ∀ X : TwoTerm R, InThick T X) : T.addClassGroup = ⊤ := by
  apply top_unique
  intro c _
  have contain (G : FiniteProjective R) : ProjectiveClass.of G ∈ T.addClassGroup := by
    obtain ⟨X,hc,he⟩ := exists_compatible_add_projective k T ht G
    obtain ⟨_,_,h₁,h₂⟩ := (isPresilting_directSum_iff k T X).1 hc
    have hx := Presilting.isInAdd_of_mem_thick _ ((isPresilting_iff_homotopy T).1 ht)
      (hgen X) ((surjective_boundary_iff_homotopy T X).1 ((shiftedHomFinrank_eq_zero_iff k T X).1 h₁))
      ((surjective_boundary_iff_homotopy X T).1 ((shiftedHomFinrank_eq_zero_iff k X T).1 h₂))
    let n := Module.finrank k (T.source ⟶ G.val)
    exact ⟨X,T.copies n,hx,homotopyAdd (isInAdd_copies T n),by
      rw [projectiveClass_copies,he]; dsimp [n]; abel⟩
  obtain ⟨G,H,rfl⟩ := ProjectiveClass.exists_sub c
  exact T.addClassGroup.sub_mem (contain G) (contain H)

include k in
/-- If a positive multiple is represented by a presilting differential D,
the original integral class is represented in add(D). -/
theorem exists_in_add_of_presilting_multiple {D : TwoTerm R} (hd : D.IsPresilting)
    {v : ProjectiveClass R} {n : ℕ} (hn : 0 < n) (he : D.projectiveClass = n • v) :
    ∃ X : TwoTerm R, IsInAdd X.asArrow D.asArrow ∧ X.projectiveClass = v := by
  classical
  obtain ⟨C,ht,hgen,_⟩ := exists_bongartz_generator k D hd
  let T := D.directSum C
  have hv : v ∈ addClassGroup T := by rw [generator_addClassGroup_top k ht hgen]; trivial
  let F (m : ℕ) := ∃ A B : TwoTerm R, HAdd A T ∧ HAdd B T ∧
    v = A.projectiveClass - B.projectiveClass ∧ B.arrowEndDim k = m
  obtain ⟨A₀,B₀,hA₀,hB₀,he₀⟩ := hv
  have hex : ∃ m, F m := ⟨_,A₀,B₀,hA₀,hB₀,he₀,rfl⟩
  obtain ⟨A,B,hA,hB,hv,hmin⟩ := Nat.find_spec hex
  have hDn : HAdd (D.directSum (B.copies n)) T := isInAdd_homotopy_directSum
    (homotopyAdd (leftSummand D C)) ((homotopyAdd (isInAdd_copies B n)).trans hB)
  have hAn := (homotopyAdd (isInAdd_copies A n)).trans hA
  have eqn : (A.copies n).projectiveClass = (D.directSum (B.copies n)).projectiveClass := by
    rw [projectiveClass_directSum,projectiveClass_copies,projectiveClass_copies,he,hv,smul_sub,sub_add_cancel]
  obtain ⟨_,hBA⟩ := isInStableAdd_of_isPresilting_of_class_eq k _ _
    (isPresilting_of_homotopy_isInAdd ht hAn) (isPresilting_of_homotopy_isInAdd ht hDn) eqn
  have hz : B.projectiveClass = 0 := by
    by_contra hb
    obtain ⟨X,r,hx,hlocal⟩ := exists_local_summand k hb
    have hXB := ((IsInAdd.of_retraction _ _ r.retract).trans (isInAdd_of_pos_copies B hn)).trans
      (rightSummand D (B.copies n))
    obtain ⟨t⟩ := retract_of_local_stableAdd hx (stableAdd_of_add hXB hBA (isInAdd_copies A n))
    obtain ⟨B',r',_,hB',hlt⟩ := strict_complement k r
    obtain ⟨A',t',_,hA',_⟩ := strict_complement k t
    have hF : F (B'.arrowEndDim k) := ⟨A',B',
      (homotopyAdd (IsInAdd.of_retraction _ _ t'.retract)).trans hA,
      (homotopyAdd (IsInAdd.of_retraction _ _ r'.retract)).trans hB,by rw [hv,hA',hB']; abel,rfl⟩
    exact (Nat.find_min' hex hF).not_gt ((hlt hx).trans_eq hmin)
  rw [hz,sub_zero] at hv
  have hs := (isInStableAdd_of_isPresilting_of_class_eq k (A.copies n) D
    (isPresilting_of_homotopy_isInAdd ht hAn) hd (by rw [projectiveClass_copies,he,hv])).1
  obtain ⟨Y,hY,hy⟩ := class_in_add_of_stableAdd k A D
    (stableAdd_of_add (isInAdd_of_pos_copies A hn) hs (IsInAdd.refl _))
  exact ⟨Y,hY,hy.trans hv.symm⟩

include k in
/-- The integral points of a presilting cone are exactly the classes of
objects in the additive closure of its generator. -/
theorem mem_gVectorCone_iff_exists_in_add (P : TwoTerm R) (hp : P.IsPresilting) (v : ProjectiveClass R) :
    realProjectiveClass R v ∈ P.gVectorCone ↔
      ∃ Q : TwoTerm R, IsInAdd Q.asArrow P.asArrow ∧ Q.projectiveClass = v := by
  constructor
  · intro hv
    obtain ⟨n,D,hn,hD,he⟩ := exists_multiple_in_add_of_mem_gVectorCone P hv
    obtain ⟨Q,hQ,hv⟩ := exists_in_add_of_presilting_multiple k
      (isPresilting_of_homotopy_isInAdd hp (homotopyAdd hD)) hn he
    exact ⟨Q,hQ.trans hD,hv⟩
  · rintro ⟨Q,hQ,rfl⟩
    exact PointedCone.subset_hull ⟨Q,hQ,rfl⟩

/-- The union of the real two-term presilting cones. -/
def gVectorFanSupport (R : Type u) [Ring R] : Set (RealProjectiveSpace R) :=
  {x | ∃ P : TwoTerm R, P.IsPresilting ∧ x ∈ P.gVectorCone}

include k in
theorem mem_fanSupport_iff_exists_presilting (v : ProjectiveClass R) :
    realProjectiveClass R v ∈ gVectorFanSupport R ↔ ∃ Q : TwoTerm R, Q.IsPresilting ∧ Q.projectiveClass = v := by
  constructor
  · rintro ⟨P,hp,hv⟩
    obtain ⟨Q,hQ,he⟩ := (mem_gVectorCone_iff_exists_in_add k P hp v).1 hv
    exact ⟨Q,isPresilting_of_homotopy_isInAdd hp (homotopyAdd hQ),he⟩
  · rintro ⟨Q,hQ,rfl⟩
    exact ⟨Q,hQ,Q.class_mem_gVectorCone⟩

/-- In any rank it suffices for the depth-j mediants to belong to the real
fan support in order to subdivide the sector into at most 2^j compatible sectors. -/
theorem exists_sector_cover_of_mediants_in_fan (E L : TwoTerm R) (hE : E.IsPresilting)
    (hL : L.IsPresilting) (hEL : E.shiftedHomFinrank k L = 0)
    (hc : ∀ v ∈ sternBrocotMediants (L.shiftedHomFinrank k E) E.projectiveClass L.projectiveClass,
      realProjectiveClass R v ∈ gVectorFanSupport R) :
    ∃ s : List (TwoTerm R × TwoTerm R), s.length ≤ 2 ^ L.shiftedHomFinrank k E ∧
      (∀ p ∈ s, (p.1.directSum p.2).IsPresilting) ∧
      sectorBetween (realProjectiveClass R E.projectiveClass) (realProjectiveClass R L.projectiveClass) =
        {x | ∃ p ∈ s, x ∈ sectorBetween (realProjectiveClass R p.1.projectiveClass)
          (realProjectiveClass R p.2.projectiveClass)} :=
  exists_presilting_sector_cover_of_mediants k _ _ E L hE hL hEL le_rfl
    (fun v hv ↦ (mem_fanSupport_iff_exists_presilting k v).1 (hc v hv))

end EFiniteCharacterizations.TwoTerm
