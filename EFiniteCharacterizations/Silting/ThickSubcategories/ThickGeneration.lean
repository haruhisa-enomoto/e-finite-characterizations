module

public import EFiniteCharacterizations.Presentations.BlockPresentation
public import EFiniteCharacterizations.Presentations.TwoTermFitting
public import EFiniteCharacterizations.Presentations.FittingPresentation

/-! # Presilting generators of two-term thick subcategories -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R] [IsNoetherianRing R]
private abbrev K := HomotopyCategory (FGModuleCat.{u} R) (ComplexShape.up ℤ)

private def represented (H : TwoTerm R → Prop) : ObjectProperty (K (R := R)) :=
  fun X ↦ ∃ P : TwoTerm R, H P ∧ Nonempty (X ≅ P.homotopyObject)

private instance (H : TwoTerm R → Prop) : (represented H).IsClosedUnderIsomorphisms where
  of_iso j := by rintro ⟨P,hP,⟨i⟩⟩; exact ⟨P,hP,⟨j.symm ≪≫ i⟩⟩

private theorem represented_ext {H : TwoTerm R → Prop} (hH : IsTwoTermThick H) :
    (represented H).IsTriangulatedClosed₂ := by
  apply ObjectProperty.IsTriangulatedClosed₂.mk'
  rintro T ht ⟨P,hP,⟨i⟩⟩ ⟨Q,hQ,⟨j⟩⟩
  obtain ⟨w,e⟩ := exists_iso_blockExtension P Q ht i j
  exact ⟨P.blockExtension Q w, ((hH.triangles P (P.blockExtension Q w) Q _ _ _ (blockTriangle_distinguished P Q w)).1 hP).2 hQ,e⟩

set_option backward.isDefEq.respectTransparency false in
private theorem mem_fitting_retract {H : TwoTerm R → Prop} (hH : IsTwoTermThick H)
    (W V Y N : TwoTerm R) (hY : H Y)
    (f : W.homotopyObject ⟶ W.homotopyObject ⊞ V.homotopyObject)
    (p : W.homotopyObject ⊞ V.homotopyObject ⟶ Y.homotopyObject)
    (δ : Y.homotopyObject ⟶ W.homotopyObject⟦(1 : ℤ)⟧) (ht : Triangle.mk f p δ ∈ distTriang _)
    (r : Retract N.homotopyObject W.homotopyObject) (m : ℕ) (a : End W.homotopyObject)
    (ha : a = f ≫ biprod.fst) (hm : (a ^ m : End W.homotopyObject) ≫ r.r = 0) : H N := by
  let A := represented H
  let B := A.retractClosure
  have : A.IsTriangulatedClosed₂ := represented_ext hH
  have : B.IsTriangulatedClosed₂ := Presilting.extension_closed_retractClosure A
  have : B.ContainsZero := by
    let O := contractible (ProjectiveClass.zeroProjective R)
    exact ⟨O.homotopyObject,isZero_contractible _,ObjectProperty.le_retractClosure A _
      (show A O.homotopyObject from ⟨O,hH.zero,⟨Iso.refl _⟩⟩)⟩
  have hf : B.trW f := ⟨Y.homotopyObject,p,δ,ht,ObjectProperty.le_retractClosure A _
    (show A Y.homotopyObject from ⟨Y,hY,⟨Iso.refl _⟩⟩)⟩
  have hN := Presilting.mem_retract_of_component_power B f biprod.fst biprod.inl biprod.inl_fst hf r m
    (by subst a; exact hm)
  obtain ⟨X,⟨P,hP,⟨i⟩⟩,⟨j⟩⟩ := hN
  exact hH.retracts N P (j.trans i.retract) hP

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
/-- Any presilting member maximal for adjoining compatible members generates H. -/
theorem inThick_iff_of_maximal_presilting (he : IsEFinite R) {H : TwoTerm R → Prop}
    (hH : IsTwoTermThick H) (U : TwoTerm R) (hU : H U) (hu : U.IsPresilting)
    (hmax : ∀ P : TwoTerm R, H P → (U.directSum P).IsPresilting → IsInAdd P.homotopyObject U.homotopyObject) :
    ∀ X : TwoTerm R, H X ↔ InThick U X := by
  apply inThick_iff_of_orthogonal_inAdd k U hu hH.triangles hU (fun Y h ↦ hH.of_inAdd Y U hU h)
  obtain ⟨B,ht,hgen,horth⟩ := exists_bongartz_generator k U hu
  let T := U.directSum B
  let G := doubleFunctor (C := FGModuleCat.{u} R) ⋙ HomotopyCategory.quotient _ _
  have hUT : IsInAdd U.homotopyObject T.homotopyObject :=
    (IsInAdd.of_retraction _ _ (inlDirectSum_fstDirectSum U B)).map G
  intro Y hY hUY hYU
  obtain ⟨V,hVmem,hv,hc,hUV,hVU⟩ := exists_presilting_in_orthogonal_of_isEFinite k he
    hH.triangles hH.retracts U Y hY hUY hYU
  have hV := hmax V hVmem ((isPresilting_directSum_iff k U V).2
    ⟨hu,hv,(shiftedHomFinrank_eq_zero_iff k U V).2 hUV,(shiftedHomFinrank_eq_zero_iff k V U).2 hVU⟩)
  obtain ⟨n,f,p,δ,hf⟩ := exists_biprod_presentation k T Y V ht hgen (horth Y hUY) (hV.trans hUT) hc.symm
  let W := T.copies n
  let a : End W.homotopyObject := f ≫ biprod.fst
  obtain ⟨N,r,c,m,hm,hcomm,htotal⟩ := exists_fitting_retract k W a
  have hn := mem_fitting_retract hH W V Y N hY f p δ hf r m a rfl hm
  have hNT : IsInAdd N.homotopyObject T.homotopyObject :=
    (IsInAdd.of_retraction _ _ r.retract).trans ((isInAdd_copies T n).map G)
  have hNU := hmax N hn (isPresilting_of_homotopy_isInAdd ht (isInAdd_homotopy_directSum hUT hNT))
  have hz := subsingleton_to_add (hNU.map (shiftFunctor _ (1 : ℤ)))
    ((surjective_boundary_iff_homotopy Y U).1 hYU 1 (by decide))
  exact Presilting.isInAdd_of_biprod_presentation f p δ hf r.r r.i c hcomm htotal hz hNU hV

include k in
/-- Over an E-finite algebra, every two-term thick subcategory is the two-term
part of the ambient thick closure of a presilting object. -/
theorem exists_presilting_thick_generator (he : IsEFinite R) {H : TwoTerm R → Prop} (hH : IsTwoTermThick H) :
    ∃ U : TwoTerm R, H U ∧ U.IsPresilting ∧ ∀ X : TwoTerm R, H X ↔ InThick U X := by
  obtain ⟨U,hU,hu,hmax⟩ := exists_maximal_presilting k hH
  exact ⟨U,hU,hu,inThick_iff_of_maximal_presilting k he hH U hU hu hmax⟩

/-- A basic decomposition lists pairwise nonisomorphic indecomposables whose
direct sum represents U in the homotopy category. -/
def BasicDecomposition (U : TwoTerm R) (l : List (HomotopyCategory (FGModuleCat.{u} R) (ComplexShape.up ℤ))) : Prop :=
  (∀ D ∈ l, Indecomposable D) ∧ l.Pairwise (fun X Y ↦ ¬ Nonempty (X ≅ Y)) ∧
    Nonempty (U.homotopyObject ≅ l.foldr (fun X Y ↦ X ⊞ Y) ((contractible (ProjectiveClass.zeroProjective R)).homotopyObject))

private theorem inAdd_list_sum {D : K (R := R)} (l : List (HomotopyCategory (FGModuleCat.{u} R) (ComplexShape.up ℤ))) (h : D ∈ l) :
    IsInAdd D (l.foldr (fun X Y ↦ X ⊞ Y) ((contractible (ProjectiveClass.zeroProjective R)).homotopyObject)) := by
  induction l with
  | nil => simp at h
  | cons A l ih =>
    rcases List.mem_cons.mp h with rfl | hh
    · exact IsInAdd.of_retraction biprod.inl biprod.fst (by simp)
    · exact (ih hh).trans (IsInAdd.of_retraction biprod.inr biprod.snd (by simp))

theorem basicDecomposition_cons_of_not_inAdd {U V : TwoTerm R} {l} (hl : BasicDecomposition U l)
    (hv : Indecomposable V.homotopyObject) (hvu : ¬ IsInAdd V.homotopyObject U.homotopyObject) :
    BasicDecomposition (V.directSum U) (V.homotopyObject :: l) := by
  obtain ⟨hind,hpair,⟨e⟩⟩ := hl
  refine ⟨fun D hD ↦ ?_,List.pairwise_cons.mpr ⟨?_,hpair⟩,
    ⟨directSumHomotopyIso V U ≪≫ biprod.mapIso (Iso.refl _) e⟩⟩
  · rcases List.mem_cons.mp hD with rfl | hh
    · exact hv
    · exact hind D hh
  · intro D hD hiso
    obtain ⟨i⟩ := hiso
    exact hvu ((IsInAdd.of_retraction _ _ i.hom_inv_id).trans
      ((inAdd_list_sum l hD).trans (IsInAdd.of_retraction _ _ e.inv_hom_id)))

include k in
/-- A basic presilting complex with the largest number of indecomposable
summands among basic presilting members of H generates H. -/
theorem inThick_iff_of_maximum_summands (he : IsEFinite R) {H : TwoTerm R → Prop}
    (hH : IsTwoTermThick H) (U : TwoTerm R) (hU : H U) (hu : U.IsPresilting)
    (l : List (HomotopyCategory (FGModuleCat.{u} R) (ComplexShape.up ℤ))) (hl : BasicDecomposition U l)
    (hmax : ∀ (T : TwoTerm R) (t : List (HomotopyCategory (FGModuleCat.{u} R) (ComplexShape.up ℤ))), H T → T.IsPresilting →
      BasicDecomposition T t → t.length ≤ l.length) :
    ∀ X : TwoTerm R, H X ↔ InThick U X := by
  apply inThick_iff_of_maximal_presilting k he hH U hU hu
  intro P hP hUP
  by_contra ho
  obtain ⟨V,hv,⟨r⟩,hvu⟩ := exists_indecomposable_outside_add k P U ho
  let T := V.directSum U
  have hV := hH.retracts V P r hP
  have ht : H T := ((hH.triangles V T U _ _ _ (blockTriangle_distinguished V U 0)).1 hV).2 hU
  let j := directSumHomotopyIso U P
  have hta : IsInAdd T.homotopyObject (U.directSum P).homotopyObject :=
    isInAdd_homotopy_directSum
      ((IsInAdd.of_retraction _ _ r.retract).trans ((IsInAdd.of_retraction biprod.inr biprod.snd
        (by simp)).trans (IsInAdd.of_retraction _ _ j.inv_hom_id)))
      ((IsInAdd.of_retraction biprod.inl biprod.fst (by simp)).trans (IsInAdd.of_retraction _ _ j.inv_hom_id))
  have htb := basicDecomposition_cons_of_not_inAdd hl hv hvu
  simpa using hmax T _ ht (isPresilting_of_homotopy_isInAdd hUP hta) htb

private theorem retract_iso_of_indecomposable {X D : K (R := R)} (hX : ¬ IsZero X)
    (hD : Indecomposable D) (r : Retract X D) : Nonempty (X ≅ D) := by
  obtain ⟨Z,g,d,ht⟩ := distinguished_cocone_triangle r.i
  have hm : Mono r.i := ⟨fun _ _ h ↦ by simpa [Category.assoc,r.retract] using congrArg (fun z ↦ z ≫ r.r) h⟩
  obtain ⟨e,_,_⟩ := exists_iso_binaryBiproduct_of_distTriang _ ht
    (Triangle.mor₃_eq_zero_of_mono₁ _ ht hm)
  have hz := (hD.2 X Z e).resolve_left hX
  let j : X ≅ X ⊞ Z := ⟨biprod.inl,biprod.fst,by simp,by
    have h := biprod.total (X := X) (Y := Z)
    simpa [hz.eq_of_src (biprod.inr : Z ⟶ X ⊞ Z) 0] using h⟩
  exact ⟨j ≪≫ e.symm⟩

private theorem unit_list_summand {S : Type*} [Ring S] [IsLocalRing S] (l : List S)
    (h : IsUnit l.sum) : ∃ a ∈ l, IsUnit a := by
  induction l with
  | nil => exact (not_isUnit_zero h).elim
  | cons a l ih =>
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with ha | hl
    · exact ⟨a,List.mem_cons_self,ha⟩
    · obtain ⟨b,hb,hu⟩ := ih hl
      exact ⟨b,List.mem_cons_of_mem _ hb,hu⟩

private noncomputable abbrev listSum (l : List (K (R := R))) :=
  l.foldr (fun X Y ↦ X ⊞ Y) ((contractible (ProjectiveClass.zeroProjective R)).homotopyObject)

set_option backward.isDefEq.respectTransparency false in
private theorem iso_mem_of_add_list_local {X : TwoTerm R} [IsLocalRing (End X.homotopyObject)] (hx : ¬ IsZero X.homotopyObject)
    (l : List (K (R := R))) (hl : ∀ D ∈ l, Indecomposable D)
    (ha : IsInAdd X.homotopyObject (listSum l)) : ∃ D ∈ l, Nonempty (X.homotopyObject ≅ D) := by
  obtain ⟨rr⟩ : Nonempty (Retract X.homotopyObject (listSum l)) := by
    obtain ⟨pairs,hpairs⟩ := ha
    let vs : List (End X.homotopyObject) := pairs.map (fun p ↦ p.1 ≫ p.2)
    have hsum : vs.sum = 1 := hpairs
    obtain ⟨v,hv,hu⟩ := unit_list_summand vs (hsum ▸ isUnit_one)
    obtain ⟨⟨a,b⟩,_,rfl⟩ := List.mem_map.mp hv
    have : IsIso (a ≫ b) := (isUnit_iff_isIso _).mp hu
    exact ⟨⟨inv (a ≫ b) ≫ a,b,by simp⟩⟩
  clear ha
  induction l with
  | nil =>
    change Retract X.homotopyObject ((contractible (ProjectiveClass.zeroProjective R)).homotopyObject) at rr
    apply (hx ((IsZero.iff_id_eq_zero _).2 ?_)).elim
    exact rr.retract.symm.trans (by rw [(isZero_contractible _).eq_of_tgt rr.i 0,zero_comp])
  | cons D l ih =>
    change Retract X.homotopyObject (D ⊞ listSum l) at rr
    let a := rr.i ≫ biprod.fst
    let b := biprod.inl ≫ rr.r
    let c := rr.i ≫ biprod.snd
    let d := biprod.inr ≫ rr.r
    have ht : (a ≫ b) + (c ≫ d) = 𝟙 X.homotopyObject := by
      simpa only [a,b,c,d,Preadditive.add_comp,Preadditive.comp_add,Category.assoc,Category.id_comp,rr.retract]
        using congrArg (fun z ↦ rr.i ≫ z ≫ rr.r) (biprod.total (X := D) (Y := listSum l))
    let x : End X.homotopyObject := a ≫ b
    let y : End X.homotopyObject := c ≫ d
    change x + y = 1 at ht
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (ht ▸ isUnit_one) with h | h
    · have : IsIso (a ≫ b) := (isUnit_iff_isIso _).mp h
      exact ⟨D,List.mem_cons_self,retract_iso_of_indecomposable hx (hl D List.mem_cons_self)
        ⟨inv (a ≫ b) ≫ a,b,by simp⟩⟩
    · have : IsIso (c ≫ d) := (isUnit_iff_isIso _).mp h
      obtain ⟨A,hA,hiso⟩ := ih (fun A hA ↦ hl A (List.mem_cons_of_mem _ hA))
        ⟨inv (c ≫ d) ≫ c,d,by simp⟩
      exact ⟨A,List.mem_cons_of_mem _ hA,hiso⟩

include k in
private theorem iso_mem_of_add_list {X : TwoTerm R} (hx : Indecomposable X.homotopyObject)
    (l : List (K (R := R))) (hl : ∀ D ∈ l, Indecomposable D)
    (ha : IsInAdd X.homotopyObject (listSum l)) : ∃ D ∈ l, Nonempty (X.homotopyObject ≅ D) := by
  let _ := isLocalRing_homotopy_end k X hx
  exact iso_mem_of_add_list_local hx.1 l hl ha

/-- A nonzero homotopy summand with local endomorphism ring occurs in
any prescribed basic decomposition of its additive generator. -/
theorem iso_mem_basic_of_local {X P : TwoTerm R} [IsLocalRing (End X.homotopyObject)]
    (hx : ¬ IsZero X.homotopyObject) {l} (hl : BasicDecomposition P l)
    (ha : IsInAdd X.homotopyObject P.homotopyObject) : ∃ D ∈ l, Nonempty (X.homotopyObject ≅ D) := by
  obtain ⟨e⟩ := hl.2.2
  exact iso_mem_of_add_list_local hx l hl.1 (ha.trans (IsInAdd.of_retraction _ _ e.hom_inv_id))

private theorem retract_listSum_of_mem {D : K (R := R)} {l : List (K (R := R))} (hd : D ∈ l) :
    Nonempty (Retract D (listSum l)) := by
  induction l with
  | nil => simp at hd
  | cons X l ih =>
    rcases List.mem_cons.mp hd with rfl | h
    · exact ⟨⟨biprod.inl, biprod.fst, by simp⟩⟩
    · obtain ⟨r⟩ := ih h
      exact ⟨r.trans ⟨biprod.inr, biprod.snd, by simp⟩⟩

include k in
private theorem basic_summand_classes_subset {U V : TwoTerm R} {l t : List (K (R := R))}
    (hl : BasicDecomposition U l) (ht : BasicDecomposition V t)
    (hUV : IsInAdd U.homotopyObject V.homotopyObject) :
    l.map toSkeleton ⊆ t.map toSkeleton := by
  intro c hc
  obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hc
  obtain ⟨e⟩ := hl.2.2
  obtain ⟨r⟩ := retract_listSum_of_mem hD
  let rU := r.trans e.symm.retract
  obtain ⟨P,⟨p⟩⟩ := exists_twoTerm_iso_of_retract k U rU
  obtain ⟨j⟩ := ht.2.2
  have hind := hl.1 D hD
  have hP : Indecomposable P.homotopyObject :=
    ⟨fun hz ↦ hind.1 (hz.of_iso p), fun A B f ↦ hind.2 A B (p ≪≫ f)⟩
  have ha := (IsInAdd.of_retraction _ _ (p.symm.retract.trans rU).retract).trans
    (hUV.trans (IsInAdd.of_retraction _ _ j.hom_inv_id))
  obtain ⟨A,hA,⟨i⟩⟩ := iso_mem_of_add_list k hP t ht.1 ha
  exact List.mem_map.mpr ⟨A,hA,congr_toSkeleton_of_iso (p ≪≫ i).symm⟩

private theorem iso_listSum_of_perm {l t : List (K (R := R))} (h : l.Perm t) :
    Nonempty (listSum l ≅ listSum t) := by
  induction h with
  | nil => exact ⟨Iso.refl _⟩
  | cons X _ ih => exact ⟨biprod.mapIso (Iso.refl X) ih.some⟩
  | swap X Y l =>
    exact ⟨(biprod.associator _ _ _).symm ≪≫ biprod.mapIso (biprod.braiding _ _) (Iso.refl _) ≪≫
      biprod.associator _ _ _⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.some ≪≫ ih₂.some⟩

private theorem iso_listSum_canonical (l : List (K (R := R))) :
    Nonempty (listSum l ≅ listSum ((l.map toSkeleton).map (fromSkeleton _).obj)) := by
  induction l with
  | nil => exact ⟨Iso.refl _⟩
  | cons X l ih => exact ⟨biprod.mapIso (fromSkeletonToSkeletonIso X).symm ih.some⟩

include k in
/-- Basic two-term complexes with the same additive closure are isomorphic
in the homotopy category. -/
theorem iso_of_basic_mutual_add {U V : TwoTerm R} {l t : List (HomotopyCategory (FGModuleCat.{u} R) (ComplexShape.up ℤ))}
    (hl : BasicDecomposition U l) (ht : BasicDecomposition V t)
    (hUV : IsInAdd U.homotopyObject V.homotopyObject) (hVU : IsInAdd V.homotopyObject U.homotopyObject) :
    Nonempty (U.homotopyObject ≅ V.homotopyObject) := by
  have nd (T : TwoTerm R) (a : List (K (R := R))) (ha : BasicDecomposition T a) :
      (a.map toSkeleton).Nodup :=
    List.pairwise_map.mpr (ha.2.1.imp fun h eq ↦ h ⟨Skeleton.isoOfEq eq⟩)
  have hperm := (List.perm_ext_iff_of_nodup (nd U l hl) (nd V t ht)).2
    (fun c ↦ ⟨fun h ↦ basic_summand_classes_subset k hl ht hUV h,
      fun h ↦ basic_summand_classes_subset k ht hl hVU h⟩)
  exact ⟨hl.2.2.some ≪≫ (iso_listSum_canonical l).some ≪≫
    (iso_listSum_of_perm (hperm.map (fromSkeleton _).obj)).some ≪≫
    (iso_listSum_canonical t).some.symm ≪≫ ht.2.2.some.symm⟩

set_option backward.isDefEq.respectTransparency false in
include k in
theorem independent_basic_family (U : TwoTerm R) (hu : U.IsPresilting)
    (l : List (HomotopyCategory (FGModuleCat.{u} R) (ComplexShape.up ℤ))) (hl : BasicDecomposition U l) :
    ∃ a : Fin l.length → TwoTerm R, (∀ i, IsInAdd (a i).homotopyObject U.homotopyObject) ∧
      LinearIndependent ℤ (fun i ↦ (a i).projectiveClass) := by
  induction l generalizing U with
  | nil => simp only [List.length_nil]; exact ⟨Fin.elim0,fun i ↦ i.elim0,linearIndependent_empty_type⟩
  | cons D l ih =>
    obtain ⟨hind,hpair,⟨e⟩⟩ := hl
    change U.homotopyObject ≅ D ⊞ listSum l at e
    let r : Retract D U.homotopyObject := ⟨biprod.inl ≫ e.inv,e.hom ≫ biprod.fst,by simp⟩
    let s : Retract (listSum l) U.homotopyObject := ⟨biprod.inr ≫ e.inv,e.hom ≫ biprod.snd,by simp⟩
    obtain ⟨P,⟨p⟩⟩ := exists_twoTerm_iso_of_retract k U r
    obtain ⟨T,⟨t⟩⟩ := exists_twoTerm_iso_of_retract k U s
    have hpU := IsInAdd.of_retraction _ _ (p.symm.retract.trans r).retract
    have htU := IsInAdd.of_retraction _ _ (t.symm.retract.trans s).retract
    have htail : ∀ A ∈ l, Indecomposable A := fun A hA ↦ hind A (List.mem_cons_of_mem _ hA)
    have hP : Indecomposable P.homotopyObject :=
      ⟨fun hz ↦ (hind D List.mem_cons_self).1 (hz.of_iso p),
        fun A B j ↦ (hind D List.mem_cons_self).2 A B (p ≪≫ j)⟩
    obtain ⟨a,ha,hi⟩ := ih T (isPresilting_of_homotopy_isInAdd hu htU)
      ⟨htail,(List.pairwise_cons.mp hpair).2,⟨t.symm⟩⟩
    have hn : ¬ IsInAdd P.homotopyObject T.homotopyObject := by
      intro h
      obtain ⟨A,hA,⟨j⟩⟩ := iso_mem_of_add_list k hP l htail (h.trans (IsInAdd.of_retraction _ _ t.inv_hom_id))
      exact (List.pairwise_cons.mp hpair).1 A hA ⟨p ≪≫ j⟩
    exact ⟨Fin.cons P a,Fin.cases hpU (fun i ↦ (ha i).trans htU),
      independent_cons_of_not_inAdd k (isPresilting_of_homotopy_isInAdd hu
        (isInAdd_homotopy_directSum htU hpU)) hn a ha hi⟩

include k in
/-- A basic two-term presilting complex has at most as many summands as
there are isomorphism classes of simple modules. -/
theorem basicDecomposition_length_le (U : TwoTerm R) (hu : U.IsPresilting) {l}
    (hl : BasicDecomposition U l) : l.length ≤ (simpleIsomorphismClasses R).ncard := by
  obtain ⟨a,_,hi⟩ := independent_basic_family k U hu l hl
  exact projectiveFamily_bound k a hi

include k in
/-- Every presilting complex has a basic representative of its additive closure. -/
theorem exists_basic_add_generator (T : TwoTerm R) (ht : T.IsPresilting) :
    ∃ (U : TwoTerm R), ∃ l, BasicDecomposition U l ∧ IsInAdd U.homotopyObject T.homotopyObject ∧
      IsInAdd T.homotopyObject U.homotopyObject := by
  classical
  let family (n : ℕ) := ∃ (U : TwoTerm R), ∃ l, BasicDecomposition U l ∧
    IsInAdd U.homotopyObject T.homotopyObject ∧ l.length = n
  let Z := contractible (ProjectiveClass.zeroProjective R)
  have hz : family 0 := ⟨Z,[],⟨by simp,by simp,⟨Iso.refl _⟩⟩,
    ⟨[],(isZero_contractible _).eq_of_src _ _⟩,rfl⟩
  let n := (simpleIsomorphismClasses R).ncard
  obtain ⟨U,l,hl,ha,hn⟩ := (Nat.findGreatest_spec (Nat.zero_le n) hz : family (Nat.findGreatest family n))
  refine ⟨U,l,hl,ha,?_⟩
  by_contra h
  obtain ⟨V,hv,⟨r⟩,hvu⟩ := exists_indecomposable_outside_add k T U h
  have hm := basicDecomposition_cons_of_not_inAdd hl hv hvu
  have hadd := isInAdd_homotopy_directSum (IsInAdd.of_retraction _ _ r.retract) ha
  have hbound := basicDecomposition_length_le k _ (isPresilting_of_homotopy_isInAdd ht hadd) hm
  have hle := Nat.le_findGreatest hbound (show family (V.homotopyObject :: l).length from
    ⟨_,_,hm,hadd,rfl⟩)
  change l.length + 1 ≤ Nat.findGreatest family n at hle
  omega

include k in
/-- A largest basic presilting member exists in every two-term thick subcategory. -/
theorem exists_maximum_basic_presilting {H : TwoTerm R → Prop} (hH : IsTwoTermThick H) :
    ∃ U l, H U ∧ U.IsPresilting ∧ BasicDecomposition U l ∧
      ∀ T t, H T → T.IsPresilting → BasicDecomposition T t → t.length ≤ l.length := by
  classical
  let family (n : ℕ) := ∃ U l, H U ∧ U.IsPresilting ∧ BasicDecomposition U l ∧ l.length = n
  let Z := contractible (ProjectiveClass.zeroProjective R)
  have hz : Z.IsPresilting := (shiftedHomFinrank_eq_zero_iff k Z Z).1
    (shiftedHomFinrank_contractible_target k _ _)
  have hzero : family 0 := ⟨Z,[],hH.zero,hz,⟨by simp,by simp,⟨Iso.refl _⟩⟩,rfl⟩
  let bound := (simpleIsomorphismClasses R).ncard
  obtain ⟨U,l,hU,hu,hl,hn⟩ := (Nat.findGreatest_spec (Nat.zero_le bound) hzero :
    family (Nat.findGreatest family bound))
  refine ⟨U,l,hU,hu,hl,fun T t hT ht hd ↦ ?_⟩
  rw [hn]
  exact Nat.le_findGreatest (basicDecomposition_length_le k T ht hd) (show family t.length from
    ⟨T,t,hT,ht,hd,rfl⟩)

end EFiniteCharacterizations.TwoTerm
