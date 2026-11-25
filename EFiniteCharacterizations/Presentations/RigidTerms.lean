module

public import EFiniteCharacterizations.Presentations.RigidPowers
public import EFiniteCharacterizations.Presentations.FinitePresiltingCokernels

/-! # Representatives of presilting objects on prescribed projective terms -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u
namespace EFiniteCharacterizations.TwoTerm

private theorem unit_add_nonunit {A : Type*} [Ring A] [IsLocalRing A] {a b : A}
    (ha : IsUnit a) (hb : ¬ IsUnit b) : IsUnit (a+b) := by
  have h : IsUnit ((a+b) + -b) := by simpa using ha
  exact (IsLocalRing.isUnit_or_isUnit_of_isUnit_add h).resolve_right (by simpa using hb)

section
variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
variable {T X Y : C} [IsLocalRing (End T)]

private theorem source_pivot (f : T ⊞ X ⟶ T ⊞ Y)
    (h0 : ¬ IsUnit (M := End T) (biprod.inl ≫ f ≫ biprod.fst : End T))
    (v : T ⟶ T ⊞ X) (hv : IsUnit (M := End T) (v ≫ f ≫ biprod.fst : End T)) :
    ∃ L : T ⊞ X ≅ T ⊞ X, IsIso (biprod.inl ≫ L.hom ≫ f ≫ biprod.fst) := by
  have good : ∃ w : T ⟶ T ⊞ X, IsUnit (M := End T) (w ≫ biprod.fst : End T) ∧
      IsUnit (M := End T) (w ≫ f ≫ biprod.fst : End T) := by
    by_cases h : IsUnit (M := End T) (v ≫ biprod.fst : End T)
    · exact ⟨v,h,hv⟩
    · refine ⟨biprod.inl + v,?_,?_⟩
      · rw [Preadditive.add_comp,biprod.inl_fst]
        exact unit_add_nonunit (a := (1 : End T)) isUnit_one h
      · rw [Preadditive.add_comp,add_comm]
        exact unit_add_nonunit hv h0
  obtain ⟨w,ha,hb⟩ := good
  have : IsIso (w ≫ biprod.fst) := (isUnit_iff_isIso _).1 ha
  let a := asIso (w ≫ biprod.fst)
  let L := biprod.mapIso a (Iso.refl X) ≪≫ Biprod.unipotentUpper (a.inv ≫ w ≫ biprod.snd)
  have he : biprod.inl ≫ L.hom = w := by
    apply biprod.hom_ext <;> simp [L,Category.assoc,a,Biprod.unipotentUpper]
  refine ⟨L,?_⟩
  rw [← Category.assoc,he]
  exact (isUnit_iff_isIso _).1 hb

private theorem target_pivot (f : T ⊞ X ⟶ T ⊞ Y)
    (h0 : ¬ IsUnit (M := End T) (biprod.inl ≫ f ≫ biprod.fst))
    (v : T ⊞ Y ⟶ T) (hv : IsUnit (M := End T) (biprod.inl ≫ f ≫ v)) :
    ∃ P : T ⊞ Y ≅ T ⊞ Y, IsIso (biprod.inl ≫ f ≫ P.hom ≫ biprod.fst) := by
  have good : ∃ w : T ⊞ Y ⟶ T, IsUnit (M := End T) (biprod.inl ≫ w) ∧
      IsUnit (M := End T) (biprod.inl ≫ f ≫ w) := by
    by_cases h : IsUnit (M := End T) (biprod.inl ≫ v)
    · exact ⟨v,h,hv⟩
    · refine ⟨biprod.fst + v,?_,?_⟩
      · rw [Preadditive.comp_add,biprod.inl_fst]
        exact unit_add_nonunit (a := (1 : End T)) isUnit_one h
      · rw [Preadditive.comp_add,Preadditive.comp_add,add_comm]
        exact unit_add_nonunit hv h0
  obtain ⟨w,ha,hb⟩ := good
  have : IsIso (biprod.inl ≫ w) := (isUnit_iff_isIso _).1 ha
  let a := asIso (biprod.inl ≫ w)
  let P := Biprod.unipotentLower (biprod.inr ≫ w ≫ a.inv) ≪≫ biprod.mapIso a (Iso.refl Y)
  have hp : P.hom ≫ biprod.fst = w := by
    apply biprod.hom_ext' <;> simp [P,Category.assoc,a,Biprod.unipotentLower,Biprod.ofComponents]
  exact ⟨P,hp ▸ (isUnit_iff_isIso _).1 hb⟩

private theorem split_rigid_block (k : Type*) [Field k] [Linear k C]
    (f : T ⊞ X ⟶ T ⊞ Y) (hf : Function.Surjective (boundaryLinear k f f)) :
    ∃ (g : X ⟶ Y), Nonempty (Arrow.mk f ≅ Arrow.mk (biprod.map (𝟙 T) g)) := by
  have pivot : ∃ (L : T ⊞ X ≅ T ⊞ X) (P : T ⊞ Y ≅ T ⊞ Y),
      IsIso (biprod.inl ≫ L.hom ≫ f ≫ P.hom ≫ biprod.fst) := by
    by_cases h : IsUnit (M := End T) (biprod.inl ≫ f ≫ biprod.fst)
    · exact ⟨Iso.refl _,Iso.refl _,by simpa using (isUnit_iff_isIso _).1 h⟩
    obtain ⟨⟨a,b⟩,hab⟩ := hf (biprod.fst ≫ biprod.inl)
    let x : End T := (biprod.inl ≫ a) ≫ f ≫ biprod.fst
    let y : End T := biprod.inl ≫ f ≫ b ≫ biprod.fst
    have hh : x - y = 1 := by
      have eq := congrArg (fun z ↦ biprod.inl ≫ z ≫ biprod.fst) hab
      simpa [x,y,boundaryLinear_apply,Preadditive.sub_comp,Preadditive.comp_sub,Category.assoc] using eq
    rw [sub_eq_add_neg] at hh
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (hh ▸ isUnit_one) with hx | hy
    · obtain ⟨L,hL⟩ := source_pivot f h _ hx
      exact ⟨L,Iso.refl _,by simpa using hL⟩
    · obtain ⟨P,hP⟩ := target_pivot f h (b ≫ biprod.fst) (by simpa using hy)
      exact ⟨Iso.refl _,P,by simpa using hP⟩
  obtain ⟨L,P,hi⟩ := pivot
  let d := L.hom ≫ f ≫ P.hom
  let t := biprod.inl ≫ d ≫ biprod.fst
  have : IsIso t := by simpa [t,d,Category.assoc] using hi
  obtain ⟨L',P',g,hg⟩ := Biprod.gaussian d
  let v := biprod.mapIso (asIso t).symm (Iso.refl Y)
  refine ⟨g,⟨(Arrow.isoMk' f d L.symm P (by simp [d])) ≪≫
    (Arrow.isoMk' d (biprod.map t g) L'.symm P' ?_) ≪≫ (Arrow.isoMk' _ _ (Iso.refl _) v ?_)⟩⟩
  · rw [← hg]; simp
  · change (𝟙 _) ≫ biprod.map (𝟙 T) g = biprod.map t g ≫ v.hom
    apply biprod.hom_ext <;> simp [v,Category.assoc]

end
section
variable {C : Type*} [Category* C] [Preadditive C] (k : Type*) [Field k] [Linear k C]

private abbrev RigidOn (X Y : C) := ∃ f : X ⟶ Y, Function.Surjective (boundaryLinear k f f)

private theorem rigid_of_arrow_iso {X Y A B : C} {f : X ⟶ Y} {g : A ⟶ B}
    (e : Arrow.mk f ≅ Arrow.mk g) (h : Function.Surjective (boundaryLinear k f f)) :
    Function.Surjective (boundaryLinear k g g) := by
  intro w
  let s : X ≅ A := Arrow.leftFunc.mapIso e
  let t : Y ≅ B := Arrow.rightFunc.mapIso e
  have hc : s.hom ≫ g = f ≫ t.hom := e.hom.w
  obtain ⟨⟨a,b⟩,hab⟩ := h (s.hom ≫ w ≫ t.inv)
  refine ⟨(s.inv ≫ a ≫ s.hom,t.inv ≫ b ≫ t.hom),?_⟩
  have hh := congrArg (fun z ↦ s.inv ≫ z ≫ t.hom) hab
  have hinv : s.inv ≫ f = g ≫ t.inv := e.inv.w
  simp only [boundaryLinear_apply,Preadditive.sub_comp,Preadditive.comp_sub,Category.assoc,
    Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id] at hh ⊢
  rw [hc,← reassoc_of% hinv]
  exact hh

private theorem RigidOn.transport {X Y A B : C} (h : RigidOn k X Y) (s : X ≅ A) (t : Y ≅ B) :
    RigidOn k A B := by
  obtain ⟨f,hf⟩ := h
  let g := s.inv ≫ f ≫ t.hom
  exact ⟨g,rigid_of_arrow_iso k (Arrow.isoMk' f g s t (by simp [g])) hf⟩

end
variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

private theorem remove_common_terms (T X Y : FGModuleCat.{u} R)
    (h : RigidOn k (T ⊞ X) (T ⊞ Y)) : RigidOn k X Y := by
  classical
  generalize hn : Module.finrank k (T.obj : Type u) = n
  induction n using Nat.strong_induction_on generalizing T X Y with
  | h n ih =>
    by_cases hz : IsZero T
    · exact RigidOn.transport k h (biprod.braiding _ _ ≪≫ (isoBiprodZero hz).symm)
        (biprod.braiding _ _ ≪≫ (isoBiprodZero hz).symm)
    by_cases ht : Indecomposable T
    · let := FGModuleCat.isLocalRing_end_of_indecomposable ht
      obtain ⟨f,hf⟩ := h
      obtain ⟨g,⟨e⟩⟩ := split_rigid_block k f hf
      have hg := rigid_of_arrow_iso k e hf
      refine ⟨g,fun w ↦ ?_⟩
      obtain ⟨⟨a,b⟩,hab⟩ := hg (biprod.snd ≫ w ≫ biprod.inr)
      refine ⟨(biprod.inr ≫ a ≫ biprod.snd,biprod.inr ≫ b ≫ biprod.snd),?_⟩
      have eq := congrArg (fun z ↦ biprod.inr ≫ z ≫ biprod.snd) hab
      simpa [boundaryLinear_apply,Preadditive.comp_sub,Preadditive.sub_comp,Category.assoc] using eq
    have hs : ¬ ∀ A B, (T ≅ A ⊞ B) → IsZero A ∨ IsZero B := fun hh ↦ ht ⟨hz,hh⟩
    push Not at hs
    obtain ⟨A,B,e,ha,hb⟩ := hs
    have hd := ((FGModuleCat.isoToLinearEquiv e).restrictScalars k).finrank_eq.trans
      (FGModuleCat.finrank_biprod k A B)
    change Module.finrank k (T.obj : Type u) = Module.finrank k (A.obj : Type u) + Module.finrank k (B.obj : Type u) at hd
    have hA := dimensionWeight_pos k A ha
    have hB := dimensionWeight_pos k B hb
    simp only [dimensionWeight_eval,Int.natCast_pos] at hA hB
    let j (V : FGModuleCat.{u} R) := biprod.mapIso e (Iso.refl V) ≪≫ biprod.associator A B V
    exact ih _ (by omega) B X Y (ih _ (by omega) A _ _ (RigidOn.transport k h (j X) (j Y)) rfl) rfl

include k in
/-- A presilting complex admits a representative on any prescribed pair of
finite projective terms with its projective class. -/
private theorem exists_representative_on_terms_aux (P Q : TwoTerm R) (hp : P.IsPresilting)
    (h : P.projectiveClass = Q.projectiveClass) :
    ∃ d : Q.source ⟶ Q.target, ({ Q with differential := d } : TwoTerm R).IsPresilting ∧
      Nonempty (P.homotopyObject ≅ ({ Q with differential := d } : TwoTerm R).homotopyObject) := by
  obtain ⟨S,T,⟨es⟩,⟨et⟩⟩ := exists_stable_term_isos P Q h
  let P' := P.directSum (contractible S)
  have hp' := (isPresilting_directSum_contractible_iff k P S).2 hp
  have hrig : RigidOn k P'.source P'.target :=
    ⟨P'.differential,(isPresilting_iff_boundaryLinear_surjective (k := k) P').1 hp'⟩
  obtain ⟨d,hd⟩ := remove_common_terms k T.val Q.source Q.target (RigidOn.transport k hrig
    (es ≪≫ biprod.braiding _ _) (et ≪≫ biprod.braiding _ _))
  have hs := (isPresilting_iff_boundaryLinear_surjective (k := k) ({ Q with differential := d } : TwoTerm R)).2 hd
  exact ⟨d,hs,nonempty_homotopyIso_of_isPresilting_of_class_eq k P _ hp hs h⟩

include k in
/-- The rigid-terms lemma: the source and target may be prescribed independently
whenever the difference of their classes is the class of P. -/
theorem exists_representative_on_terms (P : TwoTerm R) (hp : P.IsPresilting)
    (A B : FGModuleCat.{u} R) [Module.Projective R A] [Module.Projective R B]
    (h : P.projectiveClass = ProjectiveClass.of ⟨B,inferInstance⟩ - ProjectiveClass.of ⟨A,inferInstance⟩) :
    ∃ d : A ⟶ B, (ofDifferential d).IsPresilting ∧
      Nonempty (P.homotopyObject ≅ (ofDifferential d).homotopyObject) :=
  exists_representative_on_terms_aux k P (ofDifferential (0 : A ⟶ B)) hp h

omit [IsNoetherianRing R] [IsArtinianRing R] in
/-- Along the line from a presilting differential to any other differential
on the same projectives, the generic fiber is isomorphic to the rigid one
on the scalar-extended modules over the rational function field. -/
theorem exists_rational_pencil_automorphisms (P : TwoTerm R) (hp : P.IsPresilting)
    (σ : P.source ⟶ P.target) :
    let F := RatFunc k
    let G := FieldExtension.extend k F R
    ∃ (a : G.obj P.source ≅ G.obj P.source) (b : G.obj P.target ≅ G.obj P.target),
      a.hom ≫ G.map P.differential =
        (G.map P.differential + (algebraMap (Polynomial k) F Polynomial.X) • G.map (σ - P.differential)) ≫ b.hom := by
  let F := RatFunc k
  let ev : Polynomial k →ₐ[k] F := IsScalarTower.toAlgHom k (Polynomial k) F
  have hev : Function.Injective ev := IsFractionRing.injective (Polynomial k) F
  have (M N : FGModuleCat.{u} R) : Module.Finite k (M ⟶ N) := finiteModuleHom_isFinite k M N
  obtain ⟨a,b,hab⟩ := exists_generic_affine_iso k P.differential σ ev hev
    ((isPresilting_iff_boundaryLinear_surjective (k := k) P).1 hp)
  let H := FieldExtension.extendScalarCategory k F R
  let G : FGModuleCat.{u} R ⥤ ScalarCategory k F (FGModuleCat.{u} R) := ScalarCategory.of
  have hmap {M N : FGModuleCat.{u} R} (f : M ⟶ N) :
      H.map (G.map f) = (FieldExtension.extend k F R).map f := by
    change FieldExtension.homTensorMap k F R M N (TensorProduct.tmul k 1 f) = _
    simp [FieldExtension.homTensorMap_tmul]; rfl
  have hlin {M N : FGModuleCat.{u} R} (s : F) (f : G.obj M ⟶ G.obj N) :
      H.map (s • f) = s • H.map f := (FieldExtension.homTensorMap k F R M N).map_smul s f
  refine ⟨H.mapIso a,H.mapIso b,?_⟩
  have h := congrArg H.map hab
  change H.map (a.hom ≫ G.map P.differential) =
    H.map ((G.map P.differential + ev Polynomial.X • G.map (σ-P.differential)) ≫ b.hom) at h
  rw [H.map_comp,H.map_comp,H.map_add,hlin,hmap,hmap] at h
  exact h

end EFiniteCharacterizations.TwoTerm
