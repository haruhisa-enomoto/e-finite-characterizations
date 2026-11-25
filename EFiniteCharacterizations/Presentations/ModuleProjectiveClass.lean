module

public import EFiniteCharacterizations.Presentations.MinimalPresentations
public import EFiniteCharacterizations.Modules.ProjectiveBiproducts

/-! # The projective class of a minimal module presentation -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations

section
variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- Right minimality is preserved by the diagonal sum of two morphisms.
The two diagonal blocks after Gaussian elimination still fix their respective maps. -/
theorem rightMinimal_biprod_map {A B X Y : C} (p : A ⟶ X) (q : B ⟶ Y)
    (hp : ∀ a, a ≫ p = p → IsIso a) (hq : ∀ b, b ≫ q = q → IsIso b) :
    ∀ e, e ≫ biprod.map p q = biprod.map p q → IsIso e := by
  intro e he
  let a := biprod.inl ≫ e ≫ biprod.fst
  let b := biprod.inl ≫ e ≫ biprod.snd
  let c := biprod.inr ≫ e ≫ biprod.fst
  let d := biprod.inr ≫ e ≫ biprod.snd
  have ha : a ≫ p = p := by
    simpa [a, Category.assoc] using congrArg (fun f ↦ biprod.inl ≫ f ≫ biprod.fst) he
  have hb : b ≫ q = 0 := by
    simpa [b, Category.assoc] using congrArg (fun f ↦ biprod.inl ≫ f ≫ biprod.snd) he
  have hd : d ≫ q = q := by
    simpa [d, Category.assoc] using congrArg (fun f ↦ biprod.inr ≫ f ≫ biprod.snd) he
  have : IsIso a := hp a ha
  let z := d - c ≫ inv a ≫ b
  have : IsIso z := hq z (by simp [z, Preadditive.sub_comp, Category.assoc, hd, hb])
  let L := Biprod.unipotentLower (-c ≫ inv a)
  let U := Biprod.unipotentUpper (-inv a ≫ b)
  have hw : L.hom ≫ e ≫ U.hom = biprod.map a z := by
    have hw := (Biprod.gaussian' a b c d).2.2.2
    change L.hom ≫ Biprod.ofComponents a b c d ≫ U.hom = biprod.map a z at hw
    simpa only [a,b,c,d,Biprod.ofComponents_eq] using hw
  have h : e = L.inv ≫ biprod.map a z ≫ U.inv := by simp [← hw]
  have : IsIso (biprod.map a z) := (biprod.mapIso (asIso a) (asIso z)).isIso_hom
  rw [h]
  infer_instance

variable [HasFiniteBiproducts C]

/-- Split off coordinate zero from a finite power. -/
private noncomputable def finPowerSuccIso (X : C) (n : ℕ) :
    (⨁ fun _ : Fin (n+1) ↦ X) ≅ X ⊞ (⨁ fun _ : Fin n ↦ X) := by
  let A := fun _ : Fin (n+1) ↦ X
  let B := fun _ : Fin n ↦ X
  let h := biprod.lift (biproduct.π A 0) (biproduct.lift (f := B) fun j ↦ biproduct.π A j.succ)
  let g := biprod.desc (biproduct.ι A 0) (biproduct.desc (f := B) fun j ↦ biproduct.ι A j.succ)
  have hz : biproduct.ι A 0 ≫ h = biprod.inl := by
    apply biprod.hom_ext
    · simp [h,A]
    · apply biproduct.hom_ext; intro i
      simp [h,A, Ne.symm (Fin.succ_ne_zero i)]
  have hs (m : Fin n) : biproduct.ι A m.succ ≫ h = biproduct.ι B m ≫ biprod.inr := by
    apply biprod.hom_ext
    · simp [h,A]
    · apply biproduct.hom_ext; intro i
      by_cases he : m = i
      · subst i; simp [h,A,B]
      · simp [h,A,B,he]
  refine ⟨h,g,?_,?_⟩
  · apply biproduct.hom_ext'
    intro j
    refine Fin.cases ?_ (fun m ↦ ?_) j
    · rw [← Category.assoc,hz,biprod.inl_desc,Category.comp_id]
    · rw [← Category.assoc,hs,Category.assoc,biprod.inr_desc,biproduct.ι_desc,Category.comp_id]
  · apply biprod.hom_ext'
    · rw [← Category.assoc,biprod.inl_desc,hz,Category.comp_id]
    · rw [← Category.assoc,biprod.inr_desc,Category.comp_id]
      apply biproduct.hom_ext'
      intro i
      rw [← Category.assoc,biproduct.ι_desc,hs]

theorem rightMinimal_power_map {X Y : C} {f : X ⟶ Y} (hf : ∀ a, a ≫ f = f → IsIso a) (n : ℕ) :
    let D := biproduct.map (fun _ : Fin n ↦ f)
    ∀ a, a ≫ D = D → IsIso a := by
  dsimp only
  induction n with
  | zero =>
    intro a _
    have : a = 𝟙 _ := by apply biproduct.hom_ext; intro j; exact Fin.elim0 j
    rw [this]; infer_instance
  | succ n ih =>
    intro a ha
    let u := finPowerSuccIso X n
    let v := finPowerSuccIso Y n
    let D := biproduct.map (fun _ : Fin (n+1) ↦ f)
    let d := biprod.map f (biproduct.map (fun _ : Fin n ↦ f))
    have hw : u.hom ≫ d = D ≫ v.hom := by
      apply biprod.hom_ext
      · simp [u,v,d,D,finPowerSuccIso]
      · apply biproduct.hom_ext; intro i; simp [u,v,d,D,finPowerSuccIso]
    have h := rightMinimal_biprod_map f _ hf ih (u.inv ≫ a ≫ u.hom) (by
      change (u.inv ≫ a ≫ u.hom) ≫ d = d
      rw [Category.assoc,Category.assoc,hw,← Category.assoc a D,ha,← hw,Iso.inv_hom_id_assoc])
    have he : a = u.hom ≫ (u.inv ≫ a ≫ u.hom) ≫ u.inv := by simp
    rw [he]; infer_instance

end

namespace FGModuleCat.ProjectiveCover

variable {R : Type u} [Ring R] {X Y : FGModuleCat.{u} R}

noncomputable def directSum (p : ProjectiveCover X) (q : ProjectiveCover Y) : ProjectiveCover (X ⊞ Y) where
  source := p.source ⊞ q.source
  projective_source := by
    have := p.projective_source
    have := q.projective_source
    exact FGModuleCat.projective_biprod _ _
  hom := biprod.map p.hom q.hom
  epi_hom := by
    have := p.epi_hom
    have := q.epi_hom
    infer_instance
  rightMinimal := rightMinimal_biprod_map _ _ p.rightMinimal q.rightMinimal

theorem sources_iso (p : ProjectiveCover X) (q : ProjectiveCover Y) (e : X ≅ Y) :
    Nonempty (p.source ≅ q.source) := by
  have := p.projective_source
  have := q.projective_source
  have := p.epi_hom
  have := q.epi_hom
  obtain ⟨a,ha⟩ := FGModuleCat.exists_lift_of_projective q.hom (p.hom ≫ e.hom)
  obtain ⟨b,hb⟩ := FGModuleCat.exists_lift_of_projective p.hom (q.hom ≫ e.inv)
  have : IsIso (a ≫ b) := p.rightMinimal (a ≫ b) (by rw [Category.assoc,hb,← Category.assoc,ha]; simp)
  have : IsIso (b ≫ a) := q.rightMinimal (b ≫ a) (by rw [Category.assoc,ha,← Category.assoc,hb]; simp)
  have : Mono a := mono_of_mono a b
  have : IsSplitEpi a := IsSplitEpi.mk' ⟨inv (b ≫ a) ≫ b, by simp⟩
  have := isIso_of_mono_of_isSplitEpi a
  exact ⟨asIso a⟩

end FGModuleCat.ProjectiveCover

section Kernels
variable {C : Type*} [Category* C] [Abelian C]

/-- Splitting the second projection of a pullback identifies its kernel
summand with the kernel of the first map. -/
private noncomputable def pullbackKerBiprod {A B M : C} (p : A ⟶ M) (q : B ⟶ M)
    (t : B ⟶ A) (ht : t ≫ p = q) : pullback p q ≅ kernel p ⊞ B := by
  let a := pullback.fst p q
  let b := pullback.snd p q
  let k := kernel.lift p (a - b ≫ t) (by
    rw [Preadditive.sub_comp, Category.assoc, ht, pullback.condition, sub_self])
  let z : kernel p ⊞ B ⟶ A := biprod.fst ≫ kernel.ι p + biprod.snd ≫ t
  let j : kernel p ⊞ B ⟶ pullback p q := pullback.lift z biprod.snd (by simp [z, Preadditive.add_comp, Category.assoc,ht])
  refine ⟨biprod.lift k b,j,?_,?_⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      simp [z,k,a,b,Preadditive.comp_add,← Category.assoc]
    · simp [j,b]
  · apply biprod.hom_ext
    · apply (cancel_mono (kernel.ι p)).1
      simp [k,j,z,a,b,Category.assoc,Preadditive.comp_sub]
    · simp [j,b]

private noncomputable def kernelBiprodMapIso {A B X Y : C} (p : A ⟶ X) (q : B ⟶ Y) :
    kernel (biprod.map p q) ≅ kernel p ⊞ kernel q := by
  let d := biprod.map p q
  let a := kernel.lift p (kernel.ι d ≫ biprod.fst) (by
    rw [Category.assoc, ← biprod.map_fst, ← Category.assoc, kernel.condition, zero_comp])
  let b := kernel.lift q (kernel.ι d ≫ biprod.snd) (by
    rw [Category.assoc, ← biprod.map_snd, ← Category.assoc, kernel.condition, zero_comp])
  let j := kernel.lift d (biprod.map (kernel.ι p) (kernel.ι q)) (by
    ext <;> simp [d])
  refine ⟨biprod.lift a b,j,?_,?_⟩
  · apply (cancel_mono (kernel.ι d)).1
    apply biprod.hom_ext <;> simp [a,b,j,Category.assoc]
  · apply biprod.hom_ext
    · apply (cancel_mono (kernel.ι p)).1
      simp [a,j,Category.assoc]
    · apply (cancel_mono (kernel.ι q)).1
      simp [b,j,Category.assoc]

end Kernels

variable {R : Type u} [Ring R] (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R]

/-- The projective class of the source of a projective cover. -/
noncomputable def projectiveCoverClass (M : FGModuleCat.{u} R) : ProjectiveClass R :=
  let p := (FGModuleCat.nonempty_projectiveCover k M).some
  ProjectiveClass.of ⟨p.source,p.projective_source⟩

theorem projectiveCoverClass_eq {M N : FGModuleCat.{u} R} (e : M ≅ N) (p : FGModuleCat.ProjectiveCover N) :
    projectiveCoverClass k M = ProjectiveClass.of ⟨p.source,p.projective_source⟩ := by
  let q := (FGModuleCat.nonempty_projectiveCover k M).some
  exact ProjectiveClass.of_eq_of_iso _ _ (q.sources_iso p e).some

theorem projectiveCoverClass_iso {M N : FGModuleCat.{u} R} (e : M ≅ N) :
    projectiveCoverClass k M = projectiveCoverClass k N :=
  projectiveCoverClass_eq k e (FGModuleCat.nonempty_projectiveCover k N).some

theorem projectiveCoverClass_biprod (A B : FGModuleCat.{u} R) :
    projectiveCoverClass k (A ⊞ B) = projectiveCoverClass k A + projectiveCoverClass k B := by
  let p := (FGModuleCat.nonempty_projectiveCover k A).some
  let q := (FGModuleCat.nonempty_projectiveCover k B).some
  exact (projectiveCoverClass_eq k (Iso.refl _) (p.directSum q)).trans
    (ProjectiveClass.of_biprod ⟨p.source,p.projective_source⟩ ⟨q.source,q.projective_source⟩)

theorem projectiveCoverClass_projective (G : FiniteProjective R) :
    projectiveCoverClass k G.val = ProjectiveClass.of G :=
  projectiveCoverClass_eq k (Iso.refl _) ⟨G.val,G.property,𝟙 _,inferInstance,fun f h ↦ by
    have he : f = 𝟙 _ := by simpa using h
    rw [he]; infer_instance⟩

/-- The integral g-vector of a finite module. -/
noncomputable def moduleProjectiveClass (M : FGModuleCat.{u} R) : ProjectiveClass R :=
  ((MinimalPresentation.nonempty_minimalPresentation k M).some).twoTerm.projectiveClass

/-- Any projective epimorphism computes the g-vector by subtracting the
projective cover of its kernel. This is Schanuel's lemma in the split group. -/
theorem moduleProjectiveClass_of_projective_epi {M : FGModuleCat.{u} R} (A : FiniteProjective R)
    (p : A.val ⟶ M) [Epi p] : moduleProjectiveClass k M =
      ProjectiveClass.of A - projectiveCoverClass k (kernel p) := by
  let z := (MinimalPresentation.nonempty_minimalPresentation k M).some
  let B : FiniteProjective R := ⟨z.cover.source,z.cover.projective_source⟩
  let q := z.cover.hom
  have : Epi q := z.cover.epi_hom
  have := A.property
  have := z.cover.projective_source
  obtain ⟨s,hs⟩ := FGModuleCat.exists_lift_of_projective p q
  obtain ⟨t,ht⟩ := FGModuleCat.exists_lift_of_projective q p
  let e := (pullbackKerBiprod p q s hs).symm ≪≫ pullbackSymmetry p q ≪≫ pullbackKerBiprod q p t ht
  have h := projectiveCoverClass_iso k e
  change projectiveCoverClass k (kernel p ⊞ B.val) = projectiveCoverClass k (kernel q ⊞ A.val) at h
  rw [projectiveCoverClass_biprod,projectiveCoverClass_biprod,projectiveCoverClass_projective,
    projectiveCoverClass_projective,projectiveCoverClass_eq k (Iso.refl (kernel q)) z.relations] at h
  change ProjectiveClass.of B - ProjectiveClass.of ⟨z.relations.source,z.relations.projective_source⟩ = _
  exact sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm,add_left_comm,add_assoc] using h)

theorem moduleProjectiveClass_iso {M N : FGModuleCat.{u} R} (e : M ≅ N) :
    moduleProjectiveClass k M = moduleProjectiveClass k N := by
  let z := (FGModuleCat.nonempty_projectiveCover k M).some
  let A : FiniteProjective R := ⟨z.source,z.projective_source⟩
  have := z.epi_hom
  rw [moduleProjectiveClass_of_projective_epi k A z.hom,
    moduleProjectiveClass_of_projective_epi k A (z.hom ≫ e.hom)]
  exact congrArg (ProjectiveClass.of A - ·)
    (projectiveCoverClass_iso k (kernel.mapIso z.hom (z.hom ≫ e.hom) (Iso.refl _) e (by simp)))

theorem moduleProjectiveClass_biprod (M N : FGModuleCat.{u} R) :
    moduleProjectiveClass k (M ⊞ N) = moduleProjectiveClass k M + moduleProjectiveClass k N := by
  let p := (FGModuleCat.nonempty_projectiveCover k M).some
  let q := (FGModuleCat.nonempty_projectiveCover k N).some
  let A : FiniteProjective R := ⟨p.source,p.projective_source⟩
  let B : FiniteProjective R := ⟨q.source,q.projective_source⟩
  have := p.epi_hom
  have := q.epi_hom
  let z := p.directSum q
  have : Epi z.hom := z.epi_hom
  have hz := moduleProjectiveClass_of_projective_epi k ⟨z.source,z.projective_source⟩ z.hom
  change moduleProjectiveClass k (M ⊞ N) = ProjectiveClass.of (ProjectiveClass.biprod A B) -
    projectiveCoverClass k (kernel (biprod.map p.hom q.hom)) at hz
  rw [hz,
    moduleProjectiveClass_of_projective_epi k A p.hom,moduleProjectiveClass_of_projective_epi k B q.hom,
    projectiveCoverClass_iso k (kernelBiprodMapIso p.hom q.hom), projectiveCoverClass_biprod,ProjectiveClass.of_biprod]
  abel

theorem MinimalPresentation.projectiveClass_eq {M : FGModuleCat.{u} R} (p : MinimalPresentation M) :
    p.twoTerm.projectiveClass = moduleProjectiveClass k M := by
  have := p.cover.epi_hom
  rw [moduleProjectiveClass_of_projective_epi k ⟨_,p.cover.projective_source⟩ p.cover.hom,
    projectiveCoverClass_eq k (Iso.refl _) p.relations]
  rfl

/-- The source of an arbitrary projective epimorphism splits as the source
of a cover and a projective summand killed by the epimorphism. -/
theorem FGModuleCat.ProjectiveCover.split_projective_epi {M : FGModuleCat.{u} R}
    (p : FGModuleCat.ProjectiveCover M) (A : FiniteProjective R) (f : A.val ⟶ M) [Epi f] :
    ∃ (K : FiniteProjective R) (i : K.val ⟶ A.val) (r : A.val ⟶ K.val),
      i ≫ r = 𝟙 _ ∧ i ≫ f = 0 ∧ ProjectiveClass.of A =
        ProjectiveClass.of K + ProjectiveClass.of ⟨p.source,p.projective_source⟩ := by
  have := A.property
  have := p.projective_source
  have := p.epi_hom
  obtain ⟨t,ht⟩ := FGModuleCat.exists_lift_of_projective p.hom f
  obtain ⟨a,ha⟩ := FGModuleCat.exists_lift_of_projective f p.hom
  have : IsIso (a ≫ t) := p.rightMinimal _ (by rw [Category.assoc,ht,ha])
  let s := inv (a ≫ t) ≫ a
  let row := ShortComplex.mk (kernel.ι t) t (kernel.condition t)
  let spl := ShortComplex.Splitting.ofExactOfSection row (ShortComplex.exact_kernel t) s
    (by simp [row,s]) (inferInstanceAs (Mono (kernel.ι t)))
  have hi : kernel.ι t ≫ spl.r = 𝟙 _ := spl.f_r
  let K : FiniteProjective R := ⟨kernel t,Module.Projective.of_split (kernel.ι t).hom.hom spl.r.hom.hom
    (congrArg (fun v : kernel t ⟶ kernel t ↦ v.hom.hom) hi)⟩
  refine ⟨K,kernel.ι t,spl.r,hi,by rw [← ht,← Category.assoc,kernel.condition,zero_comp],?_⟩
  exact (ProjectiveClass.of_eq_of_iso A (ProjectiveClass.biprod K ⟨p.source,p.projective_source⟩)
    spl.isoBinaryBiproduct).trans (ProjectiveClass.of_biprod ..)

include k in
/-- For every two-term presentation the discrepancy from its cokernel's
g-vector is a shifted projective summand in the kernel of the differential. -/
theorem TwoTerm.exists_projectiveClass_cokernel_sub (P : TwoTerm R) :
    ∃ (K : FiniteProjective R) (i : K.val ⟶ P.source) (r : P.source ⟶ K.val),
      i ≫ r = 𝟙 _ ∧ i ≫ P.differential = 0 ∧
      P.projectiveClass = moduleProjectiveClass k (cokernel P.differential) - ProjectiveClass.of K := by
  let q := cokernel.π P.differential
  let t := kernel.lift q P.differential (cokernel.condition _)
  let row := ShortComplex.mk P.differential q (cokernel.condition _)
  have : Epi t := row.exact_iff_epi_kernel_lift.1 (ShortComplex.exact_cokernel _)
  let p := (FGModuleCat.nonempty_projectiveCover k (kernel q)).some
  obtain ⟨K,i,r,hir,hz,he⟩ := p.split_projective_epi ⟨P.source,P.projective_source⟩ t
  refine ⟨K,i,r,hir,?_,?_⟩
  · rw [← kernel.lift_ι q P.differential (cokernel.condition _),← Category.assoc i]
    exact (congrArg (· ≫ kernel.ι q) hz).trans zero_comp
  · rw [moduleProjectiveClass_of_projective_epi k ⟨_,P.projective_target⟩ q,
      projectiveCoverClass_eq k (Iso.refl _) p,projectiveClass,he]
    abel

theorem MinimalPresentation.rightMinimal {M : FGModuleCat.{u} R} (p : MinimalPresentation M)
    (a : p.twoTerm.source ⟶ p.twoTerm.source) (ha : a ≫ p.twoTerm.differential = p.twoTerm.differential) : IsIso a := by
  apply p.relations.rightMinimal a
  apply (cancel_mono (kernel.ι p.cover.hom)).1
  exact (Category.assoc ..).trans ha

theorem TwoTerm.projectiveClass_eq_of_rightMinimal (P : TwoTerm R)
    (hm : ∀ a, a ≫ P.differential = P.differential → IsIso a) :
    P.projectiveClass = moduleProjectiveClass k (cokernel P.differential) := by
  let q := cokernel.π P.differential
  let t := kernel.lift q P.differential (cokernel.condition _)
  let row := ShortComplex.mk P.differential q (cokernel.condition _)
  let p : FGModuleCat.ProjectiveCover (kernel q) := {
    source := P.source, projective_source := P.projective_source, hom := t
    epi_hom := row.exact_iff_epi_kernel_lift.1 (ShortComplex.exact_cokernel _)
    rightMinimal := fun a ha ↦ hm a (by
      have he := congrArg (· ≫ kernel.ι q) ha
      simpa [Category.assoc,t] using he) }
  rw [moduleProjectiveClass_of_projective_epi k ⟨_,P.projective_target⟩ q,projectiveCoverClass_eq k (Iso.refl _) p]
  rfl

end EFiniteCharacterizations
