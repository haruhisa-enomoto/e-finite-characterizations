module

public import EFiniteCharacterizations.Presentations.RegularInversion

/-! # Extension of scalars of finite projectives over noncommutative rings -/

@[expose] public section

universe u

namespace EFiniteCharacterizations.ScalarInduction

variable {R B : Type u} [Ring R] [Ring B] (f : R →+* B)
    (M : Type u) [AddCommGroup M] [Module R M]

noncomputable abbrev gen (x : M) : M →₀ B := Finsupp.single x 1

/-- Relations making the free generators additive and semilinear. -/
noncomputable def relations : Submodule B (M →₀ B) :=
  Submodule.span B ({v | ∃ x y : M, v = gen M (x+y) - (gen M x + gen M y)} ∪
    {v | ∃ (r : R) (x : M), v = gen M (r • x) - f r • gen M x})

abbrev Induced := (M →₀ B) ⧸ relations f M

noncomputable def unit : M →ₛₗ[f] Induced f M where
  toFun x := (relations f M).mkQ (gen M x)
  map_add' x y := by
    rw [← map_add, ← sub_eq_zero, ← map_sub]
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span (Or.inl ⟨x,y,rfl⟩))
  map_smul' r x := by
    rw [← map_smul, ← sub_eq_zero, ← map_sub]
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span (Or.inr ⟨r,x,rfl⟩))

variable {M} {N : Type u} [AddCommGroup N] [Module B N]

noncomputable def lift (p : M →ₛₗ[f] N) : Induced f M →ₗ[B] N :=
  (relations f M).liftQ (Finsupp.linearCombination B p) (by
    apply Submodule.span_le.mpr
    rintro v (⟨x,y,rfl⟩ | ⟨r,x,rfl⟩) <;> simp [LinearMap.mem_ker,gen])

@[simp] theorem lift_unit (p : M →ₛₗ[f] N) (x : M) : lift f p (unit f M x) = p x := by
  change Finsupp.linearCombination B p (Finsupp.single x 1) = _
  simp

theorem hom_ext {p q : Induced f M →ₗ[B] N} (h : ∀ x, p (unit f M x) = q (unit f M x)) : p = q := by
  have eqn : p.comp (relations f M).mkQ = q.comp (relations f M).mkQ := by
    apply Finsupp.lhom_ext
    intro x b
    have hb : Finsupp.single x b = b • gen M x := by simp [gen]
    rw [hb,map_smul,map_smul]
    exact congrArg (b • ·) (h x)
  exact LinearMap.ext fun y ↦ by
    obtain ⟨v,rfl⟩ := (relations f M).mkQ_surjective y
    exact LinearMap.congr_fun eqn v

/-- A finitely generated module remains finitely generated after induction. -/
instance [Module.Finite R M] : Module.Finite B (Induced f M) := by
  classical
  obtain ⟨s,hs⟩ := (Module.Finite.fg_top (R := R) (M := M))
  let V := Submodule.span B ((unit f M) '' (s : Set M))
  have hu (x : M) : unit f M x ∈ V := by
    have hle : Submodule.span R (s : Set M) ≤ V.comap (unit f M) :=
      Submodule.span_le.mpr fun y hy ↦ Submodule.subset_span ⟨y,hy,rfl⟩
    exact hle (hs ▸ Submodule.mem_top)
  have he : V.mkQ = 0 := hom_ext f (fun x ↦ (Submodule.Quotient.mk_eq_zero _).2 (hu x))
  have ht : V = ⊤ := top_unique fun x _ ↦ (Submodule.Quotient.mk_eq_zero _).1 (LinearMap.congr_fun he x)
  apply Module.Finite.of_fg_top
  rw [← ht]
  exact Submodule.fg_span (s.finite_toSet.image _)

/-- Induction of a projective module is projective. -/
instance [Module.Projective R M] : Module.Projective B (Induced f M) := by
  apply Module.Projective.of_lifting_property
  intro X Y _ _ _ _ q p hq
  let := Module.compHom X f
  let := Module.compHom Y f
  let q' : X →ₗ[R] Y :=
    { toFun := q, map_add' := q.map_add, map_smul' := fun r x ↦ q.map_smul (f r) x }
  let p' : M →ₗ[R] Y :=
    { toFun := fun x ↦ p (unit f M x)
      map_add' := fun _ _ ↦ by simp
      map_smul' := fun r x ↦ by simp; rfl }
  obtain ⟨v,hv⟩ := Module.projective_lifting_property q' p' hq
  let w : M →ₛₗ[f] X := { toFun := v, map_add' := v.map_add, map_smul' := v.map_smul }
  exact ⟨lift f w,hom_ext f fun x ↦ by
    simp only [LinearMap.comp_apply,lift_unit]; exact LinearMap.congr_fun hv x⟩

end EFiniteCharacterizations.ScalarInduction

namespace EFiniteCharacterizations.ScalarInduction

variable {R B : Type u} [Ring R] [Ring B] (f : R →+* B) (M : Type u) [AddCommGroup M] [Module R M]

/-- Hom adjunction for the induced module. -/
noncomputable def homEquiv (N : ModuleCat.{u} B) :
    letI := Module.compHom N f
    (Induced f M →ₗ[B] N) ≃ (M →ₗ[R] N) := by
  let := Module.compHom N f
  exact
    { toFun p := { toFun := fun x ↦ p (unit f M x)
                   map_add' := fun x y ↦ by simp
                   map_smul' := fun r x ↦ by simp; rfl }
      invFun q := lift f ⟨q.toAddHom, q.map_smul⟩
      left_inv p := hom_ext f fun x ↦ lift_unit ..
      right_inv q := LinearMap.ext fun x ↦ lift_unit .. }

end EFiniteCharacterizations.ScalarInduction

namespace EFiniteCharacterizations.TwoTerm

open ScalarInduction CategoryTheory

variable {R B : Type u} [Ring R] [Ring B]

/-- Extension of scalars of a two-term finite projective presentation. -/
noncomputable def induce (P : TwoTerm R) (f : R →+* B) : TwoTerm B := by
  have := P.projective_source
  have := P.projective_target
  have : Module.Finite R P.source := P.source.property
  have : Module.Finite R P.target := P.target.property
  let d := lift f ((unit f P.target).comp P.differential.hom.hom)
  exact ⟨FGModuleCat.of B (Induced f P.source), FGModuleCat.of B (Induced f P.target),
    inferInstanceAs (Module.Projective B (Induced f P.source)),
    inferInstanceAs (Module.Projective B (Induced f P.target)),FGModuleCat.ofHom d⟩

theorem invertedOn_induce_iff (P : TwoTerm R) (f : R →+* B) (N : ModuleCat.{u} B) :
    (P.induce f).InvertedOn N ↔ (letI := Module.compHom N f; P.InvertedOn (ModuleCat.of R N)) := by
  let := Module.compHom N f
  let X := homEquiv f P.source N
  let Y := homEquiv f P.target N
  rw [invertedOn_iff_linear, invertedOn_iff_linear]
  let t := fun p : P.target →ₗ[R] N ↦ p.comp P.differential.hom.hom
  have he : (fun p : Induced f P.target →ₗ[B] N ↦ p.comp (P.induce f).differential.hom.hom) =
      X.symm ∘ t ∘ Y := by
    funext p
    apply X.injective
    simp only [Function.comp_apply,Equiv.apply_symm_apply]
    apply LinearMap.ext
    intro x
    change p (lift f ((unit f P.target).comp P.differential.hom.hom) (unit f P.source x)) = _
    rw [lift_unit]
    rfl
  change Function.Bijective (fun p : Induced f P.target →ₗ[B] N ↦ _) ↔ Function.Bijective t
  exact (congrArg Function.Bijective he).to_iff.trans ((X.symm.comp_bijective _).trans (Y.bijective_comp _))

theorem isIso_iff_invertedOn_all (P : TwoTerm R) :
    IsIso P.differential ↔ ∀ N : ModuleCat.{u} R, P.InvertedOn N := by
  constructor
  · intro h N
    let F := forget₂ (FGModuleCat R) (ModuleCat.{u} R)
    exact ((F.mapIso (asIso P.differential).symm).homFromEquiv (Z := N)).bijective
  · intro h
    obtain ⟨v,hv⟩ := (h P.source.obj).2 (𝟙 _)
    let i : P.target ⟶ P.source := InducedCategory.homMk v
    have eqn : P.differential ≫ i = 𝟙 _ := InducedCategory.hom_ext hv
    refine ⟨i,eqn,InducedCategory.hom_ext ((h P.target.obj).1 ?_)⟩
    change P.differential.hom ≫ v ≫ P.differential.hom = P.differential.hom ≫ 𝟙 _
    change P.differential.hom ≫ v = 𝟙 _ at hv
    rw [← Category.assoc,hv,Category.id_comp,Category.comp_id]

/-- The regular-module test is equivalent to the usual definition of
inverting a finite projective map by extension of scalars. -/
theorem isIso_induce_iff_regular (P : TwoTerm R) (f : R →+* B) :
    IsIso (P.induce f).differential ↔
      (letI := Module.compHom B f; P.InvertedOn (ModuleCat.of R B)) := by
  rw [← invertedOn_restrictions_iff_regular, isIso_iff_invertedOn_all]
  exact ⟨fun h N _ _ ↦ (invertedOn_induce_iff P f (ModuleCat.of B N)).1 (h _),
    fun h N ↦ (invertedOn_induce_iff P f N).2 (h N)⟩

end EFiniteCharacterizations.TwoTerm
