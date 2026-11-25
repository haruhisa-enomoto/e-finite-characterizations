module

public import EFiniteCharacterizations.Subcategories.TorsionApproximations
public import EFiniteCharacterizations.Stability.StableSubobjects
public import EFiniteCharacterizations.Presentations.MinimalPresentations

/-! # Minimal approximations of the regular module by a torsion class -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R]

include k in
/-- A covariantly finite class closed under images of its endomorphisms has
a left minimal approximation of the regular module. Epimorphisms from
objects of the class onto the resulting generator split. -/
theorem exists_splitting_generator (T : ObjectProperty (FGModuleCat.{u} R))
    (himage : ∀ {X}, T X → ∀ f : X ⟶ X, T (Abelian.image f)) (h : CovariantlyFinite T) :
    ∃ (B : FGModuleCat.{u} R) (a : FGModuleCat.of R R ⟶ B), T B ∧
      (∀ X, T X → ∀ f : FGModuleCat.of R R ⟶ X, ∃ g, a ≫ g = f) ∧
      (∀ s : B ⟶ B, a ≫ s = a → IsIso s) ∧
      ∀ (E : FGModuleCat.{u} R), T E → ∀ r : E ⟶ B, Epi r →
        ∃ b : B ⟶ E, b ≫ r = 𝟙 B := by
  classical
  let A := FGModuleCat.of R R
  let Q (n : ℕ) := ∃ (B : FGModuleCat.{u} R) (a : A ⟶ B), T B ∧
    (∀ X, T X → ∀ f : A ⟶ X, ∃ g, a ≫ g = f) ∧ Module.finrank k (B.obj : Type u) = n
  obtain ⟨B₀, a₀, hB₀, ha₀⟩ := h A
  have hQ : ∃ n, Q n := ⟨_, B₀, a₀, hB₀, ha₀, rfl⟩
  obtain ⟨B, a, hB, ha, hd⟩ := Nat.find_spec hQ
  have hmin (s : B ⟶ B) (hs : a ≫ s = a) : IsIso s := by
    let e := Abelian.factorThruImage s
    let i := Abelian.image.ι s
    have hfac : e ≫ i = s := Abelian.image.fac s
    have hI : Q (Module.finrank k ((Abelian.image s).obj : Type u)) := by
      refine ⟨_, a ≫ e, himage hB s, ?_, rfl⟩
      intro X hX f
      obtain ⟨g, hg⟩ := ha X hX f
      exact ⟨i ≫ g, by rw [Category.assoc, ← Category.assoc e, hfac, ← Category.assoc, hs, hg]⟩
    have : IsIso i := by
      by_contra hn
      exact (Nat.not_lt_of_ge (Nat.find_min' hQ hI)) ((groundFinrank_lt_of_mono_not_iso k i hn).trans_eq hd)
    have he : Epi s := by rw [← hfac]; infer_instance
    have hsur := (FGModuleCat.epi_iff_surjective s).1 he
    let : Module.Finite k (B.obj : Type u) := Module.Finite.trans R _
    exact (FGModuleCat.isIso_iff_bijective s).2
      ⟨(LinearMap.injective_iff_surjective (f := s.hom.hom.restrictScalars k)).2 hsur, hsur⟩
  refine ⟨B, a, hB, ha, hmin, fun E hE r hr ↦ ?_⟩
  obtain ⟨e, he⟩ := FGModuleCat.exists_lift_of_projective r a
  obtain ⟨b, hb⟩ := ha E hE e
  have := hmin (b ≫ r) (by rw [← Category.assoc, hb, he])
  exact ⟨inv (b ≫ r) ≫ b, by rw [Category.assoc, IsIso.inv_hom_id]⟩

include k in
/-- A functorially finite torsion class has a left minimal approximation of the
regular module. Every epimorphism from the class onto its target splits. -/
theorem exists_splitting_torsion_generator (F : ObjectProperty (FGModuleCat.{u} R))
    (h : FunctoriallyFinite (leftHomOrthogonal F)) :
    ∃ (B : FGModuleCat.{u} R) (a : FGModuleCat.of R R ⟶ B), leftHomOrthogonal F B ∧
      (∀ X, leftHomOrthogonal F X → ∀ f : FGModuleCat.of R R ⟶ X, ∃ g, a ≫ g = f) ∧
      (∀ s : B ⟶ B, a ≫ s = a → IsIso s) ∧
      ∀ (E : FGModuleCat.{u} R), leftHomOrthogonal F E → ∀ r : E ⟶ B, Epi r →
        ∃ b : B ⟶ E, b ≫ r = 𝟙 B :=
  exists_splitting_generator k _ (fun hB s ↦ leftHomOrthogonal_of_epi (Abelian.factorThruImage s) hB) h.1

/-- The minimal presentation of a splitting generator passes the Hom
surjectivity test against every object of its torsion class. -/
theorem surjective_precompose_of_splitting_generator {F : ObjectProperty (FGModuleCat.{u} R)}
    {B X : FGModuleCat.{u} R} (p : MinimalPresentation B) (hB : leftHomOrthogonal F B)
    (hsplit : ∀ (E : FGModuleCat.{u} R), leftHomOrthogonal F E → ∀ r : E ⟶ B, Epi r →
        ∃ b : B ⟶ E, b ≫ r = 𝟙 B) (hX : leftHomOrthogonal F X) :
    Function.Surjective (p.twoTerm.precompose X) := by
  let _ := p.cover.projective_source
  let _ := p.relations.projective_source
  let _ := p.cover.epi_hom
  let d : p.relations.source ⟶ p.cover.source := p.twoTerm.differential
  let c := p.cover.hom
  have hd : d ≫ c = 0 := p.differential_comp_cover
  change ∀ f : p.relations.source ⟶ X, ∃ g, d ≫ g = f
  intro f
  let v := biprod.lift d f
  let π := cokernel.π v
  have hz : v ≫ biprod.fst ≫ c = 0 := by rw [← Category.assoc, biprod.lift_fst, hd]
  let r := cokernel.desc v (biprod.fst ≫ c) hz
  have hr : π ≫ r = biprod.fst ≫ c := cokernel.π_desc ..
  have hc : (biprod.inl ≫ π) ≫ r = c := by rw [Category.assoc, hr, biprod.inl_fst_assoc]
  have hE : leftHomOrthogonal F (cokernel v) := by
    intro Y hY e
    let a := biprod.inl ≫ π ≫ e
    have hh : π ≫ e = biprod.desc a 0 := by
      apply biprod.hom_ext'
      · simp [a]
      · simpa using hX Y hY (biprod.inr ≫ π ≫ e)
    have hda : d ≫ a = 0 := by
      have hv : v ≫ π ≫ e = 0 := by rw [← Category.assoc, cokernel.condition, zero_comp]
      rw [hh] at hv
      simpa [v, biprod.lift_desc] using hv
    obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc' p.isCokernel a hda
    have ha : a = 0 := by rw [← hg, hB Y hY g, comp_zero]
    apply (cancel_epi π).mp
    rw [hh, ha, comp_zero]
    apply biprod.hom_ext' <;> simp
  obtain ⟨s, hs⟩ := hsplit _ hE r (epi_of_epi_fac hc)
  obtain ⟨w, hw⟩ := FGModuleCat.exists_lift_of_projective π (c ≫ s)
  have hbc : (w ≫ biprod.fst - 𝟙 _) ≫ c = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, ← hr, ← Category.assoc, hw,
      Category.assoc, hs, Category.comp_id, sub_self]
  have hex : (ShortComplex.mk d c hd).Exact := ShortComplex.exact_of_g_is_cokernel _ p.isCokernel
  obtain ⟨b, hb⟩ := TwoTerm.exists_lift_of_exact hd hex _ hbc
  let w' := w - b ≫ v
  have hwπ : w' ≫ π = c ≫ s := by
    change (w - b ≫ v) ≫ π = _
    rw [Preadditive.sub_comp, hw, Category.assoc, cokernel.condition, comp_zero, sub_zero]
  have hw₁ : w' ≫ biprod.fst = 𝟙 _ := by simp [w', Preadditive.sub_comp, v, hb]
  have hdz : (d ≫ w') ≫ π = 0 := by rw [Category.assoc, hwπ, ← Category.assoc, hd, zero_comp]
  obtain ⟨t, ht⟩ := TwoTerm.exists_lift_of_exact (cokernel.condition v) (ShortComplex.exact_cokernel v) _ hdz
  have ht₁ : t ≫ d = d := by
    simpa [v, Category.assoc, hw₁] using congrArg (· ≫ biprod.fst) ht
  have ht₂ : t ≫ f = d ≫ w' ≫ biprod.snd := by
    simpa [v, Category.assoc] using congrArg (· ≫ biprod.snd) ht
  have htm : t ≫ p.relations.hom = p.relations.hom := by
    apply (cancel_mono (kernel.ι c)).mp
    rw [Category.assoc]
    exact ht₁
  let _ := p.relations.rightMinimal _ htm
  exact ⟨w' ≫ biprod.snd, (cancel_epi t).mp (by rw [← Category.assoc, ht₁, ht₂])⟩

end EFiniteCharacterizations
