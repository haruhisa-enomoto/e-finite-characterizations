module

public import EFiniteCharacterizations.Presentations.StableProjectiveTerms
public import EFiniteCharacterizations.Presentations.ModuleProjectiveClass
public import EFiniteCharacterizations.Subcategories.GeneratedModules

/-! # Bongartz's construction in two-term projective presentations -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R]

/-- A finite direct sum of projectives is projective. -/
theorem FGModuleCat.projective_biproduct {n : ℕ} (X : Fin n → FGModuleCat.{u} R)
    (hX : ∀ i, Module.Projective R (X i)) : Module.Projective R (⨁ X : FGModuleCat R) := by
  obtain ⟨F, hF, p, hp⟩ := FGModuleCat.exists_projective_epi (⨁ X)
  have hl (j : Fin n) : ∃ f : X j ⟶ F, f ≫ p = biproduct.ι X j := by
    let _ := hX j
    exact FGModuleCat.exists_lift_of_projective p (biproduct.ι X j)
  choose f hf using hl
  have h : biproduct.desc f ≫ p = 𝟙 (⨁ X) := by
    apply biproduct.hom_ext'
    intro j
    simpa only [biproduct.ι_desc_assoc, Category.comp_id] using hf j
  exact Module.Projective.of_split (biproduct.desc f).hom.hom p.hom.hom
    (congrArg (fun g : (⨁ X) ⟶ (⨁ X) ↦ g.hom.hom) h)

/-- In the split Grothendieck group a finite direct power has the expected class. -/
theorem ProjectiveClass.of_copies (P : FiniteProjective R) (n : ℕ) :
    of ⟨⨁ fun _ : Fin n ↦ P.val, FGModuleCat.projective_biproduct _ (fun _ ↦ P.property)⟩ =
      n • of P := by
  let F := forget₂ (FGModuleCat R) (ModuleCat.{u} R)
  let A (m : ℕ) := fun _ : Fin m ↦ P.val
  let T (m : ℕ) : FiniteProjective R :=
    ⟨⨁ A m, FGModuleCat.projective_biproduct _ (fun _ ↦ P.property)⟩
  let e (m : ℕ) : (T m).val.obj ≅ ModuleCat.of R (Fin m → P.val) := by
    let _ : PreservesBiproduct (A m) F := preservesBiproduct_of_preservesCoproduct F
    exact (F.mapBiproduct (A m)).trans (ModuleCat.biproductIsoPi (fun _ : Fin m ↦ P.val.obj))
  change of (T n) = n • of P
  induction n with
  | zero =>
    have hz : IsZero (T 0).val := (FGModuleCat.isZero_iff_subsingleton _).2
      ((e 0).toLinearEquiv.injective.subsingleton)
    rw [of_eq_of_iso _ (zeroProjective R) (hz.iso zeroProjective_isZero), of_zeroProjective, zero_smul]
  | succ n ih =>
    let a := LinearEquiv.piCongrLeft R (fun _ ↦ P.val) (finSuccEquiv n) ≪≫ₗ .piOptionEquivProd _
    let b : (T (n+1)).val.obj ≅ P.val.obj ⊞ (T n).val.obj :=
      (e (n+1)) ≪≫ a.toModuleIso ≪≫ (ModuleCat.biprodIsoProd P.val.obj (ModuleCat.of R (Fin n → P.val))).symm ≪≫
        biprod.mapIso (Iso.refl _) (e n).symm
    rw [of_eq_add_of_biprod P (T n) _ b, ih, succ_nsmul, add_comm]

private theorem eq_zero_of_regular_comp_eq_zero {M N : FGModuleCat.{u} R} (g : M ⟶ N)
    (hg : ∀ f : FGModuleCat.of R R ⟶ M, f ≫ g = 0) : g = 0 := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let f : FGModuleCat.of R R ⟶ M := FGModuleCat.ofHom (LinearMap.toSpanSingleton R M x)
  have h := congrArg (fun a : FGModuleCat.of R R ⟶ N ↦ a.hom.hom (1 : R)) (hg f)
  change g.hom.hom (LinearMap.toSpanSingleton R M x 1) = 0 at h
  rw [LinearMap.toSpanSingleton_apply_one] at h
  exact h

namespace TwoTerm

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R] [IsNoetherianRing R]

include k in
/-- The Bongartz construction starting from any projective gives a compatible
complex of class [G] + n[P]. Every map from G to a module in the weak torsion
class factors through the cokernel of this complex. -/
theorem exists_bongartz_at_projective_with_source (P : TwoTerm R) (hP : P.IsPresilting) (G : FGModuleCat.{u} R)
    [Module.Projective R G] :
    ∃ (Q : TwoTerm R) (ι : G ⟶ cokernel Q.differential),
      (∀ (K : FGModuleCat.{u} R) (i : K ⟶ Q.source) (r : Q.source ⟶ K), i ≫ r = 𝟙 _ →
        i ≫ Q.differential = 0 → ∃ (m : ℕ) (a : Fin m → (K ⟶ P.source)) (b : Fin m → (P.source ⟶ K)),
        (∀ j, a j ≫ P.differential = 0) ∧ ∑ j, a j ≫ b j = 𝟙 _) ∧
      ((∀ a, a ≫ P.differential = P.differential → IsIso a) →
        ∀ a, a ≫ Q.differential = Q.differential → IsIso a) ∧
      Q.projectiveClass = ProjectiveClass.of ⟨G, inferInstance⟩ +
        Module.finrank k (P.source ⟶ G) • P.projectiveClass ∧
      Function.Surjective (P.precompose (cokernel Q.differential)) ∧
      (∀ M : FGModuleCat.{u} R, Function.Surjective (P.precompose M) →
        Function.Surjective (Q.precompose M)) ∧
      ∀ M : FGModuleCat.{u} R, Function.Surjective (P.precompose M) →
        ∀ f : G ⟶ M, ∃ g, ι ≫ g = f := by
  classical
  let _ := P.projective_source
  let _ := P.projective_target
  have := finiteModuleHom_isFinite k P.source G
  let n := Module.finrank k (P.source ⟶ G)
  let b : Module.Basis (Fin n) k (P.source ⟶ G) := Module.finBasis k _
  let S : Fin n → FGModuleCat.{u} R := fun _ ↦ P.source
  let T : Fin n → FGModuleCat.{u} R := fun _ ↦ P.target
  let D : (⨁ S) ⟶ (⨁ T) := biproduct.map (fun _ ↦ P.differential)
  let H : (⨁ S) ⟶ G := biproduct.desc b
  let d : (⨁ S) ⟶ G ⊞ (⨁ T) := biprod.lift H D
  let _ := FGModuleCat.projective_biproduct S (fun _ ↦ P.projective_source)
  let _ := FGModuleCat.projective_biproduct T (fun _ ↦ P.projective_target)
  let _ := FGModuleCat.projective_biprod G (⨁ T)
  let Q := ofDifferential d
  let π := cokernel.π d
  have hd : d ≫ π = 0 := cokernel.condition d
  have hd₁ : d ≫ biprod.fst = H := biprod.lift_fst H D
  have hd₂ : d ≫ biprod.snd = D := biprod.lift_snd H D
  have hDι (i : Fin n) : biproduct.ι S i ≫ D = P.differential ≫ biproduct.ι T i := biproduct.ι_map _ _
  have hDπ (i : Fin n) : D ≫ biproduct.π T i = biproduct.π S i ≫ P.differential := biproduct.map_π _ _
  have hHι (i : Fin n) : biproduct.ι S i ≫ H = b i := biproduct.ι_desc _ _
  have hspan (r : P.source ⟶ G) : ∃ (a : P.source ⟶ ⨁ S) (c : P.target ⟶ ⨁ T),
      a ≫ H = r ∧ a ≫ D = P.differential ≫ c := by
    refine ⟨∑ i, b.repr r i • biproduct.ι S i, ∑ i, b.repr r i • biproduct.ι T i, ?_, ?_⟩
    · simp only [Preadditive.sum_comp, Linear.smul_comp, hHι, b.sum_repr]
    · simp only [Preadditive.sum_comp, Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul, hDι]
  have honto : Function.Surjective (P.precompose (cokernel Q.differential)) := by
    intro f
    change P.source ⟶ cokernel d at f
    obtain ⟨v, hv⟩ := FGModuleCat.exists_lift_of_projective π f
    have hpair (j : Fin n) : ∃ (a : P.source ⟶ P.source) (c : P.target ⟶ P.target),
        a ≫ P.differential + P.differential ≫ c = v ≫ biprod.snd ≫ biproduct.π T j := by
      obtain ⟨⟨a, c⟩, h⟩ := hP (v ≫ biprod.snd ≫ biproduct.π T j)
      exact ⟨a, -c, by simpa [homotopyBoundary, sub_eq_add_neg] using h⟩
    choose a c hc using hpair
    let a' : P.source ⟶ ⨁ S := biproduct.lift a
    let c' : P.target ⟶ ⨁ T := biproduct.lift c
    have h₂ : a' ≫ D + P.differential ≫ c' = v ≫ biprod.snd := by
      apply biproduct.hom_ext
      intro j
      have ha' : a' ≫ biproduct.π S j = a j := biproduct.lift_π (f := S) a j
      have hc' : c' ≫ biproduct.π T j = c j := biproduct.lift_π (f := T) c j
      rw [Preadditive.add_comp, Category.assoc a', hDπ, ← Category.assoc a',
        Category.assoc P.differential, Category.assoc v, ha', hc']
      exact hc j
    obtain ⟨a'', c'', h₁, hcomm⟩ := hspan (v ≫ biprod.fst - a' ≫ H)
    let g := (c' - c'') ≫ (biprod.inr : (⨁ T) ⟶ G ⊞ (⨁ T))
    have heq : (a' + a'') ≫ d + P.differential ≫ g = v := by
      apply biprod.hom_ext
      · simp only [Preadditive.add_comp, Category.assoc, hd₁, g, biprod.inr_fst, comp_zero, add_zero]
        rw [h₁]
        abel
      · simp only [Preadditive.add_comp, Category.assoc, hd₂, g, biprod.inr_snd, Category.comp_id]
        rw [hcomm, Preadditive.comp_sub, ← h₂]
        abel
    refine ⟨g ≫ π, ?_⟩
    change P.differential ≫ g ≫ π = f
    have hm := congrArg (fun w : P.source ⟶ G ⊞ (⨁ T) ↦ w ≫ π) heq
    rw [Preadditive.add_comp, Category.assoc (a' + a''), hd, comp_zero, zero_add, Category.assoc] at hm
    exact hm.trans hv
  have hfactor (M : FGModuleCat.{u} R) (h : Function.Surjective (P.precompose M))
      (f : (⨁ S) ⟶ M) : ∃ v : (⨁ T) ⟶ M, D ≫ v = f := by
    choose c hc using fun i : Fin n ↦ h (biproduct.ι S i ≫ f)
    refine ⟨biproduct.desc c, ?_⟩
    apply biproduct.hom_ext'
    intro i
    rw [← Category.assoc, hDι, Category.assoc, biproduct.ι_desc]
    exact hc i
  refine ⟨Q, biprod.inl ≫ π, ?_, ?_, ?_, honto, ?_, ?_⟩
  · intro K i r hir hi
    refine ⟨n,fun j ↦ i ≫ biproduct.π S j,fun j ↦ biproduct.ι S j ≫ r,?_,?_⟩
    · intro j
      have hv : i ≫ D = 0 := by rw [← hd₂,← Category.assoc,show i ≫ d = 0 from hi,zero_comp]
      have hπ : D ≫ biproduct.π T j = biproduct.π S j ≫ P.differential := biproduct.map_π _ _
      rw [Category.assoc,← hπ,← Category.assoc,hv,zero_comp]
    · have eq := congrArg (fun z : (⨁ S) ⟶ (⨁ S) ↦ i ≫ z ≫ r) (biproduct.total (f := S))
      refine Eq.trans ?_ ((congrArg (i ≫ ·) (Category.id_comp r)).trans hir)
      simpa only [Preadditive.sum_comp,Preadditive.comp_sum,Category.assoc] using eq
  · intro hm a ha
    apply rightMinimal_power_map hm n a
    change a ≫ d = d at ha
    change a ≫ D = D
    rw [← hd₂, ← Category.assoc, ha]
  · change ProjectiveClass.of (ProjectiveClass.biprod ⟨G, inferInstance⟩ ⟨⨁ T, inferInstance⟩) -
        ProjectiveClass.of ⟨⨁ S, inferInstance⟩ = _
    rw [ProjectiveClass.of_biprod, ProjectiveClass.of_copies ⟨P.target, P.projective_target⟩,
      ProjectiveClass.of_copies ⟨P.source, P.projective_source⟩]
    simp only [projectiveClass, nsmul_sub]
    abel
  · intro M h f
    obtain ⟨v, hv⟩ := hfactor M h f
    refine ⟨biprod.snd ≫ v, ?_⟩
    change d ≫ biprod.snd ≫ v = f
    rw [← Category.assoc, hd₂, hv]
  · intro M h f
    obtain ⟨v, hv⟩ := hfactor M h (-(H ≫ f))
    have hz : d ≫ biprod.desc f v = 0 := by
      change biprod.lift H D ≫ biprod.desc f v = 0
      rw [biprod.lift_desc, hv, add_neg_cancel]
    exact ⟨cokernel.desc d _ hz, by rw [Category.assoc, cokernel.π_desc, biprod.inl_desc]⟩

include k in
theorem exists_bongartz_at_projective_rightMinimal (P : TwoTerm R) (hP : P.IsPresilting) (G : FGModuleCat.{u} R)
    [Module.Projective R G] :
    ∃ (Q : TwoTerm R) (ι : G ⟶ cokernel Q.differential),
      ((∀ a, a ≫ P.differential = P.differential → IsIso a) →
        ∀ a, a ≫ Q.differential = Q.differential → IsIso a) ∧
      Q.projectiveClass = ProjectiveClass.of ⟨G, inferInstance⟩ +
        Module.finrank k (P.source ⟶ G) • P.projectiveClass ∧
      Function.Surjective (P.precompose (cokernel Q.differential)) ∧
      (∀ M : FGModuleCat.{u} R, Function.Surjective (P.precompose M) →
        Function.Surjective (Q.precompose M)) ∧
      ∀ M : FGModuleCat.{u} R, Function.Surjective (P.precompose M) →
        ∀ f : G ⟶ M, ∃ g, ι ≫ g = f := by
  obtain ⟨Q,i,_,h⟩ := exists_bongartz_at_projective_with_source k P hP G
  exact ⟨Q,i,h⟩

include k in
theorem exists_bongartz_at_projective (P : TwoTerm R) (hP : P.IsPresilting) (G : FGModuleCat.{u} R)
    [Module.Projective R G] :
    ∃ (Q : TwoTerm R) (ι : G ⟶ cokernel Q.differential),
      Q.projectiveClass = ProjectiveClass.of ⟨G, inferInstance⟩ +
        Module.finrank k (P.source ⟶ G) • P.projectiveClass ∧
      Function.Surjective (P.precompose (cokernel Q.differential)) ∧
      (∀ M : FGModuleCat.{u} R, Function.Surjective (P.precompose M) →
        Function.Surjective (Q.precompose M)) ∧
      ∀ M : FGModuleCat.{u} R, Function.Surjective (P.precompose M) →
        ∀ f : G ⟶ M, ∃ g, ι ≫ g = f := by
  obtain ⟨Q,ι,_,hg,hPQ,hQ,hfac⟩ := exists_bongartz_at_projective_rightMinimal k P hP G
  exact ⟨Q,ι,hg,hPQ,hQ,hfac⟩

include k in
/-- A Bongartz complement in two-term form. Its cokernel generates the
weak torsion class, and its Hom differential is surjective into every
object of that class. -/
theorem exists_bongartz_complement (P : TwoTerm R) (hP : P.IsPresilting) :
    ∃ Q : TwoTerm R,
      Function.Surjective (P.precompose (cokernel Q.differential)) ∧
      (∀ M : FGModuleCat.{u} R, Function.Surjective (P.precompose M) →
        Function.Surjective (Q.precompose M)) ∧
      ∀ M : FGModuleCat.{u} R, Function.Surjective (P.precompose M) ↔
        IsGeneratedBy (cokernel Q.differential) M := by
  let G := FGModuleCat.of R R
  let _ : Module.Projective R G := inferInstanceAs (Module.Projective R R)
  obtain ⟨Q,ι,_,honto,hQ,hreg⟩ := exists_bongartz_at_projective k P hP G
  refine ⟨Q,honto,hQ,fun M ↦ ⟨?_,fun h ↦ P.surjective_precompose_of_generatedBy honto h⟩⟩
  intro h
  obtain ⟨V, i, _, hV, hkill⟩ := exists_generated_subobject_killing_hom k (cokernel Q.differential) M
  have hz : cokernel.π i = 0 := eq_zero_of_regular_comp_eq_zero _ (fun f ↦ by
      obtain ⟨g, hg⟩ := hreg M h f
      rw [← hg, Category.assoc, hkill, comp_zero])
  have : Epi i := Abelian.epi_of_cokernel_π_eq_zero _ hz
  exact hV.of_epi i

end TwoTerm

end EFiniteCharacterizations
