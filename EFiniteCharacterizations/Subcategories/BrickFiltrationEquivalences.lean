module

public import EFiniteCharacterizations.Stability.IsolatedRepresentations
public import EFiniteCharacterizations.Subcategories.TorsionGeneratorPresentation
public import EFiniteCharacterizations.Subcategories.BrickFiltrations
public import Mathlib.RingTheory.LittleWedderburn

/-!
# Functorial finiteness of single-brick filtration subcategories

Theorem 5.1 (`thm:wide`, condition `(wide₁)` in Theorem A(I)): proves
`isEFinite_iff_functoriallyFinite_filteredBy`, showing over any field that `R` is
E-finite if and only if `Filt(B)` (`FilteredBy B`) is functorially finite for every
brick `B` in `mod R`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra ZeroObject

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
private theorem exists_free_epi (G : FGModuleCat.{u} R) :
    ∃ (a : ℕ) (p : FreeHom.freeModule R a ⟶ G), Epi p := by
  have := G.property
  obtain ⟨a,p,hp⟩ := Module.Finite.exists_fin' R G
  exact ⟨a,FGModuleCat.ofHom p,(FGModuleCat.epi_iff_surjective _).2 hp⟩

private theorem extends_across_kernel {T : ObjectProperty (FGModuleCat.{u} R)}
    (hT : IsWideClass T) {G X P : FGModuleCat.{u} R} (hG : T G) (hX : T X)
    (hs : ∀ E, T E → ∀ r : E ⟶ G, Epi r → ∃ s, s ≫ r = 𝟙 G)
    (q : P ⟶ G) [Epi q] (f : kernel q ⟶ X) : ∃ g : P ⟶ X, kernel.ι q ≫ g = f := by
  let i := kernel.ι q
  let e := pushout.inl i f
  let j := pushout.inr i f
  let r : pushout i f ⟶ G := pushout.desc q (0 : X ⟶ G) (by rw [kernel.condition,comp_zero])
  have he : e ≫ r = q := pushout.inl_desc ..
  have hj : j ≫ r = 0 := pushout.inr_desc ..
  have : Epi r := epi_of_epi_fac he
  have hr := CokernelCofork.IsColimit.ofπ' r hj (fun {Y} b hb ↦ by
    have hz : i ≫ e ≫ b = 0 := by rw [← Category.assoc,pushout.condition,Category.assoc,hb,comp_zero]
    let t := Abelian.epiDesc q (e ≫ b) hz
    refine ⟨t,?_⟩
    apply pushout.hom_ext
    · change e ≫ r ≫ t = _
      rw [← Category.assoc,he,Abelian.comp_epiDesc]
    · change j ≫ r ≫ t = _
      rw [← Category.assoc,hj,zero_comp,hb])
  let S := ShortComplex.mk j r hj
  have hS : S.ShortExact := .mk' (ShortComplex.exact_of_g_is_cokernel _ hr)
    (by dsimp [S,j,i]; infer_instance) (by assumption)
  obtain ⟨s,h⟩ := hs _ (hT.extension_mem S hS hX hG) r inferInstance
  let spl := ShortComplex.Splitting.ofExactOfSection S hS.exact s h hS.mono_f
  exact ⟨e ≫ spl.r,by rw [← Category.assoc,pushout.condition,Category.assoc,spl.f_r,Category.comp_id]⟩

private theorem FilteredBy.hom_eq_zero {B G Y : FGModuleCat.{u} R}
    (h : FilteredBy B G) (hb : ∀ f : B ⟶ Y, f = 0) (f : G ⟶ Y) : f = 0 := by
  induction h with
  | zero hz => exact hz.eq_of_src f 0
  | cons s e hq ih =>
    have hzero : s.i ≫ f = 0 := (cancel_epi e.inv).1 ((hb _).trans comp_zero.symm)
    obtain ⟨b,hh⟩ := CokernelCofork.IsColimit.desc' s.shortExact.gIsCokernel f hzero
    exact hh.symm.trans ((congrArg (s.p ≫ ·) (ih b)).trans comp_zero)

/-- A module separating one member of a family by Hom, with extension of
maps from each first syzygy, yields a three-term isolating free complex. -/
theorem exists_isolating_complex_of_module {I : Type*} (X : I → FGModuleCat.{u} R) (i : I)
    (G : FGModuleCat.{u} R) (hHom : ∃ z : G ⟶ X i, z ≠ 0)
    (hExt : ∀ (a : ℕ) (p : FreeHom.freeModule R a ⟶ G) [Epi p] (z : kernel p ⟶ X i),
      ∃ s : FreeHom.freeModule R a ⟶ X i, kernel.ι p ≫ s = z)
    (hOff : ∀ j, i ≠ j → ∀ z : G ⟶ X j, z = 0) :
    ∃ (a b c : ℕ) (f : FreeHom.freeModule R b ⟶ FreeHom.freeModule R a)
      (g : FreeHom.freeModule R c ⟶ FreeHom.freeModule R b),
      g ≫ f = 0 ∧ (∃ p : FreeHom.freeModule R a ⟶ X i, p ≠ 0 ∧ f ≫ p = 0) ∧
      (∀ q : FreeHom.freeModule R b ⟶ X i, g ≫ q = 0 → ∃ p, f ≫ p = q) ∧
      ∀ j, i ≠ j → ∀ p : FreeHom.freeModule R a ⟶ X j, f ≫ p = 0 → p = 0 := by
  obtain ⟨a,p,hp⟩ := exists_free_epi G
  obtain ⟨b,q,hq⟩ := exists_free_epi (kernel p)
  obtain ⟨c,r,hr⟩ := exists_free_epi (kernel q)
  let f := q ≫ kernel.ι p
  let g := r ≫ kernel.ι q
  have hp₀ : f ≫ p = 0 := by simp [f]
  refine ⟨a,b,c,f,g,by simp [g,f],?_,?_,?_⟩
  · obtain ⟨z,hz⟩ := hHom
    exact ⟨p ≫ z, fun h ↦ hz ((cancel_epi p).1 (h.trans comp_zero.symm)),by rw [← Category.assoc,hp₀,zero_comp]⟩
  · intro t ht
    have hk : kernel.ι q ≫ t = 0 := (cancel_epi r).1 (by simpa [g,Category.assoc] using ht)
    let z := Abelian.epiDesc q t hk
    obtain ⟨s,hs⟩ := hExt a p z
    exact ⟨s,by rw [show f ≫ s = q ≫ kernel.ι p ≫ s from Category.assoc ..,hs,Abelian.comp_epiDesc]⟩
  · intro j hij t ht
    have hk : kernel.ι p ≫ t = 0 := (cancel_epi q).1 (by simpa [f,Category.assoc] using ht)
    let z := Abelian.epiDesc p t hk
    have hz := hOff j hij z
    exact (Abelian.comp_epiDesc p t hk).symm.trans ((congrArg (p ≫ ·) hz).trans comp_zero)

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R] [IsArtinianRing R]

include k in
private theorem exists_isolating_complex {I : Type*} (X : I → FGModuleCat.{u} R)
    {θ : Weight (FGModuleCat.{u} R)} (hst : ∀ i, θ.IsStable (X i))
    (hd : ∀ i j, i ≠ j → ¬ Nonempty (X i ≅ X j))
    (hc : ∀ i, CovariantlyFinite (FilteredBy (X i))) (i : I) :
    ∃ (a b c : ℕ) (f : FreeHom.freeModule R b ⟶ FreeHom.freeModule R a)
      (g : FreeHom.freeModule R c ⟶ FreeHom.freeModule R b),
      g ≫ f = 0 ∧ (∃ p : FreeHom.freeModule R a ⟶ X i, p ≠ 0 ∧ f ≫ p = 0) ∧
      (∀ q : FreeHom.freeModule R b ⟶ X i, g ≫ q = 0 → ∃ p, f ≫ p = q) ∧
      ∀ j, i ≠ j → ∀ p : FreeHom.freeModule R a ⟶ X j, f ≫ p = 0 → p = 0 := by
  classical
  let T := FilteredBy (X i)
  have hT : IsWideClass T := isWideClass_filteredBy_of_stable (hst i)
  have hX : T (X i) := .cons (ExtensionSequence.idLeft _) (Iso.refl _) (.zero (isZero_zero _))
  obtain ⟨G,a₀,hG,ha,_,hsplit⟩ := exists_splitting_generator k T (fun h f ↦ hT.image_mem f h h) (hc i)
  apply exists_isolating_complex_of_module X i G
  · have : Nontrivial ((X i).obj : Type u) := not_subsingleton_iff_nontrivial.mp
      ((hst i).1 ∘ (FGModuleCat.isZero_iff_subsingleton _).2)
    obtain ⟨x,hx⟩ := exists_ne (0 : (X i).obj)
    let z : FGModuleCat.of R R ⟶ X i := FGModuleCat.ofHom (LinearMap.toSpanSingleton R (X i) x)
    obtain ⟨b₀,hb⟩ := ha _ hX z
    refine ⟨b₀,fun hz ↦ hx ?_⟩
    rw [hz, comp_zero] at hb
    exact (LinearMap.toSpanSingleton_apply_one R _ x).symm.trans
      (congrArg (fun t : FGModuleCat.of R R ⟶ X i ↦ t.hom.hom 1) hb.symm)
  · exact fun _ p _ z ↦ extends_across_kernel hT hG hX hsplit p z
  · exact fun j hij ↦ hG.hom_eq_zero (Weight.hom_eq_zero_of_not_iso (hst i) (hst j) (hd i j hij))


/-- Only finitely many distinct stable modules of a fixed ground dimension
can all have covariantly finite single-brick filtration categories. -/
theorem finite_covariantlyFinite_stable_of_dimension
    {I : Type*} (X : I → FGModuleCat.{u} R) (θ : Weight (FGModuleCat.{u} R))
    (hs : ∀ i, θ.IsStable (X i)) (hi : ∀ i j, i ≠ j → ¬ Nonempty (X i ≅ X j))
    (hc : ∀ i, CovariantlyFinite (FilteredBy (X i))) {d : ℕ}
    (hd : ∀ i, Module.finrank k ((X i).obj : Type u) = d) : Finite I := by
  classical
  let _ (i : I) : Module.Finite k ((X i).obj : Type u) := Module.Finite.trans R _
  let b (i : I) := (Module.finBasis k ((X i).obj : Type u)).reindex (finCongr (hd i))
  exact FreeHom.finite_of_isolating_complexes k X (fun _ ↦ k) b (exists_isolating_complex k X hs hi hc)

/-- Over a finite field the same finiteness holds at fixed endolength. -/
theorem finite_covariantlyFinite_stable_of_endolength [Finite k]
    {I : Type*} (X : I → FGModuleCat.{u} R) (θ : Weight (FGModuleCat.{u} R))
    (hs : ∀ i, θ.IsStable (X i)) (hi : ∀ i j, i ≠ j → ¬ Nonempty (X i ≅ X j))
    (hc : ∀ i, CovariantlyFinite (FilteredBy (X i))) {r : ℕ}
    (hd : ∀ i, endolength k (X i) = r) : Finite I := by
  classical
  let D (i : I) := Module.End R ((X i).obj : Type u)
  let _ (i : I) : DivisionRing (D i) := (hs i).isBrick.endomorphismDivisionRing k
  let _ (i : I) : Module.Finite k ((X i).obj : Type u) := Module.Finite.trans R _
  let _ (i : I) : Finite ((X i).obj : Type u) := Module.finite_of_finite k
  let _ (i : I) : Finite (D i) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let _ (i : I) : Field (D i) := littleWedderburn _
  let _ (i : I) : Module.Finite (D i) ((X i).obj : Type u) := Module.Finite.of_restrictScalars_finite k _ _
  have hdim (i : I) : Module.finrank (D i) ((X i).obj : Type u) = r :=
    ((hs i).isBrick.endolength_eq_finrank k).symm.trans (hd i)
  let b i := (Module.finBasis (D i) ((X i).obj : Type u)).reindex (finCongr (hdim i))
  exact FreeHom.finite_of_isolating_complexes k X D b (exists_isolating_complex k X hs hi hc)

include k in
theorem isEFinite_iff_covariantlyFinite_filteredBy :
    IsEFinite R ↔ ∀ B : FGModuleCat.{u} R, IsBrick B → CovariantlyFinite (FilteredBy B) := by
  classical
  refine ⟨fun he B hb ↦ (functoriallyFinite_filteredBy_of_isEFinite k he B hb).1,fun hc ↦ ?_⟩
  by_contra hn
  rcases finite_or_infinite k with hfin | hinf
  · obtain ⟨g,r,_,hi⟩ := exists_infinite_stableClassesOfEndolength_allFields k hn
    let I := stableClassesOfEndolength k (projectiveClassWeight (R := R) k g) r
    choose X hx hd hs using fun i : I ↦ i.property
    have : Finite I := finite_covariantlyFinite_stable_of_endolength k X _ hs (fun i j hn ⟨e⟩ ↦ hn (Subtype.ext
      ((hx i).symm.trans ((congr_toSkeleton_of_iso e).trans (hx j))))) (fun i ↦ hc _ (hs i).isBrick) hd
    exact hi (Set.toFinite I)
  · obtain ⟨d,g,hi⟩ := exists_infinite_stableClassesOfDimension_at_projectiveWeight_of_not_isEFinite k hn
    let I := stableClassesOfDimension k (projectiveClassWeight (R := R) k g) d
    choose X hx hd hs using fun i : I ↦ i.property
    have : Finite I := finite_covariantlyFinite_stable_of_dimension k X _ hs (fun i j hn ⟨e⟩ ↦ hn (Subtype.ext
      ((hx i).symm.trans ((congr_toSkeleton_of_iso e).trans (hx j))))) (fun i ↦ hc _ (hs i).isBrick) hd
    exact hi (Set.toFinite I)

include k in
theorem isEFinite_iff_functoriallyFinite_filteredBy :
    IsEFinite R ↔ ∀ B : FGModuleCat.{u} R, IsBrick B → FunctoriallyFinite (FilteredBy B) :=
  ⟨functoriallyFinite_filteredBy_of_isEFinite k,fun h ↦
    (isEFinite_iff_covariantlyFinite_filteredBy k).2 (fun B hb ↦ (h B hb).1)⟩

end EFiniteCharacterizations
