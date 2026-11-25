module

public import EFiniteCharacterizations.Geometry.ZariskiLoci
public import EFiniteCharacterizations.Modules.HomDimension
public import EFiniteCharacterizations.Stability.PolystableClasses
public import EFiniteCharacterizations.Subcategories.BrickFiltrations
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Hom-vanishing loci for based representations -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {ι m n : Type*} [Fintype ι] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Matrices of the action of the chosen algebra basis on a based module. -/
noncomputable def actionMatrices (b : Module.Basis ι k R) {M : FGModuleCat.{u} R}
    (v : Module.Basis m k (M.obj : Type u)) (j : ι) : Matrix m m k :=
  LinearMap.toMatrix v v (Algebra.lsmul k k (M.obj : Type u) (b j))

theorem subsingleton_hom_iff_zero_intertwiners (b : Module.Basis ι k R)
    {M N : FGModuleCat.{u} R} (v : Module.Basis n k (M.obj : Type u))
    (w : Module.Basis m k (N.obj : Type u)) :
    Subsingleton (M ⟶ N) ↔ ∀ T : Matrix m n k,
      (∀ j, actionMatrices b w j * T = T * actionMatrices b v j) → T = 0 := by
  let AM : R →ₐ[k] Module.End k (M.obj : Type u) := Algebra.lsmul k k (M.obj : Type u)
  let AN : R →ₐ[k] Module.End k (N.obj : Type u) := Algebra.lsmul k k (N.obj : Type u)
  have commute (f : (M.obj : Type u) →ₗ[k] (N.obj : Type u)) (j : ι) :
      actionMatrices b w j * LinearMap.toMatrix v w f = LinearMap.toMatrix v w f * actionMatrices b v j ↔
      (AN (b j)).comp f = f.comp (AM (b j)) := by
    unfold actionMatrices
    rw [← LinearMap.toMatrix_comp v w w,← LinearMap.toMatrix_comp v v w]
    exact (LinearMap.toMatrix v w).injective.eq_iff
  constructor
  · intro hs T hT
    let f := Matrix.toLin v w T
    have hf (r : R) (x : M) : f (r • x) = r • f x := by
      have hb (j : ι) : f (b j • x) = b j • f x := by
        have h := (commute f j).1 (by simpa [f] using hT j)
        exact (LinearMap.congr_fun h x).symm
      conv_lhs => rw [← b.sum_repr r, Finset.sum_smul, map_sum]
      conv_rhs => rw [← b.sum_repr r, Finset.sum_smul]
      exact Finset.sum_congr rfl fun j _ ↦ by simp [smul_assoc,map_smul,hb]
    let g : M ⟶ N := FGModuleCat.ofHom (R := R) { f.toAddHom with map_smul' := hf }
    have hz := hs.elim g 0
    have hzero : f = 0 := LinearMap.ext fun x ↦ congrArg (fun h : M ⟶ N ↦ h.hom.hom x) hz
    simpa [f] using congrArg (LinearMap.toMatrix v w) hzero
  · intro hT
    suffices ∀ f : M ⟶ N, f = 0 from ⟨fun f g ↦ (this f).trans (this g).symm⟩
    intro f
    let g := f.hom.hom.restrictScalars k
    have he := hT (LinearMap.toMatrix v w g) fun j ↦ (commute g j).2
      (LinearMap.ext fun x ↦ (f.hom.hom.map_smul (b j) x).symm)
    have hz : g = 0 := (LinearMap.toMatrix v w).injective (by simpa using he)
    exact FGModuleCat.hom_ext (LinearMap.ext fun x ↦ LinearMap.congr_fun hz x)

section Families

variable [Module.Finite k R] {X σ : Type*} (c : X → σ → k) (M : X → FGModuleCat.{u} R)
    (v : ∀ x, Module.Basis n k ((M x).obj : Type u)) (b : Module.Basis ι k R)
    (A : ι → Matrix n n (MvPolynomial σ k))
    (hA : ∀ x j, (A j).map (MvPolynomial.eval (c x)) = actionMatrices b (v x) j)

include v b A hA in
/-- Both Hom perpendiculars to a fixed module are open in a polynomial
family of representations. -/
theorem isOpen_hom_perpendiculars (N : FGModuleCat.{u} R) :
    @IsOpen X (coordinateZariski c) {x | Subsingleton (N ⟶ M x)} ∧
    @IsOpen X (coordinateZariski c) {x | Subsingleton (M x ⟶ N)} := by
  classical
  let _ : Module.Finite R (N.obj : Type u) := N.property
  let _ : Module.Finite k (N.obj : Type u) := Module.Finite.trans R _
  let w := Module.finBasis k (N.obj : Type u)
  let B j := (actionMatrices b w j).map (MvPolynomial.C : k →+* MvPolynomial σ k)
  have hB x j : (B j).map (MvPolynomial.eval (c x)) = actionMatrices b w j := by
    ext i h
    simp [B,Matrix.map_apply]
  constructor
  · convert coordinateZariski_isOpen_zero_intertwiners c A B using 1
    ext x
    simpa only [Set.mem_ofPred_eq,hA,hB] using subsingleton_hom_iff_zero_intertwiners b w (v x)
  · convert coordinateZariski_isOpen_zero_intertwiners c B A using 1
    ext x
    simpa only [Set.mem_ofPred_eq,hA,hB] using subsingleton_hom_iff_zero_intertwiners b (v x) w

variable [IsNoetherianRing R] [IsArtinianRing R]

include v b A hA in
omit [IsArtinianRing R] in
theorem isOpen_semistable_of_isEFinite (he : IsEFinite R) (g : ProjectiveClass R) :
    @IsOpen X (coordinateZariski c) {x | (projectiveClassWeight k g).IsSemistable (M x)} := by
  obtain ⟨P,hP,rfl⟩ := he g
  rw [P.projectiveClassWeight_eq_eulerWeight k]
  simp_rw [P.isSemistable_eulerWeight_iff_perpendicular k hP]
  let _ := coordinateZariski c
  exact (isOpen_hom_perpendiculars c M v b A hA _).1.inter (isOpen_hom_perpendiculars c M v b A hA _).2

include v b A hA in
theorem isOpen_wide_of_isEFinite (he : IsEFinite R)
    (hc : ∀ x y, GrothendieckGroup.of (M x) = GrothendieckGroup.of (M y))
    {W : ObjectProperty (FGModuleCat.{u} R)} (hw : IsWideClass W) :
    @IsOpen X (coordinateZariski c) {x | W (M x)} := by
  by_cases hn : ∃ x, W (M x)
  · obtain ⟨x,hx⟩ := hn
    obtain ⟨g,hg⟩ := exists_weight_for_wide_class_slices k he hw
    simpa only [hg _ _ hx (hc x _)] using isOpen_semistable_of_isEFinite c M v b A hA he g
  · have hz : {x | W (M x)} = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x h ↦ hn ⟨x,h⟩
    rw [hz]
    exact @isOpen_empty X (coordinateZariski c)

open CategoryTheory.Limits in
theorem filteredBy_iff_iso_of_equal_class {B Y : FGModuleCat.{u} R}
    (hc : GrothendieckGroup.of Y = GrothendieckGroup.of B) :
    FilteredBy B Y ↔ Nonempty (Y ≅ B) := by
  classical
  constructor
  · intro hf
    cases hf with
    | zero hz =>
      have hb : IsZero B := by
        by_contra hn
        exact FGModuleCat.class_ne_zero hn (hc.symm.trans (GrothendieckGroup.of_isZero hz))
      exact ⟨hz.iso hb⟩
    | @cons S Y Q row e _ =>
      have hr := GrothendieckGroup.of_shortExact _ row.shortExact
      rw [hc,GrothendieckGroup.of_eq_of_iso e] at hr
      have hq := add_left_cancel (hr.symm.trans (add_zero _).symm)
      have hz : IsZero Q := by
        by_contra hn
        exact FGModuleCat.class_ne_zero hn hq
      have : IsIso row.i := row.shortExact.isIso_f_iff.mpr hz
      exact ⟨(asIso row.i).symm ≪≫ e⟩
  · rintro ⟨e⟩
    exact (.cons (ExtensionSequence.idLeft _) (Iso.refl B) (.zero (isZero_zero _)) : FilteredBy B B).of_iso
      (Iso.refl _) e.symm

include v b A hA in
theorem isOpen_brick_iso_of_isEFinite (he : IsEFinite R) (B : FGModuleCat.{u} R) (hb : IsBrick B)
    (hc : ∀ x, GrothendieckGroup.of (M x) = GrothendieckGroup.of B) :
    @IsOpen X (coordinateZariski c) {x | Nonempty (M x ≅ B)} := by
  obtain ⟨_,hs⟩ := exists_projective_weight_stable_of_isEFinite k he hb
  simpa only [filteredBy_iff_iso_of_equal_class (hc _)] using
    isOpen_wide_of_isEFinite c M v b A hA he (fun x y ↦ (hc x).trans (hc y).symm)
      (isWideClass_filteredBy_of_stable hs)

end Families

section OpenFibers

variable [IsNoetherianRing R] [IsArtinianRing R] {X σ : Type*} [Finite σ]
    (c : X → σ → k) (M : X → FGModuleCat.{u} R)

omit [Algebra k R] [IsNoetherianRing R] [IsArtinianRing R] in
/-- Open brick orbits imply finiteness of the brick classes in any vector
represented by the parameter space. -/
theorem finite_bricks_of_open_iso_loci (d : GrothendieckGroup (FGModuleCat.{u} R))
    (rep : ∀ B : FGModuleCat.{u} R, IsBrick B → GrothendieckGroup.of B = d → ∃ x, Nonempty (M x ≅ B))
    (ho : ∀ B : FGModuleCat.{u} R, IsBrick B → GrothendieckGroup.of B = d →
      @IsOpen X (coordinateZariski c) {x | Nonempty (M x ≅ B)}) :
    (brickClassesOfClass d).Finite := by
  apply coordinateZariski_finite_open_fibers c (fun x ↦ toSkeleton (M x))
  · rintro _ ⟨B,rfl,hc,hb⟩
    obtain ⟨x,hx⟩ := rep _ hb hc
    exact ⟨x,toSkeleton_eq_toSkeleton_iff.2 hx⟩
  · rintro _ ⟨B,rfl,hc,hb⟩
    change @IsOpen X (coordinateZariski c) {x | toSkeleton (M x) = toSkeleton B}
    simpa only [toSkeleton_eq_toSkeleton_iff] using ho _ hb hc

omit [Algebra k R] in
/-- At a fixed class, openness of all wide loci implies finiteness of the
stable isomorphism classes at each weight. Only filtrations by stable modules
are needed. -/
theorem finite_stables_of_open_wide_loci (θ : Weight (FGModuleCat.{u} R))
    (d : GrothendieckGroup (FGModuleCat.{u} R)) (hc : ∀ x, GrothendieckGroup.of (M x) = d)
    (rep : ∀ B : FGModuleCat.{u} R, θ.IsStable B → GrothendieckGroup.of B = d → ∃ x, Nonempty (M x ≅ B))
    (ho : ∀ W : ObjectProperty (FGModuleCat.{u} R), IsWideClass W →
      @IsOpen X (coordinateZariski c) {x | W (M x)}) :
    (stableClassesOfClass θ d).Finite := by
  apply coordinateZariski_finite_open_fibers c (fun x ↦ toSkeleton (M x))
  · rintro _ ⟨B,rfl,hd,hb⟩
    obtain ⟨x,hx⟩ := rep _ hb hd
    exact ⟨x,toSkeleton_eq_toSkeleton_iff.2 hx⟩
  · rintro _ ⟨B,rfl,hd,hb⟩
    change @IsOpen X (coordinateZariski c) {x | toSkeleton (M x) = toSkeleton B}
    simpa only [toSkeleton_eq_toSkeleton_iff,
      filteredBy_iff_iso_of_equal_class ((hc _).trans hd.symm)] using ho _ (isWideClass_filteredBy_of_stable hb)

end OpenFibers

end EFiniteCharacterizations
