module

public import EFiniteCharacterizations.Stability.CommonStableClass
public import EFiniteCharacterizations.Silting.Fans.ConeSaturation
public import EFiniteCharacterizations.Stability.StableSubobjects
public import EFiniteCharacterizations.Stability.SubmodulePolytopes

/-!
# Stable bricks from integral weights outside the `g`-vector fan

Propositions 2.7 (`prop:mp-witness`, after Mousavand–Paquette) and 2.8
(`prop:stable-witnesses`) of the manuscript:

* `exists_hom_of_class_outside_fan` and `minimal_image_stable_at_corrected_class`:
  any differential `p` representing `g ∉ Σ(R)` admits a nonzero morphism
  `coker p → ker(νp)`, and the image `B` of such a morphism of minimal `k`-dimension
  is a brick stable at the corrected integral weight `(dim_k B) g - ⟨g, [B]⟩ [R]`.
* `exists_occurrence_polynomial` and `exists_infinite_stable_classes_of_outside_fan`:
  each fixed brick occurs only on a proper determinantal hypersurface, yielding
  infinitely many nonisomorphic bricks of one dimension vector and integral weight
  when `k` is infinite.
* `exists_equal_class_polytope_stable_pair`: over every field, an E-infinite algebra
  admits two nonisomorphic bricks stable at a common integral weight with the same
  dimension vector and submodule polytope.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations
namespace TwoTerm

variable {R : Type u} [Ring R] [IsNoetherianRing R] (k : Type u) [Field k] [Algebra k R]
  [Module.Finite k R]

/-- The integral projective class correcting the weight of P at the image B. -/
noncomputable def correctedProjectiveClass (P : TwoTerm R) (B : FGModuleCat.{u} R) : ProjectiveClass R :=
  (Module.finrank k (B.obj : Type u) : ℤ) • P.projectiveClass -
    (P.eulerWeight k).eval B • ProjectiveClass.of (⟨FGModuleCat.of R R,inferInstance⟩ : FiniteProjective R)

/-- Every nonzero map of smallest ground-field image dimension gives a brick
of the prescribed dimension bound, stable at the explicit integral weight. -/
theorem minimal_image_stable_at_corrected_class (P : TwoTerm R)
    (f : cokernel P.differential ⟶ P.nakayamaKernel k) (hf : f ≠ 0)
    (hmin : ∀ g : cokernel P.differential ⟶ P.nakayamaKernel k, g ≠ 0 →
      Module.finrank k ((image f).obj : Type u) ≤ Module.finrank k ((image g).obj : Type u)) :
    IsBrick (image f) ∧ Module.finrank k ((image f).obj : Type u) ≤ Module.finrank k (P.target.obj : Type u) ∧
      (projectiveClassWeight k (P.correctedProjectiveClass k (image f))).IsStable (image f) := by
  let dim (M : FGModuleCat.{u} R) := Module.finrank k (M.obj : Type u)
  have hiso {A B : FGModuleCat.{u} R} (e : A ≅ B) : dim A = dim B :=
    ((FGModuleCat.isoToLinearEquiv e).restrictScalars k).finrank_eq
  have hstrict {A B : FGModuleCat.{u} R} (q : A ⟶ B) [Epi q] (hq : ¬ IsIso q) : dim B < dim A := by
    apply (groundFinrank_le_of_epi k q).lt_of_ne
    intro he
    have hs := (FGModuleCat.epi_iff_surjective q).1 inferInstance
    have : Module.Finite k (A.obj : Type u) := Module.Finite.trans R _
    have : Module.Finite k (B.obj : Type u) := Module.Finite.trans R _
    exact hq ((FGModuleCat.isIso_iff_bijective q).2
      ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank he.symm (f := q.hom.hom.restrictScalars k)).2 hs,hs⟩)
  have hn : ¬ IsZero (image f) := fun h ↦ hf (by rw [← image.fac f,h.eq_of_tgt (factorThruImage f) 0,zero_comp])
  have hstable := stable_image_of_hom_vanishing k (P.eulerWeight k) (dimensionWeight (R := R) k)
    (dimensionWeight_pos k) (fun M ↦ (P.eulerWeight_eval k M).trans (P.euler_eq_hom_difference k M)) f hn
    (fun i _ hi ↦ hom_to_proper_subobject_of_minimal_image_size f dim hiso
      (fun a _ ha ↦ groundFinrank_lt_of_mono_not_iso k a ha) hmin i hi)
    (fun q _ hq ↦ hom_from_proper_quotient_of_minimal_image_size f dim hiso
      (fun a _ ha ↦ hstrict a ha) hmin q hq)
  refine ⟨hstable.isBrick, groundFinrank_le_of_epi k (cokernel.π P.differential ≫ factorThruImage f),?_⟩
  rw [Weight.corrected,dimensionWeight_eval] at hstable
  simpa only [correctedProjectiveClass, map_sub, map_zsmul, projectiveClassWeight_eq_eulerWeight,
    projectiveClassWeight_of, dimensionWeight] using hstable

/-- A missing integral class forces a nonzero map for each differential of that class. -/
theorem exists_hom_of_class_outside_fan (P : TwoTerm R)
    (hm : realProjectiveClass R P.projectiveClass ∉ gVectorFanSupport R) :
    ∃ f : cokernel P.differential ⟶ P.nakayamaKernel k, f ≠ 0 :=
  P.exists_nonzero_hom_of_not_isPresilting k (fun hp ↦ hm ⟨P,hp,P.class_mem_gVectorCone⟩)

/-- The occurrence locus for a fixed module, with the degree bound on the
actual source of the differential and the actual module. -/
theorem exists_occurrence_polynomial {ι : Type*} [Fintype ι]
    (P₁ P₀ M : FGModuleCat.{u} R) [Module.Projective R P₁] [Module.Projective R P₀]
    (b : Module.Basis ι k (P₁ ⟶ P₀)) :
    ∃ D : MvPolynomial ι k, D ≠ 0 ∧ D.totalDegree ≤ Module.finrank k (P₁.obj : Type u) *
      Module.finrank k (M.obj : Type u) ∧ ∀ (p : P₁ ⟶ P₀) (q : cokernel p ⟶ M), Epi q →
      (∃ g : M ⟶ (ofDifferential p).nakayamaKernel k, g ≠ 0) → MvPolynomial.eval (b.repr p) D = 0 := by
  obtain ⟨D,hn,hd,h⟩ := exists_polynomial_vanishing_at_presentation_occurrences k P₁ P₀ M b
  exact ⟨D,hn,hd.trans (homFinrank_le_mul k P₁ M),fun p q _ hM ↦
    h p (cokernel.π p ≫ q) inferInstance (by simp) hM⟩

/-- A missing weight over an infinite field gives infinitely many stable
isomorphism classes for one integral projective weight and one module class. -/
theorem exists_infinite_stable_classes_of_outside_fan [Infinite k] (v : ProjectiveClass R)
    (hv : realProjectiveClass R v ∉ gVectorFanSupport R) :
    ∃ (c : GrothendieckGroup (FGModuleCat.{u} R)) (g : ProjectiveClass R),
      (stableClassesOfClass (projectiveClassWeight k g) c).Infinite := by
  let _ : IsArtinianRing R := isArtinian_of_tower k inferInstance
  apply exists_infinite_stableClassesOfClass_at_projectiveWeight_of_not_isEFinite k
  intro h
  exact hv ((mem_fanSupport_iff_exists_presilting k v).2 (h v))

end TwoTerm

variable {R : Type u} [Ring R] [IsNoetherianRing R] (k : Type u) [Field k] [Algebra k R]
  [Module.Finite k R]

private theorem dimension_of_class {M : FGModuleCat.{u} R} {c : GrothendieckGroup (FGModuleCat.{u} R)}
    (h : GrothendieckGroup.of M = c) :
    Module.finrank k (M.obj : Type u) = ((dimensionWeight (R := R) k) c).toNat := by
  subst c
  change _ = ((dimensionWeight (R := R) k).eval M).toNat
  rw [dimensionWeight_eval,Int.toNat_natCast]

/-- Over an infinite field the same infinite stable family can be chosen
with both fixed Grothendieck class and fixed positive endolength. -/
theorem exists_infinite_stable_fixed_class_and_endolength [Infinite k] (hn : ¬ IsEFinite R) :
    ∃ (g : ProjectiveClass R) (c : GrothendieckGroup (FGModuleCat.{u} R)) (r : ℕ), 0 < r ∧
      (stableClassesOfClass (projectiveClassWeight k g) c ∩
        stableClassesOfEndolength k (projectiveClassWeight k g) r).Infinite := by
  classical
  let _ : IsArtinianRing R := isArtinian_of_tower k inferInstance
  obtain ⟨c,g,hinf⟩ := exists_infinite_stableClassesOfClass_at_projectiveWeight_of_not_isEFinite k hn
  let θ := projectiveClassWeight k g
  let d := ((dimensionWeight (R := R) k) c).toNat
  let family (r : ℕ) := stableClassesOfClass θ c ∩ stableClassesOfEndolength k θ r
  have hsub : stableClassesOfClass θ c ⊆ ⋃ r : Fin (d+1), family r.val := by
    rintro x hx
    obtain ⟨M,hm,hc,hs⟩ := hx
    have hd : Module.finrank k (M.obj : Type u) = d := dimension_of_class k hc
    have hr := (endolength_le_groundFinrank k M).trans_eq hd
    exact Set.mem_iUnion.mpr ⟨⟨_,Nat.lt_succ_of_le hr⟩,⟨M,hm,hc,hs⟩,M,hm,rfl,hs⟩
  obtain ⟨r,hr⟩ : ∃ r : Fin (d+1), (family r.val).Infinite := by
    by_contra! hall
    exact hinf ((Set.finite_iUnion hall).subset hsub)
  obtain ⟨x,_,M,_,he,hs⟩ := hr.nonempty
  exact ⟨g,c,r.val,he ▸ hs.isBrick.endolength_pos k,hr⟩

/-- Over every field two distinct stable bricks at one integral weight have
both the same module class and the same ordinary submodule polytope. -/
theorem exists_equal_class_polytope_stable_pair (hn : ¬ IsEFinite R) :
    ∃ (g : ProjectiveClass R) (X Y : FGModuleCat.{u} R),
      (projectiveClassWeight k g).IsStable X ∧ (projectiveClassWeight k g).IsStable Y ∧
      ¬ Nonempty (X ≅ Y) ∧ GrothendieckGroup.of X = GrothendieckGroup.of Y ∧
      submodulePolytope X = submodulePolytope Y := by
  classical
  let _ : IsArtinianRing R := isArtinian_of_tower k inferInstance
  rcases finite_or_infinite k with hfin | hinf
  · obtain ⟨g,X,Y,hX,hY,hne,he⟩ := exists_equalPolytope_stable_pair k hn
    exact ⟨g,X,Y,hX,hY,hne,class_eq_of_submodulePolytope_eq k he,he⟩
  obtain ⟨c,g,h⟩ := exists_infinite_stableClassesOfClass_at_projectiveWeight_of_not_isEFinite k hn
  let F := stableClassesOfClass (projectiveClassWeight k g) c
  choose M hm hc hs using fun x : F ↦ x.property
  let d := ((dimensionWeight (R := R) k) c).toNat
  obtain ⟨S,_,hS⟩ := exists_bounded_class_cover (R := R) k d
  let T := 𝒫 (S : Set (GrothendieckGroup (FGModuleCat.{u} R)))
  have : Finite T := S.finite_toSet.powerset
  let f (x : F) : T := ⟨submoduleProfile (M x), by
    rintro _ ⟨U,i,hi,rfl⟩
    have : Module.Finite k ((M x).obj : Type u) := Module.Finite.trans R _
    apply hS
    have hle := LinearMap.finrank_le_finrank_of_injective (f := i.hom.hom.restrictScalars k)
      ((FGModuleCat.mono_iff_injective i).1 hi)
    exact hle.trans_eq (dimension_of_class k (hc x))⟩
  have hni : ¬ Function.Injective f := fun hinj ↦ h (Finite.of_injective f hinj)
  obtain ⟨x,y,he,hne⟩ := Function.not_injective_iff.mp hni
  refine ⟨g,M x,M y,hs x,hs y,?_,(hc x).trans (hc y).symm,?_⟩
  · rintro ⟨e⟩
    exact hne (Subtype.ext ((hm x).symm.trans ((congr_toSkeleton_of_iso e).trans (hm y))))
  · have he' : submoduleProfile (M x) = submoduleProfile (M y) := congrArg Subtype.val he
    rw [submodulePolytope,submodulePolytope,he']

end EFiniteCharacterizations
