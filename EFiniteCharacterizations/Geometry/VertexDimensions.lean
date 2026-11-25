module

public import EFiniteCharacterizations.Geometry.VertexRepresentations

/-! # Vertex dimensions and composition vectors -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations.VertexRepresentation

variable {k R I : Type u} [Field k] [Ring R] [Algebra k R] {e : I → R}

noncomputable def partMap {M N : FGModuleCat.{u} R} (f : M ⟶ N) (i : I) :
    vertexPart (k := k) e M i →ₗ[k] vertexPart (k := k) e N i :=
  ((f.hom.hom.restrictScalars k).comp (vertexPart (k := k) e M i).subtype).codRestrict _ fun z ↦ by
    obtain ⟨y,hy⟩ := z.property
    exact ⟨f.hom.hom y,(f.hom.hom.map_smul (e i) y).symm.trans (congrArg f.hom.hom hy)⟩

noncomputable def partEquiv {M N : FGModuleCat.{u} R} (f : M ≅ N) (i : I) :
    vertexPart (k := k) e M i ≃ₗ[k] vertexPart (k := k) e N i :=
  LinearEquiv.ofLinearMap (partMap f.hom i) (partMap f.inv i)
    (LinearMap.ext fun x ↦ Subtype.ext <| (FGModuleCat.isoToLinearEquiv f).apply_symm_apply x.val)
    (LinearMap.ext fun x ↦ Subtype.ext <| (FGModuleCat.isoToLinearEquiv f).symm_apply_apply x.val)

variable [Module.Finite k R] [IsNoetherianRing R]

/-- Restricting a short exact sequence to an idempotent summand preserves
injectivity, surjectivity and exactness. -/
theorem partMap_shortExact (e : I → R) (i : I) (hi : IsIdempotentElem (e i))
    (S : ShortComplex (FGModuleCat.{u} R)) (hs : S.ShortExact) :
    Function.Injective (partMap (k := k) (e := e) S.f i) ∧
    Function.Surjective (partMap (k := k) (e := e) S.g i) ∧
    LinearMap.ker (partMap (k := k) (e := e) S.g i) = LinearMap.range (partMap (k := k) (e := e) S.f i) := by
  let F := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  have H := hs.map_of_exact F
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp H.exact
  let a := partMap (k := k) (e := e) S.f i
  let b := partMap (k := k) (e := e) S.g i
  have ha : Function.Injective a := fun x y h ↦ Subtype.ext (H.moduleCat_injective_f (congrArg Subtype.val h))
  have hb : Function.Surjective b := by
    rintro ⟨_,z,rfl⟩
    obtain ⟨y,hy⟩ := H.moduleCat_surjective_g z
    exact ⟨⟨e i • y,y,rfl⟩,Subtype.ext ((S.g.hom.hom.map_smul _ _).trans (congrArg (e i • ·) hy))⟩
  have heq : LinearMap.ker b = LinearMap.range a := by
    ext y
    constructor
    · intro hy
      obtain ⟨z,hz⟩ := (hex y.val).1 (congrArg Subtype.val (show b y = 0 from hy))
      obtain ⟨w,hw⟩ := y.property
      refine ⟨⟨e i • z,z,rfl⟩,Subtype.ext ?_⟩
      change S.f.hom.hom (e i • z) = y.val
      rw [S.f.hom.hom.map_smul,show S.f.hom.hom z = y.val from hz]
      change e i • w = y.val at hw
      rw [← hw,smul_smul,hi]
    · rintro ⟨z,rfl⟩
      exact Subtype.ext ((hex _).2 ⟨z.val,rfl⟩)
  exact ⟨ha,hb,heq⟩

/-- Dimension of the image of a vertex idempotent as an additive weight. -/
noncomputable def vertexWeight (e : I → R) (i : I) (hi : IsIdempotentElem (e i)) :
    Weight (FGModuleCat.{u} R) := GrothendieckGroup.lift
  (fun X ↦ (Module.finrank k (vertexPart (k := k) e X i) : ℤ)) fun S hs ↦ by
    let a := partMap (k := k) (e := e) S.f i
    let b := partMap (k := k) (e := e) S.g i
    obtain ⟨ha,hb,heq⟩ := partMap_shortExact (k := k) e i hi S hs
    let _ : Module.Finite R (S.X₂.obj : Type u) := S.X₂.property
    let _ : Module.Finite k (S.X₂.obj : Type u) := Module.Finite.trans R _
    have h := b.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hb,finrank_top,heq,LinearMap.finrank_range_of_inj ha,add_comm] at h
    exact_mod_cast h.symm

variable [Fintype I] [DecidableEq I] {d : I → ℕ}

omit [Module.Finite k R] [IsNoetherianRing R] in
/-- The idempotent summand of a based representation in its vertex coordinates. -/
noncomputable def vertexCoordinateEquiv (ρ : VertexRepresentation (k := k) d e) (i : I) :
    vertexPart (k := k) e ρ.moduleObj i ≃ₗ[k] (Fin (d i) → k) := by
  let p := ((LinearMap.proj i).comp ρ.coordinates.toLinearMap).comp
    (vertexPart (k := k) e ρ.moduleObj i).subtype
  have eval_e (z : ρ.moduleObj) : ρ.coordinates (e i • z) =
      Pi.single i ((ρ.coordinates z) i) := by rw [coordinates_smul,ρ.property]; rfl
  have ha : Function.Injective p := by
    rintro ⟨_,z,rfl⟩ ⟨_,w,rfl⟩ h
    apply Subtype.ext
    apply ρ.coordinates.injective
    change ρ.coordinates (e i • z) = ρ.coordinates (e i • w)
    change ρ.coordinates (e i • z) i = ρ.coordinates (e i • w) i at h
    simp only [eval_e,Pi.single_eq_same] at h ⊢
    rw [h]
  have hb : Function.Surjective p := by
    intro v
    let z := ρ.coordinates.symm (Pi.single i v)
    exact ⟨⟨e i • z,z,rfl⟩,by change ρ.coordinates (e i • z) i = v; simp [eval_e,z]⟩
  exact LinearEquiv.ofBijective p ⟨ha,hb⟩

omit [Module.Finite k R] [IsNoetherianRing R] in
theorem vertex_finrank (ρ : VertexRepresentation (k := k) d e) (i : I) :
    Module.finrank k (vertexPart (k := k) e ρ.moduleObj i) = d i := by
  simpa using (vertexCoordinateEquiv ρ i).finrank_eq

/-- Data of a split basic presentation. The simple at vertex i has dimension
one there and zero at the other vertices. -/
structure SplitBasicVertices (k : Type u) [Field k] (R : Type u) [Ring R] [Algebra k R]
    (I : Type u) [Fintype I] [DecidableEq I] where
  vertex : I → R
  complete : CompleteOrthogonalIdempotents vertex
  simpleIndex : simpleIsomorphismClasses R ≃ I
  simple_dimension : ∀ s i, Module.finrank k
    (vertexPart (k := k) vertex ((fromSkeleton _).obj s.val) i) = if simpleIndex s = i then 1 else 0

namespace SplitBasicVertices

variable (P : SplitBasicVertices k R I)

theorem vertex_weight_classOfCompositionVector (q : simpleIsomorphismClasses R → ℕ) (i : I) :
    vertexWeight (k := k) P.vertex i (P.complete.idem i) (classOfCompositionVector k q) =
      (q (P.simpleIndex.symm i) : ℤ) := by
  classical
  let _ := (finite_simpleIsomorphismClasses (R := R) k).fintype
  unfold classOfCompositionVector
  rw [map_sum]
  simp only [map_nsmul,vertexWeight,GrothendieckGroup.lift_of,P.simple_dimension]
  simp [← Equiv.eq_symm_apply]

variable [IsArtinianRing R]

theorem class_eq_of_vertex_finrank (M : FGModuleCat.{u} R) :
    classOfCompositionVector k (fun s ↦ Module.finrank k (vertexPart (k := k) P.vertex M (P.simpleIndex s))) =
      GrothendieckGroup.of M := by
  obtain ⟨q,hq⟩ := exists_compositionVector_of_module k M
  rw [← hq]
  congr 1
  funext s
  have eq := P.vertex_weight_classOfCompositionVector q (P.simpleIndex s)
  rw [hq,vertexWeight,GrothendieckGroup.lift_of,P.simpleIndex.symm_apply_apply] at eq
  exact_mod_cast eq

theorem class_of_point (ρ : VertexRepresentation (k := k) d P.vertex) :
    GrothendieckGroup.of ρ.moduleObj = classOfCompositionVector k (d ∘ P.simpleIndex) := by
  simpa [vertex_finrank,Function.comp_def] using (P.class_eq_of_vertex_finrank ρ.moduleObj).symm

omit [IsArtinianRing R] in
/-- All modules of the specified composition vector are represented on the
fixed vertex spaces. -/
theorem exists_point_of_class (M : FGModuleCat.{u} R) (q : simpleIsomorphismClasses R → ℕ)
    (hq : GrothendieckGroup.of M = classOfCompositionVector k q) :
    ∃ ρ : VertexRepresentation (k := k) (q ∘ P.simpleIndex.symm) P.vertex, Nonempty (ρ.moduleObj ≅ M) := by
  have hd i := P.vertex_weight_classOfCompositionVector q i
  obtain ⟨ρ,⟨f⟩⟩ := exists_iso_of_vertex_dimensions (k := k) P.complete M (d := q ∘ P.simpleIndex.symm)
    (fun i ↦ by
      have h := hd i
      rw [← hq,vertexWeight,GrothendieckGroup.lift_of] at h
      exact_mod_cast h)
  exact ⟨ρ,⟨f.symm⟩⟩

end SplitBasicVertices

end EFiniteCharacterizations.VertexRepresentation
