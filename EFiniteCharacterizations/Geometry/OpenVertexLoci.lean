module

public import EFiniteCharacterizations.Geometry.VertexDimensions

/-! # Open brick orbits and open wide loci in a split basic presentation -/

@[expose] public section

open CategoryTheory

universe u

namespace EFiniteCharacterizations.VertexRepresentation.SplitBasicVertices

variable {k R I J : Type u} [Field k] [Ring R] [Algebra k R]
    [Module.Finite k R] [IsNoetherianRing R] [IsArtinianRing R]
    [Fintype I] [DecidableEq I] [Fintype J]
    (P : SplitBasicVertices k R I) (b : Module.Basis J k R)

noncomputable def universalMatrix (d : I → ℕ) (j : J) :
    Matrix (Σ i, Fin (d i)) (Σ i, Fin (d i))
      (MvPolynomial (J × (Σ i, Fin (d i)) × (Σ i, Fin (d i))) k) :=
  fun a l ↦ MvPolynomial.X (j,a,l)

omit [Module.Finite k R] [IsNoetherianRing R] [IsArtinianRing R] [Fintype J] in
theorem eval_matrix (d : I → ℕ) (ρ : VertexRepresentation (k := k) d P.vertex) (j : J) :
    (universalMatrix (k := k) d j).map (MvPolynomial.eval (affineCoordinates b ρ)) =
      actionMatrices b ρ.vertexBasis j := by
  ext
  simp [universalMatrix,Matrix.map_apply,affineCoordinates]

/-- Openness of all wide loci in the fixed-vertex representation varieties
of a split basic algebra characterizes E-finiteness over an infinite field. -/
theorem isEFinite_iff_open_wide [Infinite k] :
    IsEFinite R ↔ ∀ d (W : ObjectProperty (FGModuleCat.{u} R)), IsWideClass W →
      @IsOpen (VertexRepresentation (k := k) d P.vertex) (zariski b) {ρ | W ρ.moduleObj} := by
  constructor
  · intro he d W hw
    exact isOpen_wide_of_isEFinite (affineCoordinates b) moduleObj vertexBasis b _ (P.eval_matrix b d)
      he (fun x y ↦ (P.class_of_point x).trans (P.class_of_point y).symm) hw
  · intro ho
    apply (isEFinite_iff_dim_stab k).2
    intro g q
    let d := q ∘ P.simpleIndex.symm
    exact finite_stables_of_open_wide_loci (affineCoordinates b) (moduleObj (d := d) (e := P.vertex)) _ _
      (fun x ↦ by simpa [d,Function.comp_def] using P.class_of_point x)
      (fun B _ h ↦ P.exists_point_of_class B q h) (ho d)

/-- Openness of all brick orbits under the product of the vertex general
linear groups characterizes E-finiteness over an infinite field. -/
theorem isEFinite_iff_open_brick [Infinite k] :
    IsEFinite R ↔ ∀ d (ρ : VertexRepresentation (k := k) d P.vertex), IsBrick ρ.moduleObj →
      @IsOpen _ (zariski b) {η | η.SameOrbit ρ} := by
  constructor
  · intro he d ρ hb
    simpa only [sameOrbit_iff_iso] using isOpen_brick_iso_of_isEFinite
      (affineCoordinates b) moduleObj vertexBasis b _ (P.eval_matrix b d) he ρ.moduleObj hb
      (fun x ↦ (P.class_of_point x).trans (P.class_of_point ρ).symm)
  · intro ho
    apply (isEFinite_iff_dim_brick k).2
    intro q
    let d := q ∘ P.simpleIndex.symm
    apply finite_bricks_of_open_iso_loci (affineCoordinates b) (moduleObj (d := d) (e := P.vertex)) _
      (fun B _ h ↦ P.exists_point_of_class B q h)
    intro B hb h
    obtain ⟨ρ,⟨f⟩⟩ := P.exists_point_of_class B q h
    have hρ : IsBrick ρ.moduleObj := by
      refine ⟨fun hz ↦ hb.1 (hz.of_iso f.symm),fun a ha ↦ ?_⟩
      have hne : f.inv ≫ a ≫ f.hom ≠ 0 := by
        intro hz
        apply ha
        simpa using congrArg (fun t ↦ f.hom ≫ t ≫ f.inv) hz
      have := hb.2 _ hne
      have hh : IsIso (f.hom ≫ (f.inv ≫ a ≫ f.hom) ≫ f.inv) := by infer_instance
      simpa using hh
    convert ho d ρ hρ using 1
    ext x
    change Nonempty (x.moduleObj ≅ B) ↔ x.SameOrbit ρ
    rw [sameOrbit_iff_iso]
    exact ⟨fun ⟨a⟩ ↦ ⟨a ≪≫ f.symm⟩,fun ⟨a⟩ ↦ ⟨a ≪≫ f⟩⟩

end EFiniteCharacterizations.VertexRepresentation.SplitBasicVertices

namespace EFiniteCharacterizations

private theorem equalClassHom_of_equivalence {C D : Type*} [Category C] [Abelian C]
    [Category D] [Abelian D] (E : C ≌ D) (h : EqualClassHom D) : EqualClassHom C := by
  let F := E.functor
  let G := E.inverse
  let φ := GrothendieckGroup.map F (fun _ hs ↦ hs.map_of_exact F)
  let ψ := GrothendieckGroup.map G (fun _ hs ↦ hs.map_of_exact G)
  have hf X : φ (GrothendieckGroup.of X) = GrothendieckGroup.of (F.obj X) := GrothendieckGroup.lift_of ..
  have hg X : ψ (GrothendieckGroup.of X) = GrothendieckGroup.of (G.obj X) := GrothendieckGroup.lift_of ..
  intro X Y he hn
  have hn' : GrothendieckGroup.of (F.obj X) ≠ 0 := by
    intro hz
    apply hn
    refine (GrothendieckGroup.of_eq_of_iso (E.unitIso.app X)).trans ?_
    change GrothendieckGroup.of (G.obj (F.obj X)) = 0
    rw [← hg (F.obj X),hz,map_zero]
  obtain ⟨f,hf'⟩ := h _ _ ((hf X).symm.trans ((congrArg φ he).trans (hf Y))) hn'
  exact ⟨F.preimage f,fun hz ↦ hf' (by rw [← F.map_preimage f,hz,F.map_zero])⟩

/-- E-finiteness is invariant under equivalence of the finite module
categories. The two algebra structures may be over different fields. -/
theorem isEFinite_iff_of_module_equivalence
    (k l : Type u) [Field k] [Field l] {R S : Type u} [Ring R] [Ring S] [Algebra k R] [Algebra l S]
    [Module.Finite k R] [Module.Finite l S] [IsNoetherianRing R] [IsArtinianRing R]
    [IsNoetherianRing S] [IsArtinianRing S] (E : FGModuleCat.{u} R ≌ FGModuleCat.{u} S) :
    IsEFinite R ↔ IsEFinite S := by
  rw [isEFinite_iff_equalClassHom k,isEFinite_iff_equalClassHom l]
  exact ⟨equalClassHom_of_equivalence E.symm,equalClassHom_of_equivalence E⟩

open VertexRepresentation in
/-- The two openness equivalences of Theorem A, for right modules and any
chosen Morita equivalent split basic presentation. -/
theorem isEFinite_iff_open_vertex_loci
    {k R S I J : Type u} [Field k] [Infinite k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
    [Module.Finite k R] [Module.Finite k S] [Fintype I] [DecidableEq I] [Fintype J]
    (E : FGModuleCat.{u} Rᵐᵒᵖ ≌ FGModuleCat.{u} S)
    (P : SplitBasicVertices k S I) (b : Module.Basis J k S) :
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    letI := IsNoetherianRing.of_finite k S
    (IsEFinite Rᵐᵒᵖ ↔ ∀ d (ρ : VertexRepresentation (k := k) d P.vertex), IsBrick ρ.moduleObj →
      @IsOpen _ (zariski b) (MulAction.orbit (BaseChange k d) ρ)) ∧
    (IsEFinite Rᵐᵒᵖ ↔ ∀ d (W : ObjectProperty (FGModuleCat.{u} S)), IsWideClass W →
      @IsOpen (VertexRepresentation (k := k) d P.vertex) (zariski b) {ρ | W ρ.moduleObj}) := by
  let _ := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let _ := IsNoetherianRing.of_finite k S
  let _ := IsArtinianRing.of_finite k Rᵐᵒᵖ
  let _ := IsArtinianRing.of_finite k S
  have h := isEFinite_iff_of_module_equivalence k k E
  refine ⟨?_,h.trans (P.isEFinite_iff_open_wide b)⟩
  have horbit d (ρ : VertexRepresentation (k := k) d P.vertex) :
      MulAction.orbit (BaseChange k d) ρ = {η | η.SameOrbit ρ} := by
    ext η
    change η ∈ MulAction.orbit (BaseChange k d) ρ ↔ η.SameOrbit ρ
    rw [VertexRepresentation.mem_orbit_iff,sameOrbit_iff_iso,sameOrbit_iff_iso]
    exact ⟨fun ⟨f⟩ ↦ ⟨f.symm⟩,fun ⟨f⟩ ↦ ⟨f.symm⟩⟩
  simpa only [horbit] using h.trans (P.isEFinite_iff_open_brick b)

end EFiniteCharacterizations
