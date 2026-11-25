module

public import EFiniteCharacterizations.Geometry.HomLoci
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Idempotents

/-! # Representations on fixed vertex spaces and vertexwise base change -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable {k R I : Type u} [Field k] [Ring R] [Algebra k R] [DecidableEq I]

/-- The prescribed space at each vertex, with its fixed coordinates. -/
abbrev VertexSpace (k : Type u) (d : I → ℕ) := (i : I) → Fin (d i) → k

variable (d : I → ℕ)

noncomputable def vertexProjection (i : I) : Module.End k (VertexSpace k d) :=
  (LinearMap.single k (fun i ↦ Fin (d i) → k) i).comp (LinearMap.proj i)

variable (e : I → R)

/-- Algebra actions on the fixed vertex spaces taking each vertex idempotent
to the corresponding coordinate projection. -/
def VertexRepresentation := {ρ : R →ₐ[k] Module.End k (VertexSpace k d) //
  ∀ i, ρ (e i) = vertexProjection d i}

namespace VertexRepresentation

variable {d e}

abbrev BaseChange (k : Type u) [Field k] (d : I → ℕ) :=
  ∀ i, (Fin (d i) → k) ≃ₗ[k] (Fin (d i) → k)

/-- Vertexwise changes of basis intertwining the two algebra actions. -/
def SameOrbit (ρ η : VertexRepresentation (k := k) d e) : Prop :=
  ∃ G : BaseChange k d, ∀ r z, LinearEquiv.piCongrRight G (ρ.val r z) =
    η.val r (LinearEquiv.piCongrRight G z)

/-- Conjugation of the algebra action by an invertible change of basis at each vertex. -/
noncomputable def changeBasis (G : BaseChange k d) (ρ : VertexRepresentation (k := k) d e) :
    VertexRepresentation (k := k) d e := by
  let F := LinearEquiv.piCongrRight G
  refine ⟨(F.conjAlgEquiv k).toAlgHom.comp ρ.val,fun i ↦ ?_⟩
  change F.conjAlgEquiv k (ρ.val (e i)) = _
  rw [ρ.property]
  apply LinearMap.ext
  intro z
  funext j
  change G j (Pi.single (M := fun t ↦ Fin (d t) → k) i (F.symm z i) j) =
    Pi.single (M := fun t ↦ Fin (d t) → k) i (z i) j
  by_cases hj : j = i
  · subst j
    simp [F,LinearEquiv.piCongrRight_symm]
  · simp [Pi.single_eq_of_ne hj]

noncomputable instance : MulAction (BaseChange k d) (VertexRepresentation (k := k) d e) where
  smul := changeBasis
  one_smul ρ := by
    apply Subtype.ext
    apply AlgHom.ext
    intro r
    rfl
  mul_smul G H ρ := by
    apply Subtype.ext
    apply AlgHom.ext
    intro r
    rfl

theorem mem_orbit_iff (ρ η : VertexRepresentation (k := k) d e) :
    η ∈ MulAction.orbit (BaseChange k d) ρ ↔ ρ.SameOrbit η := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨G,rfl⟩
    refine ⟨G,fun r z ↦ ?_⟩
    change _ = (LinearEquiv.piCongrRight G) (ρ.val r ((LinearEquiv.piCongrRight G).symm _))
    rw [LinearEquiv.symm_apply_apply]
  · rintro ⟨G,h⟩
    refine ⟨G,Subtype.ext (AlgHom.ext fun r ↦ LinearMap.ext fun z ↦ ?_)⟩
    obtain ⟨y,rfl⟩ := (LinearEquiv.piCongrRight G).surjective z
    change (LinearEquiv.piCongrRight G) (ρ.val r ((LinearEquiv.piCongrRight G).symm _)) = _
    rw [LinearEquiv.symm_apply_apply]
    exact h r y

/-- A change of basis intertwining the actions necessarily preserves the
vertex decomposition. Evaluating the intertwining equation on each vertex
idempotent recovers its diagonal blocks. -/
theorem sameOrbit_iff_intertwining_equiv (ρ η : VertexRepresentation (k := k) d e) :
    ρ.SameOrbit η ↔ ∃ F : VertexSpace k d ≃ₗ[k] VertexSpace k d,
      ∀ r z, F (ρ.val r z) = η.val r (F z) := by
  constructor
  · rintro ⟨G,h⟩
    exact ⟨LinearEquiv.piCongrRight G,h⟩
  · rintro ⟨F,h⟩
    have hblock i z : F (Pi.single i (z i)) = Pi.single i ((F z) i) := by
      simpa only [ρ.property,η.property,vertexProjection,LinearMap.comp_apply,LinearMap.single_apply,
        LinearMap.proj_apply] using h (e i) z
    have hinv i z : F.symm (Pi.single i (z i)) = Pi.single i ((F.symm z) i) := by
      apply F.injective
      simp [hblock]
    let block (f : VertexSpace k d →ₗ[k] VertexSpace k d) (i : I) :=
      (LinearMap.proj i).comp (f.comp (LinearMap.single k (fun j ↦ Fin (d j) → k) i))
    have entry (i : I) (z : VertexSpace k d) : block F.toLinearMap i (z i) = (F z) i := by
      simpa [block] using congrFun (hblock i z) i
    have entry' (i : I) (z : VertexSpace k d) : block F.symm.toLinearMap i (z i) = (F.symm z) i := by
      simpa [block] using congrFun (hinv i z) i
    let G (i : I) : (Fin (d i) → k) ≃ₗ[k] (Fin (d i) → k) :=
      LinearEquiv.ofLinearMap (block F.toLinearMap i) (block F.symm.toLinearMap i)
        (LinearMap.ext fun v ↦ by
          simpa [block] using entry i (F.symm (Pi.single i v)))
        (LinearMap.ext fun v ↦ by
          simpa [block] using entry' i (F (Pi.single i v)))
    have heq z : LinearEquiv.piCongrRight G z = F z := funext fun i ↦ entry i z
    exact ⟨G,fun r z ↦ by simp only [heq,h]⟩

variable [Fintype I]

/-- The finite module defined by evaluation of an algebra action. -/
noncomputable def moduleObj (ρ : VertexRepresentation (k := k) d e) : FGModuleCat.{u} R := by
  let _ : Module R (VertexSpace k d) := Module.compHom _ ρ.val.toRingHom
  have : IsScalarTower k R (VertexSpace k d) := IsScalarTower.of_algebraMap_smul fun c z ↦
    congrArg (fun f : Module.End k (VertexSpace k d) ↦ f z) (ρ.val.commutes c)
  have : Module.Finite R (VertexSpace k d) := Module.Finite.of_restrictScalars_finite k _ _
  exact FGModuleCat.of R (VertexSpace k d)

/-- Coordinates of the underlying module in the prescribed vertex spaces. -/
noncomputable def coordinates (ρ : VertexRepresentation (k := k) d e) :
    (ρ.moduleObj.obj : Type u) ≃ₗ[k] VertexSpace k d where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c z := congrArg (fun f : Module.End k (VertexSpace k d) ↦ f z) (ρ.val.commutes c)

theorem coordinates_smul (ρ : VertexRepresentation (k := k) d e) (r : R) (z : ρ.moduleObj) :
    ρ.coordinates (r • z) = ρ.val r (ρ.coordinates z) := rfl

/-- The vertexwise base-change orbit is exactly the module isomorphism class. -/
theorem sameOrbit_iff_iso (ρ η : VertexRepresentation (k := k) d e) :
    ρ.SameOrbit η ↔ Nonempty (ρ.moduleObj ≅ η.moduleObj) := by
  rw [sameOrbit_iff_intertwining_equiv]
  constructor
  · rintro ⟨F,h⟩
    let g := (ρ.coordinates.trans F).trans η.coordinates.symm
    let l : ρ.moduleObj ≃ₗ[R] η.moduleObj :=
      { g.toAddEquiv with map_smul' := fun r z ↦ h r (ρ.coordinates z) }
    exact ⟨l.toFGModuleCatIso⟩
  · rintro ⟨f⟩
    let g := (FGModuleCat.isoToLinearEquiv f).restrictScalars k
    exact ⟨(ρ.coordinates.symm.trans g).trans η.coordinates,fun r z ↦
      (FGModuleCat.isoToLinearEquiv f).map_smul r (ρ.coordinates.symm z)⟩

/-- The total basis is the union of the standard bases at the vertices. -/
noncomputable def vertexBasis (ρ : VertexRepresentation (k := k) d e) :
    Module.Basis (Σ i, Fin (d i)) k (ρ.moduleObj.obj : Type u) :=
  (Pi.basisFun k _).map ((LinearEquiv.piCurry k (fun i (_ : Fin (d i)) ↦ k)).trans ρ.coordinates.symm)

variable {J : Type u} [Fintype J] (b : Module.Basis J k R)

/-- Affine coordinates are the matrix coefficients of the basis elements of the algebra. -/
noncomputable def affineCoordinates (ρ : VertexRepresentation (k := k) d e) :
    J × (Σ i, Fin (d i)) × (Σ i, Fin (d i)) → k := fun (j,a,l) ↦
  actionMatrices b ρ.vertexBasis j a l

/-- The action matrices in fixed vertex coordinates distinguish all points. -/
theorem affineCoordinates_injective : Function.Injective (affineCoordinates (d := d) (e := e) b) := by
  classical
  intro ρ η he
  apply Subtype.ext
  apply AlgHom.toLinearMap_injective
  apply b.ext
  intro j
  let w := (Pi.basisFun k (Σ i, Fin (d i))).map (LinearEquiv.piCurry k (fun i (_ : Fin (d i)) ↦ k))
  apply (LinearMap.toMatrix w w).injective
  ext a l
  have hz := congrFun he (j,a,l)
  simpa only [affineCoordinates,actionMatrices,LinearMap.toMatrix_apply,vertexBasis,
    Module.Basis.map_apply,Module.Basis.map_repr,LinearEquiv.trans_apply,LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm,Algebra.lsmul_apply,coordinates_smul,LinearEquiv.apply_symm_apply,AlgHom.toLinearMap_apply,w]
    using hz

/-- The point-set Zariski topology of the fixed-vertex representation variety. -/
@[instance_reducible] noncomputable def zariski :
    TopologicalSpace (VertexRepresentation (k := k) d e) := coordinateZariski (affineCoordinates b)

/-- The vertex summand of a module is the image of the vertex idempotent. -/
abbrev vertexPart (e : I → R) (M : FGModuleCat.{u} R) (i : I) :=
  LinearMap.range (Algebra.lsmul k k (M.obj : Type u) (e i))

private theorem smul_vertexPart (he : CompleteOrthogonalIdempotents e) (M : FGModuleCat.{u} R)
    (i j : I) (x : vertexPart (k := k) e M j) :
    e i • (x.val : M) = if i = j then (x.val : M) else 0 := by
  obtain ⟨z,hz⟩ := x.property
  change e j • z = (x.val : M) at hz
  rw [← hz,smul_smul,he.mul_eq]
  split <;> simp_all

/-- Decomposition of a module into its vertex summands. -/
noncomputable def decompose (he : CompleteOrthogonalIdempotents e) (M : FGModuleCat.{u} R) :
    (M.obj : Type u) ≃ₗ[k] ∀ i, vertexPart (k := k) e M i where
  toFun z i := ⟨e i • z,z,rfl⟩
  invFun z := ∑ i, (z i).val
  left_inv z := by simp only [← Finset.sum_smul,he.complete,one_smul]
  right_inv z := by
    funext i
    apply Subtype.ext
    change e i • ∑ j, (z j).val = _
    simp [Finset.smul_sum,smul_vertexPart he M]
  map_add' _ _ := funext fun _ ↦ Subtype.ext (smul_add ..)
  map_smul' _ _ := funext fun _ ↦ Subtype.ext (smul_comm ..)

variable [Module.Finite k R]

/-- Every module with the prescribed vertex dimensions occurs in the variety. -/
theorem exists_iso_of_vertex_dimensions (he : CompleteOrthogonalIdempotents e) (M : FGModuleCat.{u} R)
    (hd : ∀ i, Module.finrank k (vertexPart (k := k) e M i) = d i) :
    ∃ ρ : VertexRepresentation (k := k) d e, Nonempty (M ≅ ρ.moduleObj) := by
  classical
  let _ : Module.Finite R (M.obj : Type u) := M.property
  let _ : Module.Finite k (M.obj : Type u) := Module.Finite.trans R _
  let w i := ((Module.finBasis k (vertexPart (k := k) e M i)).reindex (finCongr (hd i))).equivFun
  let F := (decompose (k := k) he M).trans (LinearEquiv.piCongrRight w)
  let a : R →ₐ[k] Module.End k (VertexSpace k d) :=
    (F.conjAlgEquiv k).toAlgHom.comp (Algebra.lsmul k k (M.obj : Type u))
  have hF r z : a r (F z) = F (r • z) := by simp [a]
  have ha i : a (e i) = vertexProjection d i := by
    apply LinearMap.ext
    intro z
    funext j l
    obtain ⟨v,rfl⟩ := F.surjective z
    rw [hF]
    change w j ⟨e j • e i • v,_⟩ l = Pi.single (M := fun t ↦ Fin (d t) → k) i ((F v) i) j l
    by_cases hj : j = i
    · subst j
      simp only [Pi.single_eq_same]
      apply congrArg (fun t : vertexPart (k := k) e M i ↦ w i t l)
      apply Subtype.ext
      exact (smul_smul _ _ _).trans (congrArg (· • v) (he.idem i))
    · rw [Pi.single_eq_of_ne hj]
      have hz : (⟨e j • e i • v, e i • v,rfl⟩ : vertexPart (k := k) e M j) = 0 := by
        apply Subtype.ext
        simp [smul_smul,he.ortho hj]
      rw [hz,map_zero]
  let ρ : VertexRepresentation (k := k) d e := ⟨a,ha⟩
  let l : M ≃ₗ[R] ρ.moduleObj :=
    { (F.trans ρ.coordinates.symm).toAddEquiv with map_smul' := fun r z ↦ (hF r z).symm }
  exact ⟨ρ,⟨l.toFGModuleCatIso⟩⟩

end VertexRepresentation
end EFiniteCharacterizations
