module

public import EFiniteCharacterizations.Algebra.FullCornerMorita
public import EFiniteCharacterizations.Geometry.SplitBasicSimples
public import EFiniteCharacterizations.Geometry.TorsionLoci
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Split basic Morita presentations and open-locus characterizations

Constructs `basicPresentation k R` over an algebraically closed field (equipping any
finite-dimensional `k`-algebra with a Morita-equivalent split basic corner and vertex
idempotents) and proves `equivalences_openLoci` (Theorem 6.1 / Theorem A(III),
establishing `(E-fin) ⇔ (open-brick)` and `(E-fin) ⇔ (open-wide)`).
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

section Corner

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] {e : R} (he : IsIdempotentElem e)
local instance : Algebra k he.Corner := IsIdempotentElem.cornerAlgebra he

theorem finite_corner [Module.Finite k R] : Module.Finite k he.Corner := by
  let f : he.Corner →ₗ[k] R :=
    { toFun := fun x ↦ x.1
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c x ↦ by
        change (algebraMap k R c * e) * x.1 = c • x.1
        rw [mul_assoc,((Subsemigroup.mem_corner_iff he).1 x.2).1,Algebra.smul_def] }
  exact Module.Finite.of_injective f (fun _ _ h ↦ Subtype.ext h)

/-- The equivalence of finite modules attached to a full idempotent. -/
noncomputable def fullCornerFiniteEquivalence [Module.Finite k R] (hfull : IsFull e) :
    FGModuleCat.{u} R ≌ FGModuleCat.{u} he.Corner := by
  let C := hfull.exists_fullnessCertificate.some
  let E := IsIdempotentElem.fullIdempotentModuleCatEquivalence (k := k) he C
  let _ := finite_corner (k := k) he
  let _ : (ModuleCat.isFG.{u} he.Corner).IsClosedUnderIsomorphisms := by
    constructor
    intro X Y f hX
    let _ : Module.Finite he.Corner X := hX
    exact Module.Finite.equiv f.toLinearEquiv
  apply E.congrFullSubcategory
  funext X
  apply propext
  let Y := IsIdempotentElem.cornerPartObj (k := k) he X
  change Module.Finite he.Corner Y ↔ Module.Finite R X
  have h := IsIdempotentElem.moduleFinite_cornerPartObj_iff (k := k) he C X
  constructor
  · intro hY
    have : Module.Finite k X := h.2 (Module.Finite.trans he.Corner Y)
    exact Module.Finite.of_restrictScalars_finite k R X
  · intro hX
    have : Module.Finite k Y := h.1 (Module.Finite.trans R X)
    exact Module.Finite.of_restrictScalars_finite k he.Corner Y

end Corner

/-- A finite-dimensional algebra presenting the right module category, with
split basic vertices and affine matrix coordinates. -/
structure BasicPresentation (k R : Type u) [Field k] [Ring R] where
  Carrier : Type u
  [ring : Ring Carrier]
  [algebra : Algebra k Carrier]
  [finite : Module.Finite k Carrier]
  n : ℕ
  vertices : VertexRepresentation.SplitBasicVertices k Carrier (ULift.{u} (Fin n))
  equivalence : FGModuleCat.{u} Rᵐᵒᵖ ≌ FGModuleCat.{u} Carrier

attribute [instance] BasicPresentation.ring BasicPresentation.algebra BasicPresentation.finite

/-- Lift the vertex labels into the universe of the algebra and its modules. -/
noncomputable def SplitBasicIdempotents.liftIndex {k A : Type u} [Field k] [Ring A] [Algebra k A]
    {n : ℕ} (P : SplitBasicIdempotents (k := k) (A := A) (ι := Fin n)) :
    SplitBasicIdempotents (k := k) (A := A) (ι := ULift.{u} (Fin n)) where
  idempotent i := P.idempotent i.down
  complete := (CompleteOrthogonalIdempotents.equiv Equiv.ulift).2 P.complete
  quotientEquiv := P.quotientEquiv.trans (AlgEquiv.piCongrLeft' k (fun _ ↦ k) Equiv.ulift.symm)
  quotientEquiv_mk_idempotent i j := by
    change P.quotientEquiv _ j.down = _
    rw [P.quotientEquiv_mk_idempotent]
    simp

/-- Every finite-dimensional algebra over an algebraically closed field
has a split basic presentation of its finite right modules. -/
noncomputable def basicPresentation (k R : Type u) [Field k] [IsAlgClosed k]
    [Ring R] [Algebra k R] [Module.Finite k R] : BasicPresentation k R := by
  let D := (exists_basicIdempotentData k Rᵐᵒᵖ).some
  let _ : Module.Finite k D.Corner := finite_corner (k := k) D.sumIdempotent_isIdempotentElem
  let _ := IsNoetherianRing.of_finite k D.Corner
  exact { Carrier := D.Corner
          n := D.n
          vertices := (D.splitBasicIdempotents k Rᵐᵒᵖ).liftIndex.toSplitBasicVertices
          equivalence := fullCornerFiniteEquivalence (k := k) D.sumIdempotent_isIdempotentElem D.full }

namespace BasicPresentation

open VertexRepresentation
variable {k R : Type u} [Field k] [Ring R] (P : BasicPresentation k R)

noncomputable def algebraBasis : Module.Basis (ULift.{u} (Fin (Module.finrank k P.Carrier))) k P.Carrier :=
  (Module.finBasis k P.Carrier).reindex Equiv.ulift.symm

/-- Every brick orbit under vertexwise changes of basis is Zariski open. -/
def OpenBrickOrbits : Prop :=
  ∀ d (ρ : VertexRepresentation (k := k) d P.vertices.vertex), IsBrick ρ.moduleObj →
    @IsOpen _ (zariski P.algebraBasis) (MulAction.orbit (BaseChange k d) ρ)

/-- Every wide locus is open in each representation variety. -/
def OpenWideLoci : Prop :=
  letI := IsNoetherianRing.of_finite k P.Carrier
  ∀ d (W : ObjectProperty (FGModuleCat.{u} P.Carrier)), IsWideClass W →
    @IsOpen (VertexRepresentation (k := k) d P.vertices.vertex) (zariski P.algebraBasis) {ρ | W ρ.moduleObj}

end BasicPresentation

/-- The open-brick, open-wide, open-torsion and open-torsion-free tests for
right modules over every finite-dimensional algebra over an algebraically
closed field, in a basic presentation constructed from the algebra. -/
theorem equivalences_openLoci (k R : Type u) [Field k] [IsAlgClosed k] [Ring R] [Algebra k R]
    [Module.Finite k R] :
    let P := basicPresentation k R
    letI := IsNoetherianRing.of_finite k Rᵐᵒᵖ
    letI := IsNoetherianRing.of_finite k P.Carrier
    (IsEFinite Rᵐᵒᵖ ↔ P.OpenBrickOrbits) ∧ (IsEFinite Rᵐᵒᵖ ↔ P.OpenWideLoci) ∧
      (IsEFinite Rᵐᵒᵖ ↔ P.vertices.OpenTorsionLoci P.algebraBasis) ∧
      (IsEFinite Rᵐᵒᵖ ↔ P.vertices.OpenTorsionFreeLoci P.algebraBasis) := by
  let P := basicPresentation k R
  obtain ⟨hb,hw⟩ := isEFinite_iff_open_vertex_loci P.equivalence P.vertices P.algebraBasis
  exact ⟨hb,hw,isEFinite_iff_open_torsion_loci P.equivalence P.vertices P.algebraBasis⟩

end EFiniteCharacterizations
