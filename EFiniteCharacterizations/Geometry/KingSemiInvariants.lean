module

public import EFiniteCharacterizations.Geometry.VertexDimensions
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

/-!
# Graded semi-invariant rings and King moduli schemes

Constructs the coordinate ring `coordinateAlgebra`, the graded `GL(d)`-semi-invariant
pieces `kingSemiInvariants`, the direct-sum ring `KingSemiInvariantRing`, and King's
projective moduli scheme `kingProj = Proj(KingSemiInvariantRing)` (`kingModuli` for
an integral projective class `g`) on the vertex representation variety `rep(A, d)`.
-/

@[expose] public section

open scoped DirectSum
universe u
namespace EFiniteCharacterizations.VertexRepresentation

variable {k R I J : Type u} [Field k] [Ring R] [Algebra k R]
    [Fintype I] [DecidableEq I] [Fintype J]
    (b : Module.Basis J k R) (d : I → ℕ) (e : I → R)

/-- The character specified by integral exponents on the vertex determinants. -/
noncomputable def vertexCharacter (w : I → ℤ) : BaseChange k d →* kˣ where
  toFun G := ∏ i, (LinearEquiv.det (G i)) ^ w i
  map_one' := by simp
  map_mul' G H := by simp [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

/-- Polynomial functions in the action matrices, restricted to the variety. -/
noncomputable def coordinateAlgebra : Subalgebra k (VertexRepresentation (k := k) d e → k) :=
  (MvPolynomial.aeval (fun j ρ ↦ affineCoordinates b ρ j)).range

/-- The degree-m part consists of regular functions on which the inverse
pullback action has character χ to the power m. -/
def kingSemiInvariants (w : I → ℤ) (m : ℕ) : Submodule k (coordinateAlgebra b d e) where
  carrier := {f | ∀ (G : BaseChange k d) x, f.val (G⁻¹ • x) =
    ((vertexCharacter d w G : kˣ) : k) ^ m * f.val x}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg G x
    change f.val _ + g.val _ = _ * (f.val x + g.val x)
    rw [hf,hg,mul_add]
  smul_mem' := by
    intro a f hf G x
    change a * f.val _ = _ * (a * f.val x)
    rw [hf]
    ring

instance (w : I → ℤ) : SetLike.GradedMonoid (kingSemiInvariants b d e w) where
  one_mem := by intro G x; simp
  mul_mem := by
    intro i j f g hf hg G x
    change f.val _ * g.val _ = _ ^ (i + j) * (f.val x * g.val x)
    rw [hf,hg,pow_add]
    ring

/-- The graded ring whose Proj defines the character quotient. -/
abbrev KingSemiInvariantRing (w : I → ℤ) := ⨁ m : ℕ, ↥(kingSemiInvariants b d e w m)

variable (w : I → ℤ)

abbrev KingPiece (m : ℕ) := ↥(kingSemiInvariants b d e w m)

local notation "A" => KingPiece b d e w

noncomputable instance : CommRing (KingSemiInvariantRing b d e w) :=
  @DirectSum.commRing ℕ _ _ _ _ (SetLike.gcommRing (kingSemiInvariants b d e w))

/-- The homogeneous pieces inside the direct sum ring. -/
noncomputable def kingGrading (m : ℕ) : AddSubgroup (KingSemiInvariantRing b d e w) :=
  AddMonoidHom.range (G := A m) (DirectSum.of A m)

instance : SetLike.GradedMonoid (kingGrading b d e w) where
  one_mem := ⟨_,(DirectSum.one_def _).symm⟩
  mul_mem := by
    rintro i j _ _ ⟨f,rfl⟩ ⟨g,rfl⟩
    exact ⟨_,(DirectSum.of_mul_of f g).symm⟩

noncomputable instance : GradedRing (kingGrading b d e w) := by
  let ins (m : ℕ) := AddMonoidHom.rangeRestrict (G := A m) (DirectSum.of A m)
  let deg := kingGrading b d e w
  let split := DirectSum.toAddMonoid (fun m ↦ (DirectSum.of (fun i ↦ ↥(deg i)) m).comp (ins m))
  refine { (inferInstance : SetLike.GradedMonoid deg) with
    toDecomposition := DirectSum.Decomposition.ofAddHom deg split ?_ ?_ }
  · apply DirectSum.addHom_ext
    intro i x
    change (DirectSum.coeAddMonoidHom deg) (split (DirectSum.of A i x)) = _
    rw [DirectSum.toAddMonoid_of]
    exact DirectSum.coeAddMonoidHom_of deg i (ins i x)
  · apply DirectSum.addHom_ext
    rintro i ⟨_,x,rfl⟩
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, split,
      DirectSum.toAddMonoid_of, AddMonoidHom.id_apply]
    rfl

/-- The projective GIT scheme for the chosen vertex determinant character. -/
noncomputable def kingProj : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Proj (kingGrading b d e w)

namespace SplitBasicVertices

variable [Module.Finite k R] [IsNoetherianRing R] (P : SplitBasicVertices k R I)

/-- Vertex exponents are the values of the integral weight on the simple
modules. The action on functions in the grading is inverse pullback. -/
noncomputable def characterExponents (g : ProjectiveClass R) (i : I) : ℤ :=
  (projectiveClassWeight k g).eval ((CategoryTheory.fromSkeleton _).obj (P.simpleIndex.symm i).val)

/-- The King scheme for a prescribed weight and vertex dimension vector. -/
noncomputable def kingModuli (g : ProjectiveClass R) : AlgebraicGeometry.Scheme :=
  kingProj b d P.vertex (P.characterExponents g)

/-- The geometric condition at the specified weight and vector. -/
def atMostOneKingClosedPoint (g : ProjectiveClass R) : Prop :=
  Set.Subsingleton {x : P.kingModuli b d g | IsClosed ({x} : Set (P.kingModuli b d g))}

end SplitBasicVertices

end EFiniteCharacterizations.VertexRepresentation
