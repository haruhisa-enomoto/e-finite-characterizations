module

public import EFiniteCharacterizations.Geometry.InfiniteMatrixImage
public import EFiniteCharacterizations.Algebra.MatrixImageEpimorphism
public import EFiniteCharacterizations.Algebra.MatrixImageSimpleArtinian
public import EFiniteCharacterizations.LargeModules.GenericBrickExclusion

/-!
# Simple Artinian epimorphic targets and the `(no-gen-brick)` characterization

Theorem 7.8 (`thm:large`) of the manuscript: constructs an infinite-dimensional simple
Artinian ring-epimorphic target from a missing integral weight over any field
(`isEFinite_of_simpleArtinianEpicTargetsFinite`) and deduces
`isEFinite_iff_no_generic_right_brick` (`(E-fin) ⇔ (no-gen-brick)`).
-/

@[expose] public section

universe u
namespace EFiniteCharacterizations.FieldExtension

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]

theorem isEFinite_of_simpleArtinianEpicTargetsFinite (h : SimpleArtinianEpicTargetsFinite k R) :
    IsEFinite R := by
  classical
  by_contra hn
  obtain ⟨P,B,_,_,f,hf,d,hd,K,_,q,hspan,_,hinf⟩ := exists_infinite_prime_localization_image k hn
  let : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let b := Module.Basis.ofSpan hspan.ge
  have hb := Module.Basis.ofSpan_subset hspan.ge
  let := FiniteDimensional.fintypeBasisIndex b
  let H := matrixImageAlgebra q b
  let Q := toMatrixImageAlgebra q b
  have hQ := toMatrixImageAlgebra_epi q b hb
  let := hQ.targetAlgebra k
  let Q' : B →ₐ[k] H := { __ := Q, commutes' := fun _ ↦ rfl }
  let : IsSimpleRing H := matrixImage_simple q b hb
  let : IsArtinianRing H := matrixImage_artinian q b hb
  have hep : IsRingEpimorphism (Q'.comp f).toRingHom := by
    intro T _ g j he
    apply hQ T g j
    exact hf.epic T _ _ he
  let : Module.Finite k H := h H (Q'.comp f) hep
  let := imageAlgebra (k := k) q
  let inc : q.range →ₐ[k] H :=
    { toFun := fun x ↦ ⟨x.val, Algebra.subset_adjoin x.property⟩
      map_one' := rfl
      map_zero' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  exact hinf (Module.Finite.of_injective inc.toLinearMap (fun _ _ he ↦ Subtype.ext (congrArg (fun z : H ↦ z.val) he)))

theorem isEFinite_iff_no_generic_right_brick :
    IsEFinite R ↔ ¬ ∃ M : ModuleCat.{u} Rᵐᵒᵖ, IsGenericBrick k M :=
  ⟨no_generic_right_brick_of_isEFinite k, fun h ↦ isEFinite_of_simpleArtinianEpicTargetsFinite k
    ((no_generic_right_brick_iff_simpleArtinianEpicTargetsFinite k).1 h)⟩

theorem isEFinite_iff_simpleArtinianEpicTargetsFinite :
    IsEFinite R ↔ SimpleArtinianEpicTargetsFinite k R :=
  (isEFinite_iff_no_generic_right_brick k).trans
    (no_generic_right_brick_iff_simpleArtinianEpicTargetsFinite k)

end EFiniteCharacterizations.FieldExtension
