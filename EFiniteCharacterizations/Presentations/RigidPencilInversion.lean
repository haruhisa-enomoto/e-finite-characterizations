module

public import EFiniteCharacterizations.LinearAlgebra.PencilKernel
public import EFiniteCharacterizations.Presentations.RigidPencil

/-!
# Specialization of module-theoretic inversion along a presilting pencil

Shows that if an `R`-module `N` (possibly infinite-dimensional) inverts any map
`σ : P.source → P.target` on the projective terms of a two-term presilting complex
`P`, then `N` also inverts the presilting differential `P.differential`
(`TwoTerm.bijective_leftComp_of_isPresilting`). This drives the direct inductive
proof that universal localizations of E-finite algebras are finite-dimensional.
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace EFiniteCharacterizations

variable (k : Type*) [Field k] {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {X Y : C} [Module.Finite k (X ⟶ X)] [Module.Finite k (Y ⟶ Y)] [Module.Finite k (X ⟶ Y)]

/-- Injectivity of precomposition at any differential on the same terms
implies injectivity at the rigid differential, with arbitrary target. -/
theorem injective_leftComp_at_rigid (u σ : X ⟶ Y) (N : C)
    (hu : Function.Surjective (boundaryLinear k u u))
    (hσ : Function.Injective (Linear.leftComp k N σ)) : Function.Injective (Linear.leftComp k N u) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.2
  intro f hf
  change u ≫ f = 0 at hf
  let δ := σ - u
  let t := - (Linear.leftComp k Y δ).comp (LinearMap.snd k (X ⟶ X) (Y ⟶ Y))
  let m := (Linear.rightComp k Y f).comp (LinearMap.snd k (X ⟶ X) (Y ⟶ Y))
  let n := -(Linear.rightComp k X f)
  have hi : Linear.leftComp k N u + Linear.leftComp k N δ = Linear.leftComp k N σ := by
    ext g
    change u ≫ g + (σ - u) ≫ g = σ ≫ g
    rw [Preadditive.sub_comp]; abel
  have hh := eq_zero_of_pencil_intertwiner (boundaryLinear k u u) t hu (𝟙 X,𝟙 Y) (by simp)
    (Linear.leftComp k N u) (Linear.leftComp k N δ) (hi ▸ hσ) m n
    (LinearMap.ext fun ⟨a,b⟩ ↦ by
      change u ≫ b ≫ f = -((a ≫ u - u ≫ b) ≫ f)
      simp [Preadditive.sub_comp,Category.assoc,hf])
    (LinearMap.ext fun ⟨a,b⟩ ↦ by
      change δ ≫ b ≫ f = -((-(δ ≫ b)) ≫ f)
      simp)
  simpa [m] using hh

/-- The transpose of precomposition, viewed as a linear function of the
arrow with a fixed functional on the source Hom space. -/
private def transposePrecomp {A B : C} (N : C) (w : Module.Dual k (A ⟶ N)) :
    (A ⟶ B) →ₗ[k] Module.Dual k (B ⟶ N) where
  toFun a := w.comp (Linear.leftComp k N a)
  map_add' a b := LinearMap.ext fun f ↦ by simp [Preadditive.add_comp]
  map_smul' r a := LinearMap.ext fun f ↦ by simp [Linear.smul_comp]

/-- Surjectivity of precomposition also specializes to the rigid differential.
The algebraic dual detects surjectivity without a finiteness hypothesis on N. -/
theorem surjective_leftComp_at_rigid (u σ : X ⟶ Y) (N : C)
    (hu : Function.Surjective (boundaryLinear k u u))
    (hσ : Function.Surjective (Linear.leftComp k N σ)) : Function.Surjective (Linear.leftComp k N u) := by
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.2
  intro w hw
  have hw' (f : Y ⟶ N) : w (u ≫ f) = 0 := DFunLike.congr_fun hw f
  let δ := σ - u
  let t := (Linear.rightComp k X δ).comp (LinearMap.fst k (X ⟶ X) (Y ⟶ Y))
  let m := (transposePrecomp k (B := X) N w).comp (LinearMap.fst k (X ⟶ X) (Y ⟶ Y))
  let n := transposePrecomp k (B := Y) N w
  have hi : (Linear.leftComp k N u).dualMap + (Linear.leftComp k N δ).dualMap =
      (Linear.leftComp k N σ).dualMap := by
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro f
    change g (u ≫ f) + g ((σ - u) ≫ f) = g (σ ≫ f)
    rw [Preadditive.sub_comp,map_sub]; abel
  have hh := eq_zero_of_pencil_intertwiner (boundaryLinear k u u) t hu (𝟙 X,𝟙 Y) (by simp)
    (Linear.leftComp k N u).dualMap (Linear.leftComp k N δ).dualMap (hi ▸ LinearMap.dualMap_injective_iff.mpr hσ) m n
    (LinearMap.ext fun ⟨a,b⟩ ↦ LinearMap.ext fun f ↦ by
      change w (a ≫ u ≫ f) = w ((a ≫ u - u ≫ b) ≫ f)
      simp [Preadditive.sub_comp,Category.assoc,hw'])
    (LinearMap.ext fun ⟨a,b⟩ ↦ LinearMap.ext fun f ↦ by
      change w (a ≫ δ ≫ f) = w ((a ≫ δ) ≫ f)
      rw [Category.assoc])
  exact LinearMap.ext fun f ↦ by simpa [m,transposePrecomp] using DFunLike.congr_fun hh f

universe u

/-- Any module inverting a map on the terms of a presilting presentation
also inverts its differential. -/
theorem TwoTerm.bijective_leftComp_of_isPresilting (K : Type u) [Field K]
    {R : Type u} [Ring R] [Algebra K R] [Module.Finite K R]
    (P : TwoTerm R) (hP : P.IsPresilting) (σ : P.source ⟶ P.target)
    (N : ModuleCat.{u} R) (hσ : Function.Bijective (Linear.leftComp K N σ.hom)) :
    Function.Bijective (Linear.leftComp K N P.differential.hom) := by
  have finiteHom (A B : FGModuleCat.{u} R) : Module.Finite K (A.obj ⟶ B.obj) := by
    let e : (A ⟶ B) ≃ₗ[K] (A.obj ⟶ B.obj) := InducedCategory.homLinearEquiv
    have := finiteModuleHom_isFinite K A B
    exact Module.Finite.equiv e
  have := finiteHom P.source P.source
  have := finiteHom P.target P.target
  have := finiteHom P.source P.target
  have hu : Function.Surjective (boundaryLinear K P.differential.hom P.differential.hom) := by
    intro f
    obtain ⟨⟨a, b⟩, h⟩ := hP (InducedCategory.homMk f)
    exact ⟨(a.hom, b.hom), congrArg (·.hom) h⟩
  exact ⟨injective_leftComp_at_rigid K _ σ.hom N hu hσ.1,
    surjective_leftComp_at_rigid K _ σ.hom N hu hσ.2⟩

end EFiniteCharacterizations
