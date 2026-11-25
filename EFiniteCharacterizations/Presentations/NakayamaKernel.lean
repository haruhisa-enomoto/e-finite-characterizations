module

public import EFiniteCharacterizations.Modules.HomDimension
public import EFiniteCharacterizations.Modules.Nakayama.Hom
public import EFiniteCharacterizations.Presentations.TwoTerm

/-! # The Nakayama kernel of a two-term differential -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]

/-- The Nakayama module of a finite module over a finite-dimensional algebra. -/
noncomputable def nakayamaObject (P : FGModuleCat.{u} R) : FGModuleCat.{u} R := by
  have : Module.Finite R (P.obj : Type u) := P.property
  have : Module.Finite k (P.obj : Type u) := Module.Finite.trans R _
  have : Module.Finite k (NakayamaModule k R (P.obj : Type u)) :=
    Module.Finite.equiv (NakayamaModule.equivDual k R (P.obj : Type u)).symm
  have : Module.Finite R (NakayamaModule k R (P.obj : Type u)) :=
    Module.Finite.of_restrictScalars_finite k R _
  exact FGModuleCat.of R (NakayamaModule k R (P.obj : Type u))

/-- The map induced by the Nakayama functor. -/
noncomputable def nakayamaMorphism {P Q : FGModuleCat.{u} R} (f : P ⟶ Q) :
    nakayamaObject k P ⟶ nakayamaObject k Q :=
  ObjectProperty.homMk (ModuleCat.ofHom (f.hom.hom.nakayamaMap (k := k)))

/-- The kernel of the Nakayama transform of the differential. -/
noncomputable def TwoTerm.nakayamaKernel [IsNoetherianRing R] (P : TwoTerm R) :
    FGModuleCat.{u} R :=
  kernel (nakayamaMorphism k P.differential)

end EFiniteCharacterizations
