module

public import EFiniteCharacterizations.Presentations.RigidPencil
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.CategoryTheory.Preadditive.Comma

/-! # Linear spaces of commuting squares -/

@[expose] public section

open CategoryTheory

namespace EFiniteCharacterizations

namespace ArrowHom

variable {k : Type*} [Field k] {C : Type*} [Category C] [Preadditive C] [Linear k C]
  (p q : Arrow C)

/-- The two components of an arrow morphism. -/
def pairAddHom : (p ⟶ q) →+ (p.left ⟶ q.left) × (p.right ⟶ q.right) where
  toFun f := (f.left, f.right)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem pairAddHom_injective : Function.Injective (pairAddHom p q) := by
  intro f g h
  exact Arrow.hom_ext f g (congrArg Prod.fst h) (congrArg Prod.snd h)

instance : SMul k (p ⟶ q) where
  smul a f := Arrow.homMk (a • f.left) (a • f.right) (by
    rw [Linear.smul_comp, Linear.comp_smul, f.w])

@[simp] theorem smul_left (a : k) (f : p ⟶ q) : (a • f).left = a • f.left := rfl

@[simp] theorem smul_right (a : k) (f : p ⟶ q) : (a • f).right = a • f.right := rfl

instance instModule : Module k (p ⟶ q) :=
  Function.Injective.module k (pairAddHom p q) (pairAddHom_injective p q) (fun _ _ ↦ rfl)

instance : Linear k (Arrow C) where
  homModule := instModule
  smul_comp X Y Z a f g := by
    apply Arrow.hom_ext
    · exact Linear.smul_comp X.left Y.left Z.left a f.left g.left
    · exact Linear.smul_comp X.right Y.right Z.right a f.right g.right
  comp_smul X Y Z f a g := by
    apply Arrow.hom_ext
    · exact Linear.comp_smul X.left Y.left Z.left f.left a g.left
    · exact Linear.comp_smul X.right Y.right Z.right f.right a g.right

variable (k)

/-- The pair of components as a linear map. -/
def pairLinear : (p ⟶ q) →ₗ[k] (p.left ⟶ q.left) × (p.right ⟶ q.right) :=
  { pairAddHom p q with map_smul' := fun _ _ ↦ rfl }

@[simp] theorem pairLinear_apply (f : p ⟶ q) : pairLinear k p q f = (f.left, f.right) := rfl

/-- Arrow morphisms are exactly the kernel of the chain-map equation. -/
noncomputable def equivKernel : (p ⟶ q) ≃ₗ[k] (boundaryLinear k p.hom q.hom).ker :=
  LinearEquiv.ofBijective ((pairLinear k p q).codRestrict _ (fun f ↦ sub_eq_zero.mpr f.w)) ⟨
    fun _ _ e ↦ pairAddHom_injective p q (congrArg Subtype.val e),
    fun z ↦ ⟨Arrow.homMk z.val.1 z.val.2 (sub_eq_zero.mp z.property), Subtype.ext rfl⟩⟩

@[simp] theorem equivKernel_val (f : p ⟶ q) :
    (equivKernel k p q f).val = pairLinear k p q f := rfl

end ArrowHom

end EFiniteCharacterizations
