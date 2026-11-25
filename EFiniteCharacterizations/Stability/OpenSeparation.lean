module

public import EFiniteCharacterizations.Subcategories.BrickFiltrationEquivalences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Zariski-open Hom–Ext separation bounds family size

Lemma A.4 (`lem:open-sep`) of Appendix A: in a fixed `k`-dimension `d`, any family of
`R`-modules `{B_i}` whose members can be pairwise isolated by witness modules `G_i`
satisfying `Hom(G_i, B_i) ≠ 0`, `Ext¹(G_i, B_i) = 0`, and `Hom(G_i, B_j) = 0` for
`j ≠ i` must be finite (`finite_of_hom_ext_separation`).
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R]

local instance : HasExt.{u+1} (FGModuleCat.{u} R) := HasExt.standard _

/-- Among modules of any fixed ground dimension, each member of a family
can be isolated by a module detecting it by Hom and having vanishing Ext¹
against it only if the family is finite. -/
theorem finite_of_hom_ext_separation (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]
    {I : Type*} (B : I → FGModuleCat.{u} R) {d : ℕ}
    (hd : ∀ i, Module.finrank k ((B i).obj : Type u) = d)
    (sep : ∀ i, ∃ G : FGModuleCat.{u} R, (∃ f : G ⟶ B i, f ≠ 0) ∧
      Subsingleton (Ext.{u+1} G (B i) 1) ∧ ∀ j, i ≠ j → ∀ f : G ⟶ B j, f = 0) : Finite I := by
  classical
  let _ (i : I) : Module.Finite k ((B i).obj : Type u) := Module.Finite.trans R _
  let b (i : I) := (Module.finBasis k ((B i).obj : Type u)).reindex (finCongr (hd i))
  apply FreeHom.finite_of_isolating_complexes k B (fun _ ↦ k) b
  intro i
  obtain ⟨G,hHom,hExt,hOff⟩ := sep i
  apply exists_isolating_complex_of_module B i G hHom _ hOff
  intro a p hp z
  let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  have hs : S.ShortExact := .mk' (ShortComplex.exact_kernel p) (by dsimp [S]; infer_instance) hp
  obtain ⟨e,he⟩ := Ext.contravariant_sequence_exact₁ hs (B i) (Ext.mk₀ z) (n₁ := 1) rfl (hExt.elim _ _)
  obtain ⟨s,rfl⟩ := (Ext.mk₀_bijective _ _).2 e
  exact ⟨s,(Ext.mk₀_bijective _ _).1 ((Ext.mk₀_comp_mk₀ _ _).symm.trans he)⟩

end EFiniteCharacterizations
