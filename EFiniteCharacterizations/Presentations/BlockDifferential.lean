module

public import EFiniteCharacterizations.Presentations.RigidPencilComparison
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # A block extension of two-term differentials -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace EFiniteCharacterizations

section Preadditive

variable {C : Type*} [Category C] [Preadditive C]
  {E₁ E₀ L₁ L₀ : C} [HasBinaryBiproduct E₁ L₁] [HasBinaryBiproduct E₀ L₀]
  (d : E₁ ⟶ E₀) (l : L₁ ⟶ L₀) (w : L₁ ⟶ E₀)

/-- The block differential of the extension of `l` by `d` given by `w`. -/
noncomputable def blockDifferential : E₁ ⊞ L₁ ⟶ E₀ ⊞ L₀ :=
  biprod.desc (d ≫ biprod.inl) (biprod.lift w l)

@[reassoc (attr := simp)] theorem inl_blockDifferential :
    biprod.inl ≫ blockDifferential d l w = d ≫ biprod.inl := by
  simp [blockDifferential]

@[reassoc (attr := simp)] theorem inr_blockDifferential_fst :
    biprod.inr ≫ blockDifferential d l w ≫ biprod.fst = w := by
  simp [blockDifferential]

@[reassoc (attr := simp)] theorem blockDifferential_snd :
    blockDifferential d l w ≫ biprod.snd = biprod.snd ≫ l := by
  apply biprod.hom_ext' <;> simp [blockDifferential]

theorem blockDifferential_zero : blockDifferential d l 0 = biprod.map d l := by
  apply biprod.hom_ext'
  · simp
  · apply biprod.hom_ext <;> simp [blockDifferential]

end Preadditive

section Linear

variable (k : Type*) [Field k] {C : Type*} [Category C] [Preadditive C] [Linear k C]

/-- Cokernel of the boundary map for degree-one morphisms between two differentials. -/
abbrev BoundaryCokernel {V₁ V₀ W₁ W₀ : C} (v : V₁ ⟶ V₀) (p : W₁ ⟶ W₀) :=
  (V₁ ⟶ W₀) ⧸ (boundaryLinear k v p).range

variable {E₁ E₀ L₁ L₀ V₁ V₀ : C} [HasBinaryBiproduct E₁ L₁] [HasBinaryBiproduct E₀ L₀]
  (d : E₁ ⟶ E₀) (l : L₁ ⟶ L₀) (w : L₁ ⟶ E₀) (v : V₁ ⟶ V₀)

/-- Inclusion of the first block on degree-one Hom cokernels. -/
noncomputable def blockCokernelInclusion :
    BoundaryCokernel k v d →ₗ[k] BoundaryCokernel k v (blockDifferential d l w) :=
  (boundaryLinear k v d).range.mapQ _ (Linear.rightComp k V₁ biprod.inl) (by
    rintro g ⟨⟨a, b⟩, rfl⟩
    refine ⟨(a ≫ biprod.inl, b ≫ biprod.inl), ?_⟩
    simp [boundaryLinear_apply, Preadditive.sub_comp, Category.assoc])

/-- Projection onto the second block on the opposite degree-one Hom cokernels. -/
noncomputable def blockCokernelProjection :
    BoundaryCokernel k l v →ₗ[k] BoundaryCokernel k (blockDifferential d l w) v :=
  (boundaryLinear k l v).range.mapQ _ (Linear.leftComp k V₀ biprod.snd) (by
    rintro g ⟨⟨a, b⟩, rfl⟩
    refine ⟨(biprod.snd ≫ a, biprod.snd ≫ b), ?_⟩
    simp [boundaryLinear_apply, Preadditive.comp_sub, Category.assoc])

theorem blockCokernelInclusion_surjective (h : Function.Surjective (boundaryLinear k v l)) :
    Function.Surjective (blockCokernelInclusion k d l w v) := by
  intro y
  obtain ⟨f, rfl⟩ := (boundaryLinear k v (blockDifferential d l w)).range.mkQ_surjective y
  obtain ⟨⟨a, b⟩, hab⟩ := h (f ≫ biprod.snd)
  let g := boundaryLinear k v (blockDifferential d l w) (a ≫ biprod.inr, b ≫ biprod.inr)
  have hg : g ≫ biprod.snd = f ≫ biprod.snd := by
    rw [← hab]
    simp [g, Preadditive.sub_comp, Category.assoc]
  let f' := (f - g) ≫ biprod.fst
  have hf : f' ≫ biprod.inl = f - g := by
    apply biprod.hom_ext
    · simp [f', Category.assoc]
    · simp [f', Category.assoc, Preadditive.sub_comp, hg]
  use (boundaryLinear k v d).range.mkQ f'
  change (boundaryLinear k v (blockDifferential d l w)).range.mkQ (f' ≫ biprod.inl) = _
  have hz : (boundaryLinear k v (blockDifferential d l w)).range.mkQ g = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
  rw [hf, map_sub, hz, sub_zero]

theorem blockCokernelProjection_surjective (h : Function.Surjective (boundaryLinear k d v)) :
    Function.Surjective (blockCokernelProjection k d l w v) := by
  intro y
  obtain ⟨f, rfl⟩ := (boundaryLinear k (blockDifferential d l w) v).range.mkQ_surjective y
  obtain ⟨⟨a, b⟩, hab⟩ := h (biprod.inl ≫ f)
  let g := boundaryLinear k (blockDifferential d l w) v (biprod.fst ≫ a, biprod.fst ≫ b)
  have hg : biprod.inl ≫ g = biprod.inl ≫ f := by
    rw [← hab]
    simp [g, Preadditive.comp_sub, Category.assoc]
  let f' := biprod.inr ≫ (f - g)
  have hf : biprod.snd ≫ f' = f - g := by
    apply biprod.hom_ext'
    · simp [f', ← Category.assoc, Preadditive.comp_sub, hg]
    · simp [f', ← Category.assoc]
  use (boundaryLinear k l v).range.mkQ f'
  change (boundaryLinear k (blockDifferential d l w) v).range.mkQ (biprod.snd ≫ f') = _
  have hz : (boundaryLinear k (blockDifferential d l w) v).range.mkQ g = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
  rw [hf, map_sub, hz, sub_zero]

theorem blockCokernelInclusion_extensionClass :
    blockCokernelInclusion k d l w l ((boundaryLinear k l d).range.mkQ w) = 0 := by
  change Submodule.Quotient.mk (w ≫ biprod.inl) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨(biprod.inr, biprod.inr), ?_⟩
  rw [boundaryLinear_apply]
  apply biprod.hom_ext
  · simp [Preadditive.sub_comp, Category.assoc]
  · simp [Preadditive.sub_comp, Category.assoc]

theorem blockCokernelProjection_extensionClass :
    blockCokernelProjection k d l w d ((boundaryLinear k l d).range.mkQ w) = 0 := by
  change Submodule.Quotient.mk (biprod.snd ≫ w) = 0
  rw [← neg_neg (biprod.snd ≫ w), Submodule.Quotient.mk_eq_zero]
  apply Submodule.neg_mem
  refine ⟨(biprod.fst, biprod.fst), ?_⟩
  rw [boundaryLinear_apply]
  apply biprod.hom_ext'
  · simp [Preadditive.comp_sub, inl_blockDifferential_assoc d l w]
  · simp [Preadditive.comp_sub]

end Linear

end EFiniteCharacterizations
