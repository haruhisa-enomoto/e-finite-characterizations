module

public import EFiniteCharacterizations.Presentations.ExtensionBounds

/-! # Shifted Hom for direct sums of two-term complexes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace EFiniteCharacterizations

section Linear

variable (k : Type*) [Field k] {C : Type*} [Category C] [Preadditive C] [Linear k C]
  {E₁ E₀ L₁ L₀ V₁ V₀ : C} [HasBinaryBiproduct E₁ L₁] [HasBinaryBiproduct E₀ L₀]
  (d : E₁ ⟶ E₀) (l : L₁ ⟶ L₀) (v : V₁ ⟶ V₀)

/-- The shifted Hom cokernel in the second variable preserves a binary direct sum. -/
noncomputable def boundaryCokernel_biprod_target :
    BoundaryCokernel k v (biprod.map d l) ≃ₗ[k]
      BoundaryCokernel k v d × BoundaryCokernel k v l := by
  let R := (boundaryLinear k v (biprod.map d l)).range
  let S := (boundaryLinear k v d).range
  let T := (boundaryLinear k v l).range
  have hfst (a : V₁ ⟶ E₁ ⊞ L₁) (b : V₀ ⟶ E₀ ⊞ L₀) :
      boundaryLinear k v (biprod.map d l) (a, b) ≫ biprod.fst =
        boundaryLinear k v d (a ≫ biprod.fst, b ≫ biprod.fst) := by
    simp [Preadditive.sub_comp, Category.assoc]
  have hsnd (a : V₁ ⟶ E₁ ⊞ L₁) (b : V₀ ⟶ E₀ ⊞ L₀) :
      boundaryLinear k v (biprod.map d l) (a, b) ≫ biprod.snd =
        boundaryLinear k v l (a ≫ biprod.snd, b ≫ biprod.snd) := by
    simp [Preadditive.sub_comp, Category.assoc]
  let p := R.mapQ S (Linear.rightComp k V₁ biprod.fst) (by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact ⟨_, (hfst a b).symm⟩)
  let q := R.mapQ T (Linear.rightComp k V₁ biprod.snd) (by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact ⟨_, (hsnd a b).symm⟩)
  let f := p.prod q
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro z hz
    obtain ⟨g, rfl⟩ := R.mkQ_surjective z
    have hp : S.mkQ (g ≫ biprod.fst) = 0 := congrArg Prod.fst (show f (R.mkQ g) = 0 from hz)
    have hq : T.mkQ (g ≫ biprod.snd) = 0 := congrArg Prod.snd (show f (R.mkQ g) = 0 from hz)
    obtain ⟨⟨a₁, b₁⟩, ha⟩ := (Submodule.Quotient.mk_eq_zero S).mp hp
    obtain ⟨⟨a₂, b₂⟩, hb⟩ := (Submodule.Quotient.mk_eq_zero T).mp hq
    apply (Submodule.mem_bot k).mpr ((Submodule.Quotient.mk_eq_zero R).mpr ?_)
    refine ⟨(biprod.lift a₁ a₂, biprod.lift b₁ b₂), ?_⟩
    apply biprod.hom_ext
    · rw [hfst]; simpa using ha
    · rw [hsnd]; simpa using hb
  · intro ⟨x, y⟩
    obtain ⟨a, rfl⟩ := S.mkQ_surjective x
    obtain ⟨b, rfl⟩ := T.mkQ_surjective y
    refine ⟨R.mkQ (biprod.lift a b), Prod.ext ?_ ?_⟩
    · change S.mkQ (biprod.lift a b ≫ biprod.fst) = _; simp
    · change T.mkQ (biprod.lift a b ≫ biprod.snd) = _; simp

/-- The shifted Hom cokernel in the first variable preserves a binary direct sum. -/
noncomputable def boundaryCokernel_biprod_source :
    BoundaryCokernel k (biprod.map d l) v ≃ₗ[k]
      BoundaryCokernel k d v × BoundaryCokernel k l v := by
  let R := (boundaryLinear k (biprod.map d l) v).range
  let S := (boundaryLinear k d v).range
  let T := (boundaryLinear k l v).range
  have hinl (a : E₁ ⊞ L₁ ⟶ V₁) (b : E₀ ⊞ L₀ ⟶ V₀) :
      biprod.inl ≫ boundaryLinear k (biprod.map d l) v (a, b) =
        boundaryLinear k d v (biprod.inl ≫ a, biprod.inl ≫ b) := by
    simp [Preadditive.comp_sub, Category.assoc]
  have hinr (a : E₁ ⊞ L₁ ⟶ V₁) (b : E₀ ⊞ L₀ ⟶ V₀) :
      biprod.inr ≫ boundaryLinear k (biprod.map d l) v (a, b) =
        boundaryLinear k l v (biprod.inr ≫ a, biprod.inr ≫ b) := by
    simp [Preadditive.comp_sub, Category.assoc]
  let p := R.mapQ S (Linear.leftComp k V₀ biprod.inl) (by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact ⟨_, (hinl a b).symm⟩)
  let q := R.mapQ T (Linear.leftComp k V₀ biprod.inr) (by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact ⟨_, (hinr a b).symm⟩)
  let f := p.prod q
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro z hz
    obtain ⟨g, rfl⟩ := R.mkQ_surjective z
    have hp : S.mkQ (biprod.inl ≫ g) = 0 := congrArg Prod.fst (show f (R.mkQ g) = 0 from hz)
    have hq : T.mkQ (biprod.inr ≫ g) = 0 := congrArg Prod.snd (show f (R.mkQ g) = 0 from hz)
    obtain ⟨⟨a₁, b₁⟩, ha⟩ := (Submodule.Quotient.mk_eq_zero S).mp hp
    obtain ⟨⟨a₂, b₂⟩, hb⟩ := (Submodule.Quotient.mk_eq_zero T).mp hq
    apply (Submodule.mem_bot k).mpr ((Submodule.Quotient.mk_eq_zero R).mpr ?_)
    refine ⟨(biprod.desc a₁ a₂, biprod.desc b₁ b₂), ?_⟩
    apply biprod.hom_ext'
    · rw [hinl]; simpa using ha
    · rw [hinr]; simpa using hb
  · intro ⟨x, y⟩
    obtain ⟨a, rfl⟩ := S.mkQ_surjective x
    obtain ⟨b, rfl⟩ := T.mkQ_surjective y
    refine ⟨R.mkQ (biprod.desc a b), Prod.ext ?_ ?_⟩
    · change S.mkQ (biprod.inl ≫ biprod.desc a b) = _; simp
    · change T.mkQ (biprod.inr ≫ biprod.desc a b) = _; simp

end Linear

namespace TwoTerm

universe u

variable {R : Type u} [Ring R]

/-- The degreewise direct sum of two two-term complexes. -/
noncomputable def directSum (P Q : TwoTerm R) : TwoTerm R := P.blockExtension Q 0

/-- A contractible two-term complex with both terms equal to one projective. -/
abbrev contractible (P : FiniteProjective R) : TwoTerm R :=
  ⟨P.val, P.val, P.property, P.property, 𝟙 P.val⟩

@[simp] theorem projectiveClass_directSum (P Q : TwoTerm R) :
    (P.directSum Q).projectiveClass = P.projectiveClass + Q.projectiveClass :=
  projectiveClass_blockExtension P Q 0

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

theorem shiftedHomFinrank_directSum_target (P Q V : TwoTerm R) :
    V.shiftedHomFinrank k (P.directSum Q) = V.shiftedHomFinrank k P + V.shiftedHomFinrank k Q := by
  have := finiteModuleHom_isFinite k V.source P.target
  have := finiteModuleHom_isFinite k V.source Q.target
  change Module.finrank k (BoundaryCokernel k V.differential
    (blockDifferential P.differential Q.differential 0)) = _
  rw [blockDifferential_zero, (boundaryCokernel_biprod_target k P.differential Q.differential V.differential).finrank_eq,
    Module.finrank_prod]
  rfl

theorem shiftedHomFinrank_directSum_source (P Q V : TwoTerm R) :
    (P.directSum Q).shiftedHomFinrank k V = P.shiftedHomFinrank k V + Q.shiftedHomFinrank k V := by
  have := finiteModuleHom_isFinite k P.source V.target
  have := finiteModuleHom_isFinite k Q.source V.target
  change Module.finrank k (BoundaryCokernel k (blockDifferential P.differential Q.differential 0)
    V.differential) = _
  rw [blockDifferential_zero, (boundaryCokernel_biprod_source k P.differential Q.differential V.differential).finrank_eq,
    Module.finrank_prod]
  rfl

theorem shiftedHomFinrank_contractible_target (P : FiniteProjective R) (V : TwoTerm R) :
    V.shiftedHomFinrank k (contractible P) = 0 := by
  apply (shiftedHomFinrank_eq_zero_iff k _ _).2
  intro f
  refine ⟨(f, 0), ?_⟩
  change f ≫ 𝟙 P.val - V.differential ≫ 0 = f
  simp

theorem shiftedHomFinrank_contractible_source (P : FiniteProjective R) (V : TwoTerm R) :
    (contractible P).shiftedHomFinrank k V = 0 := by
  apply (shiftedHomFinrank_eq_zero_iff k _ _).2
  intro f
  refine ⟨(0, -f), ?_⟩
  change 0 ≫ V.differential - 𝟙 P.val ≫ (-f) = f
  simp

@[simp] theorem shiftedHomFinrank_directSum_contractible_source (P Q : TwoTerm R) (T : FiniteProjective R) :
    (P.directSum (contractible T)).shiftedHomFinrank k Q = P.shiftedHomFinrank k Q := by
  rw [shiftedHomFinrank_directSum_source, shiftedHomFinrank_contractible_source, add_zero]

@[simp] theorem shiftedHomFinrank_directSum_contractible_target (P Q : TwoTerm R) (T : FiniteProjective R) :
    Q.shiftedHomFinrank k (P.directSum (contractible T)) = Q.shiftedHomFinrank k P := by
  rw [shiftedHomFinrank_directSum_target, shiftedHomFinrank_contractible_target, add_zero]

theorem isPresilting_directSum_iff (P Q : TwoTerm R) : (P.directSum Q).IsPresilting ↔
    P.IsPresilting ∧ Q.IsPresilting ∧ P.shiftedHomFinrank k Q = 0 ∧ Q.shiftedHomFinrank k P = 0 := by
  simp only [IsPresilting, ← shiftedHomFinrank_eq_zero_iff k, shiftedHomFinrank_directSum_source,
    shiftedHomFinrank_directSum_target]
  omega

include k in
theorem isPresilting_directSum_contractible_iff (P : TwoTerm R) (T : FiniteProjective R) :
    (P.directSum (contractible T)).IsPresilting ↔ P.IsPresilting := by
  simp only [IsPresilting, ← shiftedHomFinrank_eq_zero_iff k,
    shiftedHomFinrank_directSum_contractible_source, shiftedHomFinrank_directSum_contractible_target]

end TwoTerm

end EFiniteCharacterizations
