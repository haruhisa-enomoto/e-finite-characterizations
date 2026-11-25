module

public import EFiniteCharacterizations.RingEpimorphisms.FiniteDimensionalResidual
public import EFiniteCharacterizations.Geometry.InfiniteMatrixImage
public import EFiniteCharacterizations.Stability.OppositeAlgebra

/-! # Residually finite-dimensional quotients of ground localization charts -/

@[expose] public section
open CategoryTheory
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R B : Type u} [Ring R] [Algebra k R] [Ring B] [Algebra k B]

private theorem singleton_generators [Module.Finite k R] (P : TwoTerm R) (f : R →ₐ[k] B)
    (hf : IsUniversalLocalization (fun _ : Unit ↦ P) f.toRingHom) :
    ∃ S : Set B, S.Finite ∧ Algebra.adjoin k S = ⊤ := by
  obtain ⟨A,_,_,g,hg,S,hS,hgen⟩ := exists_finitely_generated_singleton_localization k P
  obtain ⟨p,hp,_⟩ := hg.desc B f.toRingHom hf.inverts
  obtain ⟨q,hq,_⟩ := hf.desc A g.toRingHom hg.inverts
  let a : A →ₐ[k] B :=
    { __ := p
      commutes' := fun c ↦ (congrArg p (g.commutes c).symm).trans
        ((DFunLike.congr_fun hp _).trans (f.commutes c)) }
  have hi : p.comp q = RingHom.id B := by
    apply hf.epic
    rw [RingHom.comp_assoc,hq,hp,RingHom.id_comp]
  have sur : Function.Surjective a := fun b ↦ ⟨q b,DFunLike.congr_fun hi b⟩
  refine ⟨a '' S,hS.image _,?_⟩
  rw [← AlgHom.map_adjoin,hgen,Algebra.map_top,(AlgHom.range_eq_top a).mpr sur]

/-- Over an algebraic field extension, a representation of a finitely
generated algebra has finite-dimensional ground image. -/
private theorem finite_matrix_image {F : Type u} [Field F] [Algebra k F] [Algebra.IsAlgebraic k F]
    {m : Type} [Fintype m] [DecidableEq m] (S : Set B) (hS : S.Finite) (hgen : Algebra.adjoin k S = ⊤)
    (ρ : B →ₐ[k] Matrix m m F) : Module.Finite k ρ.range := by
  classical
  let := hS.fintype
  let entry (i : S × m × m) := ρ i.1 i.2.1 i.2.2
  let E := IntermediateField.adjoin k (Set.range entry)
  let : Module.Finite k E := IntermediateField.finiteDimensional_adjoin
    (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  let a : Matrix m m E →ₐ[k] Matrix m m F := E.val.mapMatrix
  have hle : ρ.range ≤ a.range := by
    rw [← Algebra.map_top ρ,← hgen,AlgHom.map_adjoin]
    apply Algebra.adjoin_le
    rintro _ ⟨s,hs,rfl⟩
    refine ⟨fun i j ↦ ⟨ρ s i j,IntermediateField.subset_adjoin k _ ⟨(⟨s,hs⟩,i,j),rfl⟩⟩,rfl⟩
  let := Module.Finite.of_surjective a.rangeRestrict.toLinearMap a.rangeRestrict_surjective
  exact Module.Finite.of_injective (Subalgebra.inclusion hle).toLinearMap
    (fun _ _ he ↦ Subtype.ext (congrArg (fun z : a.range ↦ z.val) he))

/-- A missing integral weight yields one projective differential whose
localization remains infinite-dimensional modulo the common annihilator
of all finite-dimensional modules. -/
theorem exists_infinite_residual_localization [Module.Finite k R] (hn : ¬ IsEFinite R) :
    ∃ (P : TwoTerm R) (B : Type u) (_ : Ring B) (_ : Algebra k B) (f : R →ₐ[k] B),
      IsUniversalLocalization (fun _ : Unit ↦ P) f.toRingHom ∧
      ¬ Module.Finite k B ∧ ¬ Module.Finite k (B ⧸ finiteDimensionalResidual k B) := by
  obtain ⟨P,B,_,_,f,hf,d,hd,K,_,q,S,hS,_,_,hfib⟩ := FieldExtension.exists_generic_localization_family k hn
  obtain ⟨G,hG,hgen⟩ := singleton_generators k P f hf
  let p := Ideal.Quotient.mkₐ k (finiteDimensionalResidual k B)
  suffices hi : ¬ Module.Finite k (B ⧸ finiteDimensionalResidual k B) from
    ⟨P,B,inferInstance,inferInstance,f,hf,fun _ ↦ hi (Module.Finite.of_surjective
      p.toLinearMap (Ideal.Quotient.mkₐ_surjective k _)),hi⟩
  apply FieldExtension.infinite_of_matrix_specializations k f p hd hS
  intro x
  obtain ⟨M,v,ρ,hm,hr,hspan,_⟩ := hfib x
  let := finite_matrix_image k G hG hgen ρ
  exact ⟨M,v,ρ,hm,hr,hspan,liftFiniteImage k B ρ,fun _ ↦ rfl⟩

/-- Testing every residually finite-dimensional epic target characterizes
E-finiteness over an arbitrary field. -/
theorem isEFinite_iff_residuallyFiniteEpicTargetsFinite [Module.Finite k R] :
    IsEFinite R ↔ ∀ (B : Type u) [Ring B] [Algebra k B] (f : R →ₐ[k] B),
      IsRingEpimorphism f.toRingHom → IsResiduallyFiniteDimensional k B → Module.Finite k B := by
  let := IsNoetherianRing.of_finite k R
  let := IsArtinianRing.of_finite k R
  refine ⟨fun he _ _ _ f hf h ↦ finite_residuallyFinite_epic_target k he f hf h,fun H ↦ ?_⟩
  by_contra hn
  obtain ⟨P,B,_,_,f,hf,_,hi⟩ := exists_infinite_residual_localization k hn
  let p := Ideal.Quotient.mkₐ k (finiteDimensionalResidual k B)
  apply hi (H _ (p.comp f) _ (quotient_residuallyFiniteDimensional k B))
  intro A _ g h eqn
  have e : g.comp p.toRingHom = h.comp p.toRingHom := hf.epic A _ _ eqn
  apply RingHom.ext
  intro x
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mkₐ_surjective k _ x
  exact DFunLike.congr_fun e b

/-- The epic-target criterion for right modules and arbitrary ring maps,
with the target algebra structure induced by the epimorphism. -/
theorem isEFinite_iff_residuallyFinite_ring_epimorphisms [Module.Finite k R] :
    IsEFinite Rᵐᵒᵖ ↔ ∀ (B : Type u) [Ring B] (f : R →+* B) (hf : IsRingEpimorphism f),
      letI := hf.targetAlgebra k
      IsResiduallyFiniteDimensional k Bᵐᵒᵖ → Module.Finite k B := by
  rw [← isEFinite_iff_opposite k, isEFinite_iff_residuallyFiniteEpicTargetsFinite k]
  constructor
  · intro h B _ f hf
    let := hf.targetAlgebra k
    let g : R →ₐ[k] B := { __ := f, commutes' := fun _ ↦ rfl }
    intro hB
    exact h B g hf ((residuallyFiniteDimensional_iff_opposite k B).2 hB)
  · intro h B _ a f hf hB
    have ha : hf.targetAlgebra k = a := Algebra.algebra_ext _ _ fun r ↦ f.commutes r
    have hm := h B f.toRingHom hf
    let test := fun a' : Algebra k B ↦ by
      letI := a'
      exact IsResiduallyFiniteDimensional k Bᵐᵒᵖ → Module.Finite k B
    change test (hf.targetAlgebra k) at hm
    rw [ha] at hm
    exact hm ((residuallyFiniteDimensional_iff_opposite k B).1 hB)

end EFiniteCharacterizations
