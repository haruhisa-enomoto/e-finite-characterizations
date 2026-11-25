module

public import EFiniteCharacterizations.RingEpimorphisms.RingEpimorphism
public import EFiniteCharacterizations.Modules.Endolength
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import Mathlib.RingTheory.SimpleRing.Matrix

/-! # Generic bricks and simple Artinian epic targets -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]

/-- An infinite-dimensional brick of finite dimension over its division ring
of endomorphisms. -/
structure IsGenericBrick (M : ModuleCat.{u} R) : Prop where
  infinite : ¬ Module.Finite k M
  invertible : ∀ p : Module.End R M, p ≠ 0 → Function.Bijective p
  endofinite : Module.Finite (Module.End R M) M

/-- In a finite direct-sum decomposition of the regular module, the
coordinates of one generate the summand over its endomorphisms, even after
restriction of scalars. -/
private theorem finite_over_restricted_end {B : Type u} [Ring B] (f : R →+* B)
    (S : ModuleCat.{u} B) {n : ℕ} (e : B ≃ₗ[B] (Fin n → S)) :
    let M := (ModuleCat.restrictScalars f).obj S
    Module.Finite (Module.End R M) M := by
  classical
  let M := (ModuleCat.restrictScalars f).obj S
  let D := Module.End R M
  let v : Fin n → M := e 1
  let V := Submodule.span D (Set.range v)
  have ht : V = ⊤ := by
    apply top_unique
    intro x _
    let eval : B →ₗ[B] S := LinearMap.toSpanSingleton B S x
    let a (i : Fin n) : S →ₗ[B] S := (eval.comp e.symm.toLinearMap).comp (LinearMap.single B (fun _ : Fin n ↦ S) i)
    let t (i : Fin n) : D :=
      ((ModuleCat.restrictScalars f).map (ModuleCat.ofHom (a i))).hom
    have hx : ∑ i, t i • v i = x := by
      change ∑ i, (eval.comp e.symm.toLinearMap) (Pi.single i ((e 1) i)) = x
      rw [← map_sum,Finset.univ_sum_single]
      change eval (e.symm (e 1)) = x
      rw [e.symm_apply_apply]
      exact LinearMap.toSpanSingleton_apply_one _ _ _
    rw [← hx]
    exact V.sum_mem fun i _ ↦ V.smul_mem _ (Submodule.subset_span ⟨i,rfl⟩)
  apply Module.Finite.of_fg_top
  rw [← ht]
  exact Submodule.fg_span (Set.finite_range v)

/-- Restriction of a simple module from an infinite-dimensional simple
Artinian epic algebra gives a generic brick. -/
theorem exists_genericBrick_of_simpleArtinian_epi {B : Type u} [Ring B] [Algebra k B]
    [IsArtinianRing B] [IsSimpleRing B] (f : R →ₐ[k] B) (hf : IsRingEpimorphism f.toRingHom)
    (hB : ¬ Module.Finite k B) : ∃ M : ModuleCat.{u} R, IsGenericBrick k M := by
  classical
  obtain ⟨n,_,I,hI,⟨e⟩⟩ := (IsSimpleRing.isIsotypic B B).linearEquiv_fun
  let S := ModuleCat.of B I
  let M := (ModuleCat.restrictScalars f.toRingHom).obj S
  refine ⟨M,⟨?_,?_,finite_over_restricted_end f.toRingHom S e⟩⟩
  · intro hm
    let ψ : B ≃ₗ[k] (Fin n → M) :=
      { toEquiv := e.toEquiv
        map_add' := e.map_add
        map_smul' := fun c x ↦ by
          funext i
          rw [Algebra.smul_def]
          change e ((algebraMap k B c) * x) i = (f (algebraMap k R c) • (e x i) : I)
          rw [f.commutes, ← smul_eq_mul, e.map_smul]
          rfl }
    exact hB (Module.Finite.equiv ψ.symm)
  · intro p hp
    let q : I →ₗ[B] I :=
      { toFun := p
        map_add' := p.map_add
        map_smul' := hf.map_smul (M := I) (N := I) p }
    have hq : q ≠ 0 := fun h ↦ hp (LinearMap.ext fun x ↦ LinearMap.congr_fun h x)
    exact (LinearMap.bijective_of_ne_zero (f := q) hq : Function.Bijective q)

private theorem simpleArtinian_copies {B : Type u} [Ring B] [IsSimpleRing B] [IsArtinianRing B]
    (S X : Type u) [AddCommGroup S] [Module B S] [IsSimpleModule B S]
    [AddCommGroup X] [Module B X] : ∃ ι : Type u, Nonempty (X ≃ₗ[B] ι →₀ S) := by
  apply IsIsotypicOfType.linearEquiv_finsupp
  intro m hm
  obtain ⟨I,⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule B S
  obtain ⟨J,⟨e'⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule B m
  have := IsSimpleModule.congr e.symm
  have := IsSimpleModule.congr e'.symm
  exact ⟨e'.trans (((IsSimpleRing.isIsotypic B B) I J).some.trans e.symm)⟩

/-- For a simple Artinian target, restriction is full as soon as it preserves
the endomorphisms of one simple module. -/
theorem isRingEpimorphism_of_simple_end {B : Type u} [Ring B] [IsSimpleRing B] [IsArtinianRing B]
    (f : R →+* B) (S : Type u) [AddCommGroup S] [Module B S] [IsSimpleModule B S]
    (hs : letI := Module.compHom S f
          ∀ (l : Module.End R S) (b : B) (x : S), l (b • x) = b • l x) :
    IsRingEpimorphism f := by
  classical
  apply isRingEpimorphism_of_map_smul
  intro X Y _ _ _ _
  obtain ⟨ι,⟨e⟩⟩ := simpleArtinian_copies (B := B) S X
  obtain ⟨κ,⟨d⟩⟩ := simpleArtinian_copies (B := B) S Y
  let := Module.compHom X f
  let := Module.compHom Y f
  let := Module.compHom S f
  intro p b x
  let u (i : ι) : S →ₗ[B] X := e.symm.toLinearMap.comp (Finsupp.lsingle i)
  let v (j : κ) : Y →ₗ[B] S := (Finsupp.lapply j).comp d.toLinearMap
  have hu (i : ι) (s : S) : p (b • u i s) = b • p (u i s) := by
    apply d.injective
    ext j
    let c : Module.End R S :=
      { toFun := fun z ↦ v j (p (u i z))
        map_add' := fun _ _ ↦ by simp
        map_smul' := fun r z ↦ by
          change v j (p (u i (f r • z))) = f r • v j (p (u i z))
          rw [(u i).map_smul, show p (f r • u i z) = f r • p (u i z) from p.map_smul r _,(v j).map_smul] }
    change v j (p (b • u i s)) = v j (b • p (u i s))
    rw [← (u i).map_smul,(v j).map_smul]
    exact hs c b s
  have hall (w : ι →₀ S) : p (b • e.symm w) = b • p (e.symm w) := by
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add w w' hw hw' => simp [smul_add,hw,hw']
    | single i s => exact hu i s
  simpa using hall (e x)

/-- The endomorphism ring of a generic brick, with inverse given by the
inverse linear equivalence. -/
@[instance_reducible] noncomputable def IsGenericBrick.divisionRing {M : ModuleCat.{u} R}
    (h : IsGenericBrick k M) : DivisionRing (Module.End R M) := by
  classical
  have : Nontrivial M := not_subsingleton_iff_nontrivial.mp (fun _ ↦ h.infinite inferInstance)
  exact
    { (inferInstance : Ring (Module.End R M)) with
      inv := fun a ↦ if ha : a = 0 then 0 else (LinearEquiv.ofBijective a (h.invertible a ha)).symm.toLinearMap
      exists_pair_ne := ⟨0,1,zero_ne_one⟩
      mul_inv_cancel := fun a ha ↦ by
        simp only [dite_eq_right ha]
        exact LinearMap.ext (LinearEquiv.ofBijective a (h.invertible a ha)).right_inv
      inv_zero := dite_eq_left rfl
      nnqsmul := _, nnqsmul_def := fun _ _ ↦ rfl
      qsmul := _, qsmul_def := fun _ _ ↦ rfl }

private theorem simple_end_of_finite (D V : Type u) [DivisionRing D] [AddCommGroup V]
    [Module D V] [Module.Finite D V] [Nontrivial V] : IsSimpleRing (Module.End D V) := by
  classical
  let n := Module.finrank D V
  let b := Module.finBasis D V
  have : NeZero n := ⟨(Module.finrank_pos (R := D) (M := V)).ne'⟩
  let e := b.equivFun.conjRingEquiv.trans (endVecRingEquivMatrixEnd (Fin n) D D)
  apply (IsSimpleRing.iff_injective_ringHom _).2
  intro T _ _ f
  have hi := (f.comp e.symm.toRingHom).injective
  exact fun x y h ↦ e.injective (hi (show f (e.symm (e x)) = f (e.symm (e y)) by simpa using h))

/-- A generic brick yields an infinite-dimensional simple Artinian epic
target by the action on its vector space over the division endomorphism ring. -/
theorem exists_simpleArtinian_epi_of_genericBrick {M : ModuleCat.{u} R} (h : IsGenericBrick k M) :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra k B) (_ : IsSimpleRing B) (_ : IsArtinianRing B)
      (f : R →ₐ[k] B), IsRingEpimorphism f.toRingHom ∧ ¬ Module.Finite k B := by
  classical
  let D := Module.End R M
  let : DivisionRing D := h.divisionRing k
  have : Module.Finite D M := h.endofinite
  have : Nontrivial M := not_subsingleton_iff_nontrivial.mp (fun _ ↦ h.infinite inferInstance)
  let B := Module.End D M
  let : IsSimpleRing B := simple_end_of_finite D M
  let : IsSemisimpleRing B := IsSemisimpleRing.moduleEnd D M
  let ρ : R →ₐ[k] B :=
    { __ := Module.toModuleEnd D (S := R) M
      commutes' := fun c ↦ LinearMap.ext fun x ↦ algebraMap_smul R c x }
  refine ⟨B,inferInstance,inferInstance,inferInstance,inferInstance,ρ,?_,?_⟩
  · apply isRingEpimorphism_of_simple_end ρ.toRingHom M
    intro l b x
    exact (b.map_smul (l : D) x).symm
  · intro hfin
    obtain ⟨x,hx⟩ := exists_ne (0 : M)
    have hs := (isSimpleModule_iff_toSpanSingleton_surjective (R := B) (M := M)).mp inferInstance
    let ev : B →ₗ[k] M :=
      { toFun := fun b ↦ b x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    exact h.infinite (Module.Finite.of_surjective ev (hs.2 x hx))

/-- The simple Artinian ring-epimorphism condition. -/
def SimpleArtinianEpicTargetsFinite (R : Type u) [Ring R] [Algebra k R] : Prop :=
  ∀ (B : Type u) [Ring B] [Algebra k B] [IsSimpleRing B] [IsArtinianRing B]
    (f : R →ₐ[k] B), IsRingEpimorphism f.toRingHom → Module.Finite k B

/-- The large-module and ring-epimorphism conditions in the paper's
right-module convention. -/
theorem no_generic_right_brick_iff_simpleArtinianEpicTargetsFinite :
    (¬ ∃ M : ModuleCat.{u} Rᵐᵒᵖ, IsGenericBrick k M) ↔ SimpleArtinianEpicTargetsFinite k R := by
  constructor
  · intro hn B _ _ _ _ f hf
    by_contra hB
    apply hn
    apply exists_genericBrick_of_simpleArtinian_epi k (AlgHom.op f) hf.op
    intro h
    exact hB (Module.Finite.equiv (MulOpposite.opLinearEquiv k).symm)
  · rintro h ⟨M,hM⟩
    obtain ⟨B,_,_,_,_,f,hf,hB⟩ := exists_simpleArtinian_epi_of_genericBrick k hM
    let g := (AlgHom.op f).comp (AlgEquiv.opOp k R).toAlgHom
    have hg : IsRingEpimorphism g.toRingHom := by
      intro T _ a b hab
      apply hf.op T a b
      exact RingHom.ext fun x ↦ DFunLike.congr_fun hab x.unop.unop
    have := h Bᵐᵒᵖ g hg
    exact hB (Module.Finite.equiv (MulOpposite.opLinearEquiv k).symm)

/-- The criterion for arbitrary ring maps, with the target field action
induced by the epimorphism. -/
theorem no_generic_right_brick_iff_finite_ring_epimorphisms :
    (¬ ∃ M : ModuleCat.{u} Rᵐᵒᵖ, IsGenericBrick k M) ↔
      ∀ (B : Type u) [Ring B] [IsSimpleRing B] [IsArtinianRing B] (f : R →+* B)
        (hf : IsRingEpimorphism f), letI := hf.targetAlgebra k; Module.Finite k B := by
  rw [no_generic_right_brick_iff_simpleArtinianEpicTargetsFinite]
  constructor
  · intro h B _ _ _ f hf
    let := hf.targetAlgebra k
    let g : R →ₐ[k] B := { __ := f, commutes' := fun _ ↦ rfl }
    exact h B g hf
  · intro h B _ a _ _ f hf
    have ha : hf.targetAlgebra k = a := Algebra.algebra_ext _ _ fun r ↦ f.commutes r
    have hm := h B f.toRingHom hf
    change @Module.Finite k B _ _ (hf.targetAlgebra k).toModule at hm
    rwa [ha] at hm

end EFiniteCharacterizations
