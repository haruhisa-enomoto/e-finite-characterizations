module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Trace

/-! # Full matrix action on a geometric simple module -/

@[expose] public section

namespace EFiniteCharacterizations

variable {F B M : Type*} [Field F] [IsAlgClosed F] [Ring B] [Algebra F B]
  [AddCommGroup M] [Module B M] [Module F M] [IsScalarTower F B M]
  [Module.Finite F M] [IsSimpleModule B M]

/-- Each endomorphism of a finite-dimensional simple module over an
algebraically closed field is scalar. -/
theorem simple_end_eq_scalar (f : Module.End B M) : ∃ c : F, ∀ x, f x = c • x := by
  let := IsSimpleModule.nontrivial B M
  let fF := f.restrictScalars F
  obtain ⟨c,hc⟩ := Module.End.exists_eigenvalue fF
  obtain ⟨v,hv⟩ := hc.exists_hasEigenvector
  let g : Module.End B M :=
    { toFun := fun x ↦ c • x
      map_add' := smul_add c
      map_smul' := fun b x ↦ smul_comm c b x }
  have hz : (f - g) v = 0 := sub_eq_zero.mpr hv.apply_eq_smul
  have he : f - g = 0 := by
    by_contra hn
    have hi := LinearMap.injective_of_ne_zero hn
    exact hv.2 (hi (hz.trans ((f - g).map_zero).symm))
  exact ⟨c,fun x ↦ LinearMap.congr_fun (sub_eq_zero.mp he) x⟩

/-- Density makes the action onto the full endomorphism algebra of a
finite-dimensional simple module over an algebraically closed field. -/
theorem simple_action_surjective :
    Function.Surjective (Algebra.lsmul F F M : B →ₐ[F] Module.End F M) := by
  classical
  intro f
  have hf (q : Module.End B M) (x : M) : f (q x) = q (f x) := by
    obtain ⟨c,hc⟩ := simple_end_eq_scalar (F := F) q
    rw [hc, hc, map_smul]
  let g : Module.End (Module.End B M) M :=
    { f.toAddHom with map_smul' := hf }
  let b := Module.finBasis F M
  obtain ⟨r,hr⟩ := jacobson_density g (Finset.univ.image b)
  refine ⟨r,?_⟩
  apply b.ext
  intro i
  exact (hr (b i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)).symm

variable {N : Type*} [AddCommGroup N] [Module B N] [Module F N]
    [IsScalarTower F B N] [Module.Finite F N] [IsSimpleModule B N]

/-- A single algebra element can prescribe independent linear actions on
two nonisomorphic finite-dimensional simple modules. -/
theorem simple_pair_action_surjective (hne : IsEmpty (M ≃ₗ[B] N))
    (f : Module.End F M) (g : Module.End F N) :
    ∃ r : B, (∀ x : M, r • x = f x) ∧ (∀ y : N, r • y = g y) := by
  classical
  let L := LinearMap.inl B M N
  let K := LinearMap.inr B M N
  let : IsSemisimpleModule B (M × N) := by
    have htop : L.range ⊔ K.range = ⊤ := by
      apply top_unique
      rintro ⟨x,y⟩ _
      exact Submodule.mem_sup.mpr ⟨L x,⟨x,rfl⟩,K y,⟨y,rfl⟩,by simp [L,K]⟩
    have hs := IsSemisimpleModule.sup (IsSemisimpleModule.range L) (IsSemisimpleModule.range K)
    rw [htop] at hs
    exact Submodule.topEquiv.isSemisimpleModule_iff.mp hs
  let H := f.prodMap g
  have comm (q : Module.End B (M × N)) (z : M × N) : H (q z) = q (H z) := by
    let π := LinearMap.fst B M N
    let σ := LinearMap.snd B M N
    have h₁ : (π.comp q).comp K = 0 := by
      by_contra h
      exact hne.false (LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero h)).symm
    have h₂ : (σ.comp q).comp L = 0 := by
      by_contra h
      exact hne.false (LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero h))
    obtain ⟨c,hc⟩ := simple_end_eq_scalar (F := F) ((π.comp q).comp L)
    obtain ⟨a,ha⟩ := simple_end_eq_scalar (F := F) ((σ.comp q).comp K)
    have hq (x : M) (y : N) : q (x,y) = (c • x,a • y) := by
      rw [show (x,y) = L x + K y by simp [L,K],map_add]
      apply Prod.ext
      · exact (congrArg₂ (· + ·) (hc x) (LinearMap.congr_fun h₁ y)).trans (add_zero _)
      · exact (congrArg₂ (· + ·) (LinearMap.congr_fun h₂ x) (ha y)).trans (zero_add _)
    rcases z with ⟨x,y⟩
    change (f (q (x,y)).1,g (q (x,y)).2) = q (f x,g y)
    simp [hq]
  let h : Module.End (Module.End B (M × N)) (M × N) :=
    { H.toAddHom with map_smul' := comm }
  let v := Module.finBasis F (M × N)
  obtain ⟨r,hr⟩ := jacobson_density h (Finset.univ.image v)
  have he : Algebra.lsmul F F (M × N) r = H := v.ext fun i ↦
    (hr (v i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)).symm
  exact ⟨r, fun x ↦ congrArg Prod.fst (LinearMap.congr_fun he (x,0)),
    fun y ↦ congrArg Prod.snd (LinearMap.congr_fun he (0,y))⟩

/-- Traces of algebra elements distinguish nonisomorphic geometric simple
modules, including in positive characteristic. -/
theorem exists_distinct_simple_traces (hne : IsEmpty (M ≃ₗ[B] N)) :
    ∃ r : B, LinearMap.trace F M (Algebra.lsmul F F M r) = 1 ∧
      LinearMap.trace F N (Algebra.lsmul F F N r) = 0 := by
  classical
  let := IsSimpleModule.nontrivial B M
  let v := Module.finBasis F M
  let i : Fin (Module.finrank F M) := ⟨0,Module.finrank_pos⟩
  let f := (LinearMap.toMatrixAlgEquiv v).symm (Matrix.single i i 1)
  obtain ⟨r,hr,hs⟩ := simple_pair_action_surjective hne f 0
  have he : Algebra.lsmul F F M r = f := LinearMap.ext hr
  have hz : Algebra.lsmul F F N r = 0 := LinearMap.ext hs
  refine ⟨r,?_,by simp [hz]⟩
  rw [he,LinearMap.trace_eq_matrix_trace F v]
  change Matrix.trace ((LinearMap.toMatrixAlgEquiv v) f) = 1
  simp [f,Matrix.trace,Matrix.single]

end EFiniteCharacterizations
