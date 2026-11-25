module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Artinian.Module

/-! # Inverting an endomorphism on a module of finite length -/

@[expose] public section

namespace EFiniteCharacterizations

universe u v

variable {R : Type*} {M : Type u} {N : Type v} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- When kernel and image are complementary, inverting an endomorphism by
precomposition amounts to killing all maps out of its kernel. -/
theorem bijective_precomp_iff_of_isCompl (a : Module.End R M)
    (h : IsCompl (LinearMap.ker a) (LinearMap.range a)) :
    Function.Bijective (fun f : M →ₗ[R] N ↦ f.comp a) ↔
      Subsingleton (LinearMap.ker a →ₗ[R] N) := by
  let K := LinearMap.ker a
  let I := LinearMap.range a
  let p := K.projectionOnto I h
  let q := I.projectionOnto K h.symm
  constructor
  · intro hb
    suffices ∀ g : K →ₗ[R] N, g = 0 from ⟨fun g g' ↦ (this g).trans (this g').symm⟩
    intro g
    obtain ⟨f, hf⟩ := hb.2 (g.comp p)
    ext x
    have he := LinearMap.congr_fun hf (x : M)
    simpa [p, LinearMap.mem_ker.mp x.property] using he.symm
  · intro hK
    have vanishes (f : M →ₗ[R] N) (x : K) : f x = 0 :=
      LinearMap.congr_fun (hK.elim (f.comp K.subtype) 0) x
    constructor
    · intro f g he
      ext x
      obtain ⟨v, hv, w, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.mp
        (show x ∈ K ⊔ I by rw [h.sup_eq_top]; trivial)
      simp only [map_add, vanishes f ⟨v,hv⟩, vanishes g ⟨v,hv⟩]
      rw [show f (a y) = g (a y) from LinearMap.congr_fun he y]
    · intro f
      let l := K.liftQ f (fun x hx ↦ vanishes f ⟨x,hx⟩)
      let e := a.quotKerEquivRange
      refine ⟨(l.comp e.symm.toLinearMap).comp q, ?_⟩
      ext x
      change l (e.symm (q (a x))) = f x
      have hq : q (a x) = a.rangeRestrict x :=
        I.projectionOnto_apply_left h.symm (a.rangeRestrict x)
      rw [hq, show a.rangeRestrict x = e (K.mkQ x) from rfl, e.symm_apply_apply]
      rfl

/-- A single Fitting summand works simultaneously for all target modules. -/
theorem exists_fitting_inversion [IsArtinian R M] [IsNoetherian R M] (a : Module.End R M) :
    ∃ n > 0, IsCompl (LinearMap.ker (a ^ n)) (LinearMap.range (a ^ n)) ∧
      ∀ (N : Type*) [AddCommGroup N] [Module R N],
        Function.Bijective (fun f : M →ₗ[R] N ↦ f.comp a) ↔
          Subsingleton (LinearMap.ker (a ^ n) →ₗ[R] N) := by
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp a.eventually_isCompl_ker_pow_range_pow
  refine ⟨m+1, Nat.succ_pos _, hm _ (Nat.le_succ _), ?_⟩
  intro N _ _
  let T := fun f : M →ₗ[R] N ↦ f.comp a
  have iter (n : ℕ) (f : M →ₗ[R] N) : T^[n] f = f.comp (a ^ n) := by
    induction n generalizing f with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply, ih, pow_succ', Module.End.mul_eq_comp]
      rfl
  rw [← bijective_precomp_iff_of_isCompl _ (hm _ (Nat.le_succ _)),
    ← funext (iter (m+1))]
  exact ⟨fun hb ↦ hb.iterate _, fun hb ↦
    ⟨(Function.iterate_succ T m ▸ hb.1 : Function.Injective (T^[m] ∘ T)).of_comp,
     (Function.iterate_succ' T m ▸ hb.2 : Function.Surjective (T ∘ T^[m])).of_comp⟩⟩

/-- The two-sided trace ideal of a left module. -/
def moduleTraceIdeal (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] : TwoSidedIdeal R :=
  TwoSidedIdeal.span {r | ∃ (φ : M →ₗ[R] R) (x : M), φ x = r}

/-- The trace ideal of a projective module cuts out exactly the modules
receiving no nonzero homomorphism from it. -/
theorem subsingleton_hom_iff_trace_le [Module.Projective R M] :
    Subsingleton (M →ₗ[R] N) ↔
      moduleTraceIdeal R M ≤ (Module.annihilator R N).toTwoSided := by
  rw [moduleTraceIdeal, TwoSidedIdeal.span_le]
  constructor
  · intro h r hr
    obtain ⟨φ, x, hx⟩ := hr
    subst r
    apply Ideal.mem_toTwoSided.mpr
    apply Module.mem_annihilator.mpr
    intro y
    exact LinearMap.congr_fun (h.elim ((LinearMap.toSpanSingleton R N y).comp φ) 0) x
  · intro h
    obtain ⟨s, hs⟩ := (inferInstance : Module.Projective R M).out
    have vanish (f : M →ₗ[R] N) (x : M) : f x = 0 := by
      calc
        f x = f (Finsupp.linearCombination R id (s x)) := congrArg f (hs x).symm
        _ = 0 := by
          rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
          apply Finset.sum_eq_zero
          intro i _
          rw [map_smul]
          exact Module.mem_annihilator.mp (Ideal.mem_toTwoSided.mp
            (h ⟨(Finsupp.lapply i).comp s, x, rfl⟩)) _
    exact ⟨fun f g ↦ LinearMap.ext fun x ↦ (vanish f x).trans (vanish g x).symm⟩

/-- Inverting a noninvertible endomorphism of a projective module of finite
length on arbitrary targets cuts out the modules over one proper quotient. -/
theorem exists_nonzero_ideal_of_endomorphism [Module.Projective R M]
    [IsArtinian R M] [IsNoetherian R M] (a : Module.End R M) (ha : ¬ Function.Bijective a) :
    ∃ I : TwoSidedIdeal R,
      (∃ (S : Type u) (_ : AddCommGroup S) (_ : Module R S),
        IsSimpleModule R S ∧ ¬ I ≤ (Module.annihilator R S).toTwoSided) ∧
      ∀ (N : Type*) [AddCommGroup N] [Module R N],
      Function.Bijective (fun f : M →ₗ[R] N ↦ f.comp a) ↔
        I ≤ (Module.annihilator R N).toTwoSided := by
  obtain ⟨n, hn, hc, h⟩ := exists_fitting_inversion a
  let K := LinearMap.ker (a ^ n)
  have : Module.Projective R K := Module.Projective.of_split K.subtype
    (K.projectionOnto _ hc) (K.projectionOnto_comp_subtype hc)
  refine ⟨moduleTraceIdeal R K, ?_, fun N _ _ ↦ (h N).trans subsingleton_hom_iff_trace_le⟩
  have hK : Nontrivial K := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hzero
    have hk : K = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      exact congrArg Subtype.val (hzero.elim (⟨x,hx⟩ : K) 0)
    have hi := LinearMap.ker_eq_bot.mp hk
    have hs : Function.Surjective (a ^ n) := LinearMap.range_eq_top.mp (by
      have he := hc.sup_eq_top
      change K ⊔ _ = ⊤ at he
      simpa [hk] using he)
    exact ha ⟨Module.End.injective_of_iterate_injective hn.ne' hi,
      Module.End.surjective_of_iterate_surjective hn.ne' hs⟩
  obtain ⟨L, hL⟩ := IsCoatomic.exists_coatom (α := Submodule R K)
  let S := K ⧸ L
  have hs : IsSimpleModule R S := isSimpleModule_iff_isCoatom.mpr hL
  refine ⟨S, inferInstance, inferInstance, hs, ?_⟩
  intro hi
  have hz : L.mkQ = 0 := (subsingleton_hom_iff_trace_le.mpr hi).elim _ _
  exact hL.ne_top (top_le_iff.mp (fun x _ ↦ by
    have hx := LinearMap.congr_fun hz x
    exact (Submodule.Quotient.mk_eq_zero L).mp hx))

/-- Ring maps whose restricted modules invert the endomorphism factor uniquely
through the Fitting trace quotient. One simple module of the original ring
is excluded. -/
theorem exists_quotient_inverting_endomorphism [Module.Projective R M]
    [IsArtinian R M] [IsNoetherian R M] (a : Module.End R M) (ha : ¬ Function.Bijective a) :
    ∃ I : TwoSidedIdeal R,
      (∃ (S : Type u) (_ : AddCommGroup S) (_ : Module R S),
        IsSimpleModule R S ∧ ¬ I ≤ (Module.annihilator R S).toTwoSided) ∧
      ∀ (T : Type v) [Ring T] (g : R →+* T),
        (∀ (N : Type v) [AddCommGroup N] [Module T N],
          letI := Module.compHom N g
          Function.Bijective (fun f : M →ₗ[R] N ↦ f.comp a)) ↔
        ∃! q : R ⧸ I.asIdeal →+* T, q.comp (Ideal.Quotient.mk I.asIdeal) = g := by
  obtain ⟨I, hS, hI⟩ := exists_nonzero_ideal_of_endomorphism a ha
  refine ⟨I, hS, fun T _ g ↦ ?_⟩
  constructor
  · intro h
    let := Module.compHom T g
    have hker (r : R) (hr : r ∈ I.asIdeal) : g r = 0 := by
      have hr' := Ideal.mem_toTwoSided.mp ((hI T).mp (h T) hr)
      have hz := Module.mem_annihilator.mp hr' (1 : T)
      change g r * 1 = 0 at hz
      simpa using hz
    refine ⟨Ideal.Quotient.lift I.asIdeal g hker, rfl, fun q hq ↦ ?_⟩
    exact Ideal.Quotient.ringHom_ext hq
  · rintro ⟨q, rfl, _⟩ N _ _
    let := Module.compHom N (q.comp (Ideal.Quotient.mk I.asIdeal))
    apply (hI N).mpr
    intro r hr
    apply Ideal.mem_toTwoSided.mpr
    apply Module.mem_annihilator.mpr
    intro y
    change q (Ideal.Quotient.mk I.asIdeal r) • y = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero, zero_smul]

end EFiniteCharacterizations
