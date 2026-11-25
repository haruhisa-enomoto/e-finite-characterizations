module

public import EFiniteCharacterizations.RingEpimorphisms.LocalizationExtensions
public import Mathlib.Algebra.FreeAlgebra

/-! # Simultaneous commutators over division ring localizations of free algebras -/

@[expose] public section

open CategoryTheory

universe u
namespace EFiniteCharacterizations

/-- A division ring obtained by universally inverting projective maps over a
free algebra solves the simultaneous commutator equations for its generators. -/
theorem simultaneous_commutators_of_division_localization {k D ι : Type u}
    [Field k] [DivisionRing D] [Algebra k D] (g : FreeAlgebra k ι →ₐ[k] D)
    {κ : Type*} {φ : κ → TwoTerm (FreeAlgebra k ι)} (loc : IsUniversalLocalization φ g.toRingHom)
    (b : ι → Module.End k D) :
    ∃ T : Module.End k D, ∀ i x,
      b i x = T (g (FreeAlgebra.ι k i) * x) - g (FreeAlgebra.ι k i) * T x := by
  let R := FreeAlgebra k ι
  let a i := g (FreeAlgebra.ι k i)
  let mat (i : ι) : Module.End k (D × D) :=
    (((LinearMap.mulLeft k (a i)).comp (LinearMap.fst k D D) +
      (b i).comp (LinearMap.snd k D D))).prod ((LinearMap.mulLeft k (a i)).comp (LinearMap.snd k D D))
  let ρ := FreeAlgebra.lift k mat
  have compat (r : R) :
      (∀ x : D, ρ r (x,0) = (g r * x,0)) ∧
      (∀ z : D × D, (ρ r z).2 = g r * z.2) := by
    induction r using FreeAlgebra.induction with
    | grade0 c =>
      rw [ρ.commutes,g.commutes]
      constructor <;> intro x <;> simp [Algebra.smul_def]
    | grade1 i =>
      rw [show ρ (FreeAlgebra.ι k i) = mat i from FreeAlgebra.lift_ι_apply ..]
      constructor <;> intro x <;> simp [mat,a]
    | mul r s hr hs =>
      simp only [map_mul,Module.End.mul_apply]
      exact ⟨fun x ↦ by rw [hs.1,hr.1,mul_assoc],fun x ↦ by rw [hr.2,hs.2,mul_assoc]⟩
    | add r s hr hs =>
      simp only [map_add,LinearMap.add_apply]
      exact ⟨fun x ↦ by simp [hr.1,hs.1,add_mul,Prod.mk_add_mk],
        fun x ↦ by simp [hr.2,hs.2,add_mul]⟩
  let : Module R D := Module.compHom D g.toRingHom
  let : Module R (D × D) := Module.compHom (D × D) ρ.toRingHom
  let A := ModuleCat.of R D
  let V := ModuleCat.of R (D × D)
  let j : A ⟶ V := ModuleCat.ofHom
    { toFun := fun x ↦ (x,0)
      map_add' := by simp
      map_smul' := fun r x ↦ (compat r).1 x |>.symm }
  let q : V ⟶ A := ModuleCat.ofHom
    { toFun := Prod.snd
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ (compat r).2 x }
  let S := ShortComplex.mk j q (by ext; rfl)
  have hs : S.ShortExact := ShortComplex.ShortExact.mk'
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 (fun z ↦ by
      change z.2 = 0 ↔ ∃ x : D, (x,0) = z
      exact ⟨fun hz ↦ ⟨z.1,Prod.ext rfl hz.symm⟩,by rintro ⟨x, rfl⟩; rfl⟩))
    ((ModuleCat.mono_iff_injective j).2 (fun _ _ he ↦ congrArg Prod.fst he))
    ((ModuleCat.epi_iff_surjective q).2 (fun x ↦ ⟨(0,x),rfl⟩))
  have hi (i : κ) : (φ i).InvertedOn A :=
    ((φ i).invertedOn_induce_iff g.toRingHom (ModuleCat.of D D)).1
      (((φ i).induce g.toRingHom).isIso_iff_invertedOn_all.mp (loc.inverts i) (ModuleCat.of D D))
  obtain ⟨s,hsq⟩ := loc.splits_over_divisionRing S hs hi hi
  let T : Module.End k D :=
    { toFun := fun x ↦ (s.hom x).1
      map_add' := fun x y ↦ congrArg Prod.fst (s.hom.map_add x y)
      map_smul' := fun c x ↦ by
        have h := s.hom.map_smul (algebraMap k R c) x
        change s.hom (g (algebraMap k R c) * x) = ρ (algebraMap k R c) (s.hom x) at h
        rw [g.commutes,ρ.commutes,← Algebra.smul_def] at h
        exact congrArg Prod.fst h }
  refine ⟨T,fun i x ↦ ?_⟩
  have hh := s.hom.map_smul (FreeAlgebra.ι k i) x
  change s.hom (a i * x) = ρ (FreeAlgebra.ι k i) (s.hom x) at hh
  rw [show ρ (FreeAlgebra.ι k i) = mat i from FreeAlgebra.lift_ι_apply ..] at hh
  have hz : (s.hom x).2 = x := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hsq) x
  have he := congrArg Prod.fst hh
  change T (a i * x) = a i * T x + b i (s.hom x).2 at he
  rw [hz] at he
  change b i x = T (a i * x) - a i * T x
  rw [he]
  abel

end EFiniteCharacterizations
