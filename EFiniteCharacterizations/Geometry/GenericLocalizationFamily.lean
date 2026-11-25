module

public import EFiniteCharacterizations.RingEpimorphisms.GroundLocalization
public import EFiniteCharacterizations.Geometry.LocalizedMatrixAction
public import EFiniteCharacterizations.Algebra.RepresentationImage

/-! # The generic image of a ground localization -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace EFiniteCharacterizations.FieldExtension

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]

/-- A missing projective class yields a prime matrix image of one ground
localization. Its relations hold on infinitely many nonisomorphic geometric
modules of a single dimension. -/
theorem exists_generic_localization_family (hn : ¬ IsEFinite R) :
    let F := AlgebraicClosure k
    let A := ExtendedAlgebra k F R
    ∃ (P : TwoTerm R) (B : Type u) (_ : Ring B) (_ : Algebra k B) (f : R →ₐ[k] B),
      IsUniversalLocalization (fun _ : Unit ↦ P) f.toRingHom ∧
      ∃ (d : ℕ) (_ : 0 < d) (K : Type u) (_ : Field K) (q : B →+* Matrix (Fin d) (Fin d) K)
        (S : Set (Skeleton (FGModuleCat.{u} A))), S.Infinite ∧ Submodule.span K (Set.range q) = ⊤ ∧
        (∀ a b, q a ≠ 0 → q b ≠ 0 → ∃ z, q (a*z*b) ≠ 0) ∧
        ∀ x : S, ∃ (M : FGModuleCat.{u} A) (v : Module.Basis (Fin d) F (M.obj : Type u))
          (ρ : B →ₐ[k] Matrix (Fin d) (Fin d) F),
          toSkeleton M = x.val ∧ (∀ r, ρ (f r) = basedAction v (1 ⊗ₜ[k] r)) ∧
          Submodule.span F (Set.range ρ) = ⊤ ∧
          (letI := imageAlgebra (k := k) q
           ∃ π : q.range →ₐ[k] Matrix (Fin d) (Fin d) F, ∀ a, π (q.rangeRestrict a) = ρ a) := by
  classical
  let F := AlgebraicClosure k
  let A := ExtendedAlgebra k F R
  let := IsNoetherianRing.of_finite F A
  obtain ⟨P,θ,c,h⟩ := exists_infinite_fixed_class_extended_chart_of_not_isEFinite k hn
  let U := P.induce (algebraInclusion k F R).toRingHom
  let X := U.stableInvertingClasses F ∩ stableClassesOfClass θ c
  have : Infinite X := h.to_subtype
  obtain ⟨B,_,_,f,hf,G,hfin,hG⟩ := exists_finitely_generated_singleton_localization k P
  obtain ⟨C,_,_,g,hg'⟩ := exists_algebra_universalLocalization F (fun _ : PUnit.{u+1} ↦ U)
  have hg : IsUniversalLocalization (fun _ : Unit ↦ U) g.toRingHom :=
    ⟨fun _ ↦ hg'.inverts PUnit.unit,fun T _ p hp ↦ hg'.desc T p (fun _ ↦ hp ())⟩
  choose M hM hs hi using fun x : X ↦ x.property.1
  let d := (dimensionWeight (R := A) F c).toNat
  have hd (x : X) : Module.finrank F ((M x).obj : Type u) = d := by
    obtain ⟨N,hN,hc,_⟩ := x.property.2
    obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.1 ((hM x).trans hN.symm)
    have he := (GrothendieckGroup.of_eq_of_iso e).trans hc
    dsimp only [d]
    rw [← he]
    change _ = ((dimensionWeight (R := A) F).eval (M x)).toNat
    simp
  let _ (x : X) : Module.Finite F ((M x).obj : Type u) := Module.Finite.trans A _
  have hpos : 0 < d := by
    obtain ⟨x,hx⟩ := h.nonempty
    let y : X := ⟨x,hx⟩
    have : Nontrivial (M y) := not_subsingleton_iff_nontrivial.mp
      ((hs y).1 ∘ (FGModuleCat.isZero_iff_subsingleton _).2)
    exact hd y ▸ (Module.finrank_pos (R := F) (M := (M y).obj))
  let v (x : X) := (Module.finBasis F ((M x).obj : Type u)).reindex (finCongr (hd x))
  choose ρ hr hspan using fun x : X ↦
    exists_full_span_localized_action P f hf g hg (M x) (v x) (hs x) (hi x)
  obtain ⟨S,hS,K,_,q,hgeneric,hprime,hrel⟩ := exists_generic_prime_image (k := k) (F := F) (A := B) (n := Fin d) (X := X) G hfin hG ρ hspan
  refine ⟨P,B,inferInstance,inferInstance,f,hf,d,hpos,K,inferInstance,q,Subtype.val '' S,
    hS.image Subtype.val_injective.injOn,hgeneric,hprime,?_⟩
  rintro ⟨x,y,hy,rfl⟩
  exact ⟨M y,v y,ρ y,hM y,hr y,hspan y,
    exists_image_factor q (ρ y) (fun a b hab ↦ hrel a b hab y hy)⟩

end EFiniteCharacterizations.FieldExtension
