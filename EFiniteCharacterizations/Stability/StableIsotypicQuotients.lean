module

public import EFiniteCharacterizations.ScalarExtension.FieldWitnessFibres
public import EFiniteCharacterizations.Stability.SemistablePowers

/-! # Restriction of a stable module over a finite extension -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations
variable {R : Type u} [Ring R] [IsNoetherianRing R]

private noncomputable def powerSuccIso (S : FGModuleCat.{u} R) (n : ℕ) :
    S ⊞ FGModuleCat.of R (Fin n → S) ≅ FGModuleCat.of R (Fin (n+1) → S) := by
  let T := FGModuleCat.of R (Fin n → S)
  let F := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  let e : S ⊞ T ≅ FGModuleCat.of R (S × (Fin n → S)) :=
    F.preimageIso ((FGModuleCat.forgetBiprodIso S T).trans (ModuleCat.biprodIsoProd S.obj T.obj))
  exact e.trans (Fin.consLinearEquiv R (fun _ : Fin (n+1) ↦ (S : Type u))).toFGModuleCatIso

/-- A semistable quotient of a finite power of a stable object is itself
a power of that object, and the quotient map splits. -/
theorem Weight.IsStable.split_quotient_of_power {θ : Weight (FGModuleCat.{u} R)}
    {S : FGModuleCat.{u} R} (hS : θ.IsStable S) (n : ℕ) {N : FGModuleCat.{u} R}
    (hN : θ.IsSemistable N) (f : FGModuleCat.of R (Fin n → S) ⟶ N) [Epi f] :
    (∃ m ≤ n, Nonempty (N ≅ FGModuleCat.of R (Fin m → S))) ∧ ∃ t, t ≫ f = 𝟙 N := by
  classical
  induction n generalizing N with
  | zero =>
    have hz := (FGModuleCat.isZero_iff_subsingleton (FGModuleCat.of R (Fin 0 → S))).2
      (inferInstanceAs (Subsingleton (Fin 0 → S)))
    have hn : IsZero N := (IsZero.iff_id_eq_zero _).2 ((cancel_epi f).1 (hz.eq_of_src _ _))
    exact ⟨⟨0,le_rfl,⟨hn.iso hz⟩⟩,0,hn.eq_of_tgt _ _⟩
  | succ n ih =>
    let U := FGModuleCat.of R (Fin n → S)
    let e := powerSuccIso S n
    let d : S ⊞ U ⟶ N := e.hom ≫ f
    let a := (biprod.inl : S ⟶ S ⊞ U) ≫ d
    let b := (biprod.inr : U ⟶ S ⊞ U) ≫ d
    have hd : Epi d := epi_comp e.hom f
    have decomp : biprod.desc a b = d := biprod.hom_ext' _ _ (by simp [a]) (by simp [b])
    by_cases ha : a = 0
    · have eq : (biprod.snd : S ⊞ U ⟶ U) ≫ b = d :=
        biprod.hom_ext' _ _ (by simpa using ha.symm) (by simp [b])
      let _ : Epi b := epi_of_epi_fac eq
      obtain ⟨⟨m,hm,hiso⟩,s,hs⟩ := ih hN b
      exact ⟨⟨m,hm.trans (Nat.le_succ _),hiso⟩,s ≫ biprod.inr ≫ e.hom,by simpa [b,d] using hs⟩
    · let _ := Weight.mono_of_isStable_of_isSemistable hS hN a ha
      let π := cokernel.π a
      have hQ := hS.isSemistable.cokernel_of_mono hN a
      have heq : (biprod.snd : S ⊞ U ⟶ U) ≫ b ≫ π = d ≫ π := by
        apply biprod.hom_ext'
        · simp [← Category.assoc,show a ≫ π = 0 from cokernel.condition a,a,π]
        · simp [b]
      let _ : Epi (b ≫ π) := epi_of_epi_fac heq
      obtain ⟨⟨m,hm,⟨ei⟩⟩,s,hs⟩ := ih hQ (b ≫ π)
      let seq := ShortComplex.mk a π (cokernel.condition a)
      let spl := ShortComplex.Splitting.ofExactOfSection seq (ShortComplex.exact_cokernel a) (s ≫ b)
        ((Category.assoc ..).trans hs) (inferInstanceAs (Mono a))
      let iso : N ≅ FGModuleCat.of R (Fin (m+1) → S) :=
        spl.isoBinaryBiproduct.trans ((biprod.mapIso (Iso.refl S) ei).trans (powerSuccIso S m))
      refine ⟨⟨m+1,Nat.succ_le_succ hm,⟨iso⟩⟩,biprod.lift spl.r (π ≫ s) ≫ e.hom,?_⟩
      change (biprod.lift spl.r (π ≫ s) ≫ e.hom) ≫ f = _
      rw [Category.assoc,← show d = e.hom ≫ f from rfl,← decomp,biprod.lift_desc,Category.assoc]
      exact spl.id

namespace FieldExtension

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Algebra k R] [Module.Finite k R]
  [Module.Finite k F] [IsNoetherianRing (ExtendedAlgebra k F R)]

/-- A nonzero map from a ground stable module into the restriction of a
stable extension module identifies that restriction with a positive power
of the ground module. The multiplicity is at most the extension degree. -/
theorem restrict_stable_is_power (P : TwoTerm R) {S : FGModuleCat.{u} R}
    {N : FGModuleCat.{u} (ExtendedAlgebra k F R)} (hS : (P.eulerWeight k).IsStable S)
    (hN : ((extendTwoTerm k F R P).eulerWeight F).IsStable N)
    (i : S ⟶ restrictObj k F R N) (hi : i ≠ 0) :
    ∃ m, 0 < m ∧ m ≤ Module.finrank k F ∧ Nonempty (restrictObj k F R N ≅ FGModuleCat.of R (Fin m → S)) := by
  obtain ⟨g,hg⟩ := exists_epi_of_hom_restrictObj k F R P hS.isSemistable hN i hi
  let e := (restrictExtendBasisEquiv k F R (Module.finBasis k F) S).toFGModuleCatIso
  let d : FGModuleCat.of R (Fin (Module.finrank k F) → S) ⟶ restrictObj k F R N := e.inv ≫ (restrict k F R).map g
  have hd : Epi d := (FGModuleCat.epi_iff_surjective d).2 (((FGModuleCat.epi_iff_surjective g).1 hg).comp
    ((FGModuleCat.isIso_iff_bijective e.inv).1 inferInstance).2)
  have hres : (P.eulerWeight k).IsSemistable (restrictObj k F R N) := (isSemistable_restrictObj_iff k F R P N).2 hN.isSemistable
  obtain ⟨⟨m,hm,⟨iso⟩⟩,_⟩ := hS.split_quotient_of_power _ hres d
  refine ⟨m,?_,hm,⟨iso⟩⟩
  by_contra! hz
  obtain rfl : m = 0 := Nat.eq_zero_of_le_zero hz
  have hs := (FGModuleCat.isZero_iff_subsingleton (FGModuleCat.of R (Fin 0 → S))).2
    (inferInstanceAs (Subsingleton (Fin 0 → S)))
  exact hi ((hs.of_iso iso).eq_of_tgt i 0)

end FieldExtension
end EFiniteCharacterizations
