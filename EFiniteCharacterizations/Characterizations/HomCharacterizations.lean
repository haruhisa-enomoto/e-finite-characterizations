module

public import EFiniteCharacterizations.ScalarExtension.GroundFieldWitnesses
public import EFiniteCharacterizations.Stability.StableDependentExtraction

/-!
# Core module-theoretic and semibrick characterizations

Theorem 3.2 of the manuscript (excluding `(comp-tors)`, which is proved in
`Subcategories/CompactTorsionEquivalences.lean`). Over an arbitrary field `k`,
this file establishes the equivalence of E-finiteness `(E-fin)` with:

* `EqualClassHom` (`(K₀-Hom)`): any two nonzero modules of the same dimension
  vector admit a nonzero homomorphism in each direction;
* `EqualClassBrickHom`: the same condition restricted to pairs of bricks;
* `NumericallyDisjointTorsionPairs` (`(num-disj)`): no nonzero torsion module
  and torsion-free module for a torsion pair share a dimension vector;
* finiteness of every semibrick (`(fin-sbrick)`);
* uniqueness of the simple modules as an `n`-element semibrick (`(n-sbrick)`).
-/

@[expose] public section

open CategoryTheory

universe u

namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R] [IsArtinianRing R]

include k in
/-- Forward implication `(E-fin) ⇒ (K₀-Hom)`: if `Hom(M, N) = 0` for nonzero modules with `[M] = [N]`,
extraction produces a jointly stable dependent semibrick, contradicting linear independence at covered weights. -/
theorem equalClassHom_of_isEFinite (h : IsEFinite R) : EqualClassHom (FGModuleCat.{u} R) := by
  by_contra hn
  obtain ⟨s, g, hs, hd⟩ := FamilyExtraction.exists_jointly_stable_dependent_semibrick k hn
  let f (x : s) : stableClasses (C := FGModuleCat.{u} R) (projectiveClassWeight k g) := ⟨x.val, hs x.property⟩
  exact hd ((linearIndependent_stableClasses_of_isEFinite k h g).comp f
    (fun x y he ↦ Subtype.ext (congrArg (fun z : stableClasses (C := FGModuleCat.{u} R) (projectiveClassWeight k g) ↦ z.val) he)))

include k in
/-- **Theorem 3.2, `(E-fin) ⇔ (K₀-Hom)`.** -/
theorem isEFinite_iff_equalClassHom : IsEFinite R ↔ EqualClassHom (FGModuleCat.{u} R) :=
  ⟨equalClassHom_of_isEFinite k, isEFinite_of_equalClassHom_allFields k⟩

include k in
/-- Variant of `(K₀-Hom)` restricted to bricks of equal Grothendieck class. -/
theorem isEFinite_iff_equalClassBrickHom : IsEFinite R ↔ EqualClassBrickHom (FGModuleCat.{u} R) :=
  ⟨fun h ↦ equalClassBrickHom_of_equalClassHom (equalClassHom_of_isEFinite k h),
    isEFinite_of_equalClassBrickHom_allFields k⟩

include k in
/-- **Theorem 3.2, `(E-fin) ⇔ (num-disj)`.** -/
theorem isEFinite_iff_numericallyDisjointTorsionPairs :
    IsEFinite R ↔ NumericallyDisjointTorsionPairs (FGModuleCat.{u} R) :=
  (isEFinite_iff_equalClassHom k).trans numericallyDisjointTorsionPairs_iff_equalClassHom.symm

include k in
/-- **Theorem 3.2, `(E-fin) ⇔ (fin-sbrick)`.** -/
theorem isEFinite_iff_finite_semibricks :
    IsEFinite R ↔ ∀ s : Set (Skeleton (FGModuleCat.{u} R)), IsSemibrick s → s.Finite :=
  ⟨fun h _ hs ↦ FamilyExtraction.finite_semibricks_of_equalClassHom k (equalClassHom_of_isEFinite k h) hs,
    isEFinite_of_finite_semibricks_allFields k⟩

include k in
/-- **Theorem 3.2, `(E-fin) ⇔ (n-sbrick)`.** -/
theorem isEFinite_iff_unique_fullSize_semibrick :
    IsEFinite R ↔ ∀ s : Set (Skeleton (FGModuleCat.{u} R)), IsSemibrick s → s.Finite →
      s.ncard = (simpleIsomorphismClasses R).ncard → s = simpleIsomorphismClasses R :=
  ⟨fun h _ hs _ ↦ FamilyExtraction.fullSize_semibrick_eq_simples_of_equalClassHom k
    (equalClassHom_of_isEFinite k h) hs, isEFinite_of_unique_fullSize_semibrick_allFields k⟩

end EFiniteCharacterizations
