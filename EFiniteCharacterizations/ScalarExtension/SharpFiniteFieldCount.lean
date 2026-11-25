module

public import EFiniteCharacterizations.ScalarExtension.FiniteFieldGrowth
public import EFiniteCharacterizations.Silting.Fans.ConeSaturation

/-!
# Exponentially growing families of stable bricks over finite fields

Proposition A.3 (`prop:fq-count`) of Appendix A. Over a finite field `k` of order `q`,
let `P` be a two-term projective presentation whose `g`-vector lies outside `Σ(R)`, and
set `b₀ = dim_k P⁰` and `c₀ = max(1, b₀ · dim_k P⁻¹)`. There is a finite set `Ω` of
integral weights such that for every auxiliary extension degree `s ≥ 1`, at least
`q^s / (c₀ s)` pairwise nonisomorphic ground-field bricks in `mod R` are stable at
weights in `Ω` and satisfy `endolength(M) ≤ b₀` and `dim_k M ≤ s · b₀`
(`exists_stable_bricks_of_each_degree`).
-/

@[expose] public section
open CategoryTheory
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

variable (k : Type u) [Field k] [Finite k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
  [IsNoetherianRing R]

/-- If P represents a class outside the fan, then, for every extension degree s,
there are at least q^s/(c₀ s) ground bricks at one fixed finite list of weights.
Here b₀ is the dimension of the target and c₀ is the larger of one and the
product of the ground dimensions of the two projectives. -/
theorem exists_stable_bricks_of_each_degree (P : TwoTerm R)
    (h : realProjectiveClass R P.projectiveClass ∉ TwoTerm.gVectorFanSupport R) :
    let b₀ := Module.finrank k (P.target.obj : Type u)
    let c₀ := max 1 (b₀ * Module.finrank k (P.source.obj : Type u))
    ∃ Ω : Finset (ProjectiveClass R), ∀ s : ℕ, 0 < s →
      ∃ B : Finset (Skeleton (FGModuleCat.{u} R)), Nat.card k ^ s ≤ c₀ * s * B.card ∧
        ∀ x ∈ B, ∃ (M : FGModuleCat.{u} R) (g : ProjectiveClass R), toSkeleton M = x ∧ g ∈ Ω ∧
          (projectiveClassWeight k g).IsStable M ∧ IsBrick M ∧ endolength k M ≤ b₀ ∧
          Module.finrank k (M.obj : Type u) ≤ s * b₀ := by
  classical
  have hm := FieldExtension.no_presilting_differential_after_finite_extension k P
    (fun ex ↦ h ((TwoTerm.mem_fanSupport_iff_exists_presilting k _).2 ex))
  obtain ⟨Ω,hΩ⟩ := FieldExtension.exists_sharp_ground_witness_bound k P
  refine ⟨Ω,fun s hs ↦ ?_⟩
  obtain ⟨F,_,_,_,hdeg,hcard⟩ := exists_finiteFieldExtension k s hs
  let _ := Fintype.ofFinite F
  obtain ⟨B,hB,hw⟩ := hΩ F (hm F)
  rw [← Nat.card_eq_fintype_card,hdeg,hcard] at hB
  refine ⟨B,hB,?_⟩
  intro x hx
  obtain ⟨M,g,e,hg,hst,hd,he⟩ := hw x hx
  exact ⟨M,g,e,hg,hst,hst.isBrick,he,hdeg ▸ hd⟩

end EFiniteCharacterizations
