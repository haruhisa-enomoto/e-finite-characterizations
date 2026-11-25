module

public import EFiniteCharacterizations.Modules.ProjectiveCovers
public import EFiniteCharacterizations.Presentations.PresiltingHom

/-! # Minimal projective presentations and their Hom surjectivity -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- A minimal projective presentation consists of a projective cover and a
projective cover of its kernel. -/
structure MinimalPresentation (M : FGModuleCat.{u} R) where
  cover : FGModuleCat.ProjectiveCover M
  relations : FGModuleCat.ProjectiveCover (kernel cover.hom)

namespace MinimalPresentation

variable {M : FGModuleCat.{u} R}

/-- The complex underlying a minimal presentation. -/
noncomputable def twoTerm (p : MinimalPresentation M) : TwoTerm R where
  source := p.relations.source
  target := p.cover.source
  projective_source := p.relations.projective_source
  projective_target := p.cover.projective_source
  differential := p.relations.hom ≫ kernel.ι p.cover.hom

theorem differential_comp_cover (p : MinimalPresentation M) :
    p.twoTerm.differential ≫ p.cover.hom = 0 := by
  change (p.relations.hom ≫ kernel.ι p.cover.hom) ≫ p.cover.hom = 0
  rw [Category.assoc, kernel.condition, comp_zero]

/-- The cover of a minimal presentation realizes the cokernel of its differential. -/
noncomputable def isCokernel (p : MinimalPresentation M) :
    IsColimit (CokernelCofork.ofπ p.cover.hom p.differential_comp_cover) := by
  let _ := p.cover.epi_hom
  let _ := p.relations.epi_hom
  exact isCokernelEpiComp (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel p.cover.hom))
    p.relations.hom rfl

/-- The module presented by a minimal presentation is its cokernel. -/
noncomputable def cokernelIso (p : MinimalPresentation M) : cokernel p.twoTerm.differential ≅ M :=
  (cokernelIsCokernel p.twoTerm.differential).coconePointUniqueUpToIso p.isCokernel

/-- A minimal projective presentation of a retract splits degreewise
from any projective presentation of the larger module. -/
theorem exists_split_presentation_maps (p : MinimalPresentation M)
    {N : FGModuleCat.{u} R} (i : M ⟶ N) (r : N ⟶ M) (hi : i ≫ r = 𝟙 M)
    (Q : TwoTerm R) (q : Q.target ⟶ N) [Epi q]
    (hq : Q.differential ≫ q = 0) (he : (ShortComplex.mk Q.differential q hq).Exact)
    : ∃ (f : p.twoTerm.target ⟶ Q.target) (g : Q.target ⟶ p.twoTerm.target)
        (a : p.twoTerm.source ⟶ Q.source) (b : Q.source ⟶ p.twoTerm.source),
      a ≫ Q.differential = p.twoTerm.differential ≫ f ∧
      b ≫ p.twoTerm.differential = Q.differential ≫ g ∧ f ≫ g = 𝟙 _ ∧ a ≫ b = 𝟙 _ := by
  let _ := p.cover.projective_source
  let _ := p.relations.projective_source
  let _ := p.cover.epi_hom
  let _ := Q.projective_source
  let _ := Q.projective_target
  let d : p.relations.source ⟶ p.cover.source := p.twoTerm.differential
  have hd : d ≫ p.cover.hom = 0 := p.differential_comp_cover
  have hp : (ShortComplex.mk d p.cover.hom hd).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ p.isCokernel
  obtain ⟨f, hf⟩ := FGModuleCat.exists_lift_of_projective q (p.cover.hom ≫ i)
  obtain ⟨g, hg⟩ := FGModuleCat.exists_lift_of_projective p.cover.hom (q ≫ r)
  have hfg : (f ≫ g) ≫ p.cover.hom = p.cover.hom := by
    rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc, hi, Category.comp_id]
  let _ := p.cover.rightMinimal _ hfg
  let g' := g ≫ inv (f ≫ g)
  have hg' : g' ≫ p.cover.hom = q ≫ r := by
    have hv : inv (f ≫ g) ≫ p.cover.hom = p.cover.hom := by
      calc
        inv (f ≫ g) ≫ p.cover.hom = inv (f ≫ g) ≫ (f ≫ g) ≫ p.cover.hom := by rw [hfg]
        _ = p.cover.hom := IsIso.inv_hom_id_assoc _ _
    dsimp only [g']
    rw [Category.assoc, hv, hg]
  have hsplit : f ≫ g' = 𝟙 _ := by
    dsimp only [g']
    rw [← Category.assoc, IsIso.hom_inv_id]
  have hfz : (d ≫ f) ≫ q = 0 := by
    rw [Category.assoc, hf, ← Category.assoc, hd, zero_comp]
  have hgz : (Q.differential ≫ g') ≫ p.cover.hom = 0 := by
    rw [Category.assoc, hg', ← Category.assoc, hq, zero_comp]
  obtain ⟨a, ha⟩ := TwoTerm.exists_lift_of_exact hq he _ hfz
  obtain ⟨b, hb⟩ := TwoTerm.exists_lift_of_exact hd hp _ hgz
  have hab : (a ≫ b) ≫ d = d := by
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, hsplit, Category.comp_id]
  have hab' : (a ≫ b) ≫ p.relations.hom = p.relations.hom := by
    apply (cancel_mono (kernel.ι p.cover.hom)).mp
    rw [Category.assoc]
    exact hab
  let _ := p.relations.rightMinimal _ hab'
  let b' := b ≫ inv (a ≫ b)
  have hw : (inv (a ≫ b)) ≫ d = d := by
    calc
      inv (a ≫ b) ≫ d = inv (a ≫ b) ≫ ((a ≫ b) ≫ d) := by rw [hab]
      _ = d := by simp
  exact ⟨f,g',a,b',ha,(Category.assoc b _ d).trans ((congrArg (b ≫ ·) hw).trans hb),hsplit,
    (Category.assoc a b _).symm.trans (IsIso.hom_inv_id (a ≫ b))⟩

/-- Suppose that `M` is a retract of the module presented by `Q`.
Surjectivity of the Hom map of `Q` into a module implies surjectivity
of the Hom map of the minimal presentation of `M` into that module. -/
theorem surjective_precompose_of_presentation_retract (p : MinimalPresentation M)
    {N : FGModuleCat.{u} R} (i : M ⟶ N) (r : N ⟶ M) (hi : i ≫ r = 𝟙 M)
    (Q : TwoTerm R) (q : Q.target ⟶ N) [Epi q]
    (hq : Q.differential ≫ q = 0) (he : (ShortComplex.mk Q.differential q hq).Exact)
    {L : FGModuleCat.{u} R} (hQ : Function.Surjective (Q.precompose L)) :
    Function.Surjective (p.twoTerm.precompose L) := by
  obtain ⟨f,g,a,b,ha,_,_,hab⟩ := p.exists_split_presentation_maps i r hi Q q hq he
  intro v
  obtain ⟨w,hw⟩ := hQ (b ≫ v)
  change Q.differential ≫ w = b ≫ v at hw
  refine ⟨f ≫ w,?_⟩
  change p.twoTerm.differential ≫ f ≫ w = v
  rw [← Category.assoc,← ha,Category.assoc,hw,← Category.assoc,hab,Category.id_comp]

/-- The Hom test for tau-rigidity descends along a retract of the presented module. -/
theorem surjective_precompose_of_retract (p : MinimalPresentation M)
    {N : FGModuleCat.{u} R} (i : M ⟶ N) (r : N ⟶ M) (hi : i ≫ r = 𝟙 M)
    (Q : TwoTerm R) (q : Q.target ⟶ N) [Epi q]
    (hq : Q.differential ≫ q = 0) (he : (ShortComplex.mk Q.differential q hq).Exact)
    (hQ : Function.Surjective (Q.precompose N)) :
    Function.Surjective (p.twoTerm.precompose M) := by
  apply p.surjective_precompose_of_presentation_retract i r hi Q q hq he
  intro v
  obtain ⟨w, hw⟩ := hQ (v ≫ i)
  change Q.differential ≫ w = v ≫ i at hw
  refine ⟨w ≫ r, ?_⟩
  change Q.differential ≫ w ≫ r = v
  rw [← Category.assoc, hw, Category.assoc, hi, Category.comp_id]

variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

include k in
theorem nonempty_minimalPresentation (M : FGModuleCat.{u} R) : Nonempty (MinimalPresentation M) := by
  obtain ⟨p⟩ := FGModuleCat.nonempty_projectiveCover k M
  obtain ⟨q⟩ := FGModuleCat.nonempty_projectiveCover k (kernel p.hom)
  exact ⟨⟨p, q⟩⟩

end MinimalPresentation

end EFiniteCharacterizations
