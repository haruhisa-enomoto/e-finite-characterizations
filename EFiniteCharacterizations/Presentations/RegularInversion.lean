module

public import EFiniteCharacterizations.LargeModules.LargePerpendicular
public import Mathlib.RingTheory.Finiteness.Finsupp

/-! # Testing inversion on the restricted regular module -/

@[expose] public section

universe u
namespace EFiniteCharacterizations.TwoTerm

variable {R : Type u} [Ring R]

private theorem surj_finsupp (P : TwoTerm R) (N : ModuleCat.{u} R)
    (hs : Function.Surjective (fun f : P.target →ₗ[R] N ↦ f.comp P.differential.hom.hom))
    (ι : Type u) :
    Function.Surjective (fun f : P.target →ₗ[R] (ι →₀ N) ↦ f.comp P.differential.hom.hom) := by
  classical
  intro f
  have : Module.Finite R P.source := P.source.property
  obtain ⟨v,rfl⟩ := (LinearMap.finsuppLinearMap_bijective_of_moduleFinite R P.source N ι ℕ).2 f
  choose l hl using hs
  let w : ι →₀ (P.target →ₗ[R] N) := v.mapRange (fun a ↦ if a = 0 then 0 else l a) (by simp)
  refine ⟨LinearMap.finsuppLinearMap ℕ w,?_⟩
  apply LinearMap.ext
  intro x
  ext i
  change (if v i = 0 then 0 else l (v i)) (P.differential.hom.hom x) = v i x
  split_ifs with h
  · simp [h]
  · exact LinearMap.congr_fun (hl _) x

private def restrictHom {T : Type u} [Ring T] (g : R →+* T)
    {M N : Type u} [AddCommGroup M] [Module T M] [AddCommGroup N] [Module T N] (f : M →ₗ[T] N) :
    letI := Module.compHom M g
    letI := Module.compHom N g
    M →ₗ[R] N := by
  letI := Module.compHom M g
  letI := Module.compHom N g
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r m ↦ f.map_smul (g r) m }

private theorem surj_restrict (P : TwoTerm R) {T : Type u} [Ring T] (g : R →+* T)
    (hg : letI := Module.compHom T g; P.InvertedOn (ModuleCat.of R T))
    (N : Type u) [AddCommGroup N] [Module T N] :
    letI := Module.compHom N g
    Function.Surjective (fun f : P.target →ₗ[R] N ↦ f.comp P.differential.hom.hom) := by
  let := Module.compHom T g
  let := Module.compHom N g
  let q := Finsupp.linearCombination T (id : N → N)
  have hq : Function.Surjective (restrictHom g q) := Finsupp.linearCombination_surjective _ Function.surjective_id
  have := P.projective_source
  intro f
  obtain ⟨v,hv⟩ := Module.projective_lifting_property (restrictHom g q) f hq
  obtain ⟨z,hz⟩ := surj_finsupp P (ModuleCat.of R T) ((invertedOn_iff_linear P _).1 hg).2 N v
  exact ⟨(restrictHom g q).comp z, (congrArg ((restrictHom g q).comp ·) hz).trans hv⟩

/-- A map of finite projectives is inverted on all restricted modules exactly
when it is inverted on the restricted regular module. -/
theorem invertedOn_restrictions_iff_regular (P : TwoTerm R) {T : Type u} [Ring T] (g : R →+* T) :
    (∀ (N : Type u) [AddCommGroup N] [Module T N], letI := Module.compHom N g
      P.InvertedOn (ModuleCat.of R N)) ↔
      (letI := Module.compHom T g; P.InvertedOn (ModuleCat.of R T)) := by
  refine ⟨fun h ↦ h T,?_⟩
  intro hg N _ _
  let := Module.compHom T g
  let := Module.compHom N g
  apply (invertedOn_iff_linear P _).2
  refine ⟨?_,surj_restrict P g hg N⟩
  intro f f' he
  let q := Finsupp.linearCombination T (id : N → N)
  have hq : Function.Surjective (restrictHom g q) := Finsupp.linearCombination_surjective _ Function.surjective_id
  have := P.projective_target
  obtain ⟨v,hv⟩ := Module.projective_lifting_property (restrictHom g q) (f - f') hq
  let d := P.differential.hom.hom
  have hzero (x : P.source) : q (v (d x)) = 0 := by
    change (restrictHom g q) (v (d x)) = 0
    rw [show (restrictHom g q) (v (d x)) = _ from LinearMap.congr_fun hv (d x)]
    exact sub_eq_zero.mpr (LinearMap.congr_fun he x)
  let := Module.compHom (LinearMap.ker q) g
  let w : P.source →ₗ[R] q.ker :=
    { toFun := fun x ↦ ⟨v (d x),hzero x⟩
      map_add' := fun x y ↦ Subtype.ext (by simp)
      map_smul' := fun r x ↦ Subtype.ext ((v.comp d).map_smul r x) }
  obtain ⟨z,hz⟩ := surj_restrict P g hg q.ker w
  let z' := (restrictHom g q.ker.subtype).comp z
  have eqv : v = z' := by
    apply LinearMap.ext
    intro x
    ext i
    let c := Finsupp.lapply (R := R) (M := T) (α := N) i
    have heq : c.comp v = c.comp z' := ((invertedOn_iff_linear P _).1 hg).1
      (LinearMap.ext fun y ↦ congrArg (fun a : q.ker ↦ (a : N →₀ T) i) (LinearMap.congr_fun hz y).symm)
    exact LinearMap.congr_fun heq x
  apply sub_eq_zero.mp
  rw [← hv, eqv]
  exact LinearMap.ext fun x ↦ (z x).property

end EFiniteCharacterizations.TwoTerm
