module

public import EFiniteCharacterizations.Silting.Fans.ConeGeneratorInterior
public import EFiniteCharacterizations.Stability.ConeTorsionPairs
public import EFiniteCharacterizations.Subcategories.CompactTorsion

/-! # Compactness of both numerical torsion classes at a covered real weight -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R] [IsNoetherianRing R]

/-- At a real weight, the strict test requires positive weight on nonzero quotients. -/
def realStrictTorsion (v : RealProjectiveSpace R) : ObjectProperty (FGModuleCat.{u} R) :=
  fun M ↦ ∀ {Q : FGModuleCat.{u} R} (q : M ⟶ Q) [Epi q], ¬ IsZero Q →
    0 < realEulerEvaluation k (GrothendieckGroup.of Q) v

/-- At a real weight, the weak test requires nonnegative weight on all quotients. -/
def realWeakTorsion (v : RealProjectiveSpace R) : ObjectProperty (FGModuleCat.{u} R) :=
  fun M ↦ ∀ {Q : FGModuleCat.{u} R} (q : M ⟶ Q) [Epi q],
    0 ≤ realEulerEvaluation k (GrothendieckGroup.of Q) v

include k in
/-- A left approximation of the regular module gives a torsion generator. Its Nakayama
approximation gives a finite module cutting out the same class by Hom vanishing. -/
theorem bicompact_of_covariantlyFinite_torsion (T : ObjectProperty (FGModuleCat.{u} R))
    (h : CovariantlyFinite T) (closed : ∀ B, T B → generatedTorsionClass B ≤ T) :
    (∃ B, T = generatedTorsionClass B) ∧ ∃ N : FGModuleCat.{u} R, ∀ M, T M ↔ Subsingleton (M ⟶ N) := by
  let P := FGModuleCat.of R R
  let _ : Module.Projective R P := inferInstanceAs (Module.Projective R R)
  obtain ⟨B,a,hB,ha⟩ := h P
  have gen : T = generatedTorsionClass B := by
    apply le_antisymm _ (closed B hB)
    intro X hX Y hY f
    apply FGModuleCat.hom_ext
    ext x
    let u : P ⟶ X := FGModuleCat.ofHom (LinearMap.toSpanSingleton R X x)
    obtain ⟨b,hb⟩ := ha X hX u
    have he : u ≫ f = 0 := by rw [← hb,Category.assoc,hY (b ≫ f),comp_zero]
    have hx := congrArg (fun z : P ⟶ Y ↦ z.hom.hom 1) he
    change f.hom.hom (LinearMap.toSpanSingleton R X x 1) = 0 at hx
    rwa [LinearMap.toSpanSingleton_apply_one] at hx
  refine ⟨⟨B,gen⟩,?_⟩
  obtain ⟨C,p,hp,hfac⟩ := exists_nakayama_approximation k T a ha
  obtain ⟨L,N,i,q,w,hL,hN,hs⟩ := (isTorsionPair_generated B).2 C
  let : Epi (ShortComplex.mk i q w).g := hs.epi_g
  obtain ⟨b,hb⟩ := CokernelCofork.IsColimit.desc' hs.exact.gIsCokernel p (hp _ (gen ▸ hL) i)
  refine ⟨N,fun M ↦ ⟨fun hm ↦ ⟨fun f g ↦ ((gen ▸ hm : generatedTorsionClass B M) N hN f).trans
    ((gen ▸ hm : generatedTorsionClass B M) N hN g).symm⟩,fun hm ↦ ?_⟩⟩
  obtain ⟨K,Z,j,z,w',hK,hZ,hs'⟩ := (isTorsionPair_generated B).2 M
  have : Epi z := hs'.epi_g
  have hz : IsZero Z := by
    by_contra hn
    have hdim := dimensionWeight_pos k Z hn
    rw [dimensionWeight,projectiveHomWeight_eval,Int.natCast_pos,homFinrank_eq_finrank] at hdim
    have := finiteModuleHom_isFinite k P Z
    have he : Module.finrank k (Z ⟶ nakayamaObject k P) = Module.finrank k (P ⟶ Z) :=
      (nakayamaPairing k P Z).finrank_eq.symm.trans (Subspace.dual_finrank_eq ..)
    obtain ⟨f,hf⟩ := (homFinrank_pos_iff k Z _).1 (by rw [homFinrank_eq_finrank,he]; exact hdim)
    obtain ⟨t,ht⟩ := hfac Z hZ f
    have kill : t ≫ q = 0 := (cancel_epi z).1 (hm.elim _ _)
    change q ≫ b = p at hb
    exact hf (by rw [← ht,← hb,← Category.assoc,kill,zero_comp])
  have : IsIso j := hs'.isIso_f_iff.2 hz
  rw [gen]
  exact leftHomOrthogonal_of_epi j hK

include k in
/-- A single module cuts out a covariantly finite strict numerical torsion class by Hom vanishing. -/
theorem exists_cogenerator_of_covariantlyFinite_strict (θ : Weight (FGModuleCat.{u} R))
    (h : CovariantlyFinite θ.strictTorsionClass) :
    ∃ N : FGModuleCat.{u} R, ∀ M, θ.strictTorsionClass M ↔ Subsingleton (M ⟶ N) := by
  apply (bicompact_of_covariantlyFinite_torsion k _ h ?_).2
  intro B hB M hM
  rw [strictTorsionClass_eq_leftOrthogonal k θ] at hB ⊢
  exact fun Y hY f ↦ hM Y (hB Y hY) f

include k in
private theorem bicompact_of_generators (T : ObjectProperty (FGModuleCat.{u} R))
    (B N : FGModuleCat.{u} R) (gen : T = IsGeneratedBy B)
    (orth : ∀ M, T M ↔ Subsingleton (M ⟶ N)) :
    FunctoriallyFinite T ∧ (∃ A, T = generatedTorsionClass A) ∧ (∃ D : FGModuleCat.{u} R, ∀ M, T M ↔ Subsingleton (M ⟶ D)) := by
  have hB : T B := gen ▸ (show IsGeneratedBy B B from ⟨1,biproduct.π (fun _ : Fin 1 ↦ B) 0,inferInstance⟩)
  refine ⟨gen ▸ functoriallyFinite_generatedBy k B,⟨B,funext fun M ↦ propext ⟨fun hm Y hY f ↦ ?_,fun hm ↦ ?_⟩⟩,N,orth⟩
  · exact (show IsGeneratedBy B M from gen ▸ hm).hom_eq_zero f (fun a ↦ hY (a ≫ f))
  · exact (orth M).2 ⟨fun f g ↦ (hm N (fun a ↦ ((orth B).1 hB).elim a 0) f).trans
      (hm N (fun a ↦ ((orth B).1 hB).elim a 0) g).symm⟩

/-- At every point of the real fan both numerical torsion classes are functorially finite,
generated as torsion classes by one module, and left orthogonal to one module. -/
theorem covered_real_torsion_bicompact {v : RealProjectiveSpace R} (hv : v ∈ TwoTerm.gVectorFanSupport R) :
    ∀ T ∈ ({realStrictTorsion k v,realWeakTorsion k v} : Set (ObjectProperty (FGModuleCat.{u} R))),
      FunctoriallyFinite T ∧ (∃ B, T = generatedTorsionClass B) ∧
      ∃ N : FGModuleCat.{u} R, ∀ M, T M ↔ Subsingleton (M ⟶ N) := by
  obtain ⟨P,hP,hv⟩ := (TwoTerm.mem_fanSupport_iff_cone_interior k v).1 hv
  have h := P.cone_interior_torsion_identities k hP hv
  intro T hT
  rcases Set.mem_insert_iff.1 hT with rfl | hT
  · have hgen : realStrictTorsion k v = IsGeneratedBy (cokernel P.differential) :=
      funext fun M ↦ propext (h M).1
    have he : realStrictTorsion k v = (P.eulerWeight k).strictTorsionClass :=
      funext fun M ↦ propext ((h M).1.trans (P.pos_eulerWeight_nonzero_quotients_iff k hP M).symm)
    obtain ⟨N,hN⟩ := exists_cogenerator_of_covariantlyFinite_strict k (P.eulerWeight k)
      (he ▸ hgen.symm ▸ (functoriallyFinite_generatedBy k (cokernel P.differential)).1)
    exact bicompact_of_generators k _ _ N hgen (he ▸ hN)
  · obtain rfl := Set.mem_singleton_iff.1 hT
    obtain ⟨Q,_,_,hgen⟩ := P.exists_bongartz_complement k hP
    exact bicompact_of_generators k _ (cokernel Q.differential) (P.nakayamaKernel k)
      (funext fun M ↦ propext ((h M).2.1.trans
        ((P.surjective_precompose_iff_no_hom_nakayamaKernel k M).symm.trans (hgen M)))) (fun M ↦ (h M).2.1)

end EFiniteCharacterizations
