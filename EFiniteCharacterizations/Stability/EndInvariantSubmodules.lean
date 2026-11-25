module

public import EFiniteCharacterizations.Stability.BrickWalls
public import EFiniteCharacterizations.Stability.SubmoduleWeights

/-! # Testing weights on endomorphism-invariant submodules of a brick -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace EFiniteCharacterizations

variable {R : Type u} [Ring R] [IsNoetherianRing R]
variable (k : Type u) [Field k] [Algebra k R] [Module.Finite k R]

/-- A submodule preserved by all endomorphisms of the ambient module. -/
def EndInvariant {M : FGModuleCat.{u} R} (U : Submodule R (M.obj : Type u)) : Prop :=
  ∀ (f : Module.End R (M.obj : Type u)) x, x ∈ U → f x ∈ U

include k in
theorem exists_endInvariant_weight_maximizer {M : FGModuleCat.{u} R} (hb : IsBrick M)
    (θ : Weight (FGModuleCat.{u} R)) :
    ∃ U : Submodule R (M.obj : Type u), EndInvariant (M := M) U ∧
      ∀ V : Submodule R (M.obj : Type u), θ.eval (FGModuleCat.of R V) ≤ θ.eval (FGModuleCat.of R U) := by
  have : Module.Finite k (M.obj : Type u) := Module.Finite.trans R _
  have hf : (Set.range (fun U : Submodule R (M.obj : Type u) ↦ θ.eval (FGModuleCat.of R U))).Finite := by
    refine ((finite_classes_of_groundFinrank_le (R := R) k (Module.finrank k (M.obj : Type u))).image θ).subset ?_
    rintro z ⟨V, rfl⟩
    exact ⟨_, ⟨FGModuleCat.of R V, LinearMap.finrank_le_finrank_of_injective
      (f := V.subtype.restrictScalars k) Subtype.val_injective, rfl⟩, rfl⟩
  obtain ⟨U, hmax, hlarge⟩ := θ.exists_largest_weight_maximizer hf
  refine ⟨U, ?_, hmax⟩
  intro f x hx
  by_cases hz : f = 0
  · simp [hz]
  · let _ := hb.endomorphismDivisionRing k
    have hi : Function.Injective f := by
      intro v w hv
      have H := congrArg (fun z ↦ f⁻¹ z) hv
      change (f⁻¹ * f) v = (f⁻¹ * f) w at H
      simpa [inv_mul_cancel₀ hz] using H
    let e := Submodule.equivMapOfInjective f hi U
    exact hlarge _ (θ.eval_eq_of_isIso e.toFGModuleCatIso.hom).symm ⟨x,hx,rfl⟩

include k in
theorem isSemistable_iff_endInvariant {M : FGModuleCat.{u} R} (hb : IsBrick M)
    (θ : Weight (FGModuleCat.{u} R)) :
    θ.IsSemistable M ↔ θ.eval M = 0 ∧ ∀ U : Submodule R (M.obj : Type u),
      EndInvariant (M := M) U → θ.eval (FGModuleCat.of R U) ≤ 0 := by
  constructor
  · intro h
    refine ⟨h.1, fun U _ ↦ ?_⟩
    let i : FGModuleCat.of R U ⟶ M := FGModuleCat.ofHom U.subtype
    have : Mono i := (FGModuleCat.mono_iff_injective _).2 Subtype.val_injective
    exact h.2 i
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun {V} i hi ↦ ?_⟩
    obtain ⟨U, hU, hmax⟩ := exists_endInvariant_weight_maximizer k hb θ
    let e := LinearEquiv.ofInjective i.hom.hom ((FGModuleCat.mono_iff_injective i).1 hi)
    exact (θ.eval_eq_of_isIso e.toFGModuleCatIso.hom).trans_le
      ((hmax i.hom.hom.range).trans (h U hU))

/-- Hom into an invariant submodule has ground dimension divisible by the
dimension of the brick endomorphism ring. Its quotient is bounded in terms
of the source and the endolength alone. -/
theorem hom_dimension_of_endInvariant {M : FGModuleCat.{u} R} (hb : IsBrick M)
    (P : FGModuleCat.{u} R) {U : Submodule R (M.obj : Type u)} (hU : EndInvariant (M := M) U) :
    ∃ n ≤ Module.finrank k (P.obj : Type u) * endolength k M,
      homFinrank k P (FGModuleCat.of R U) = homFinrank k M M * n := by
  let D := Module.End R (M.obj : Type u)
  let _ : DivisionRing D := hb.endomorphismDivisionRing k
  let V : Submodule D (M.obj : Type u) :=
    { carrier := U.carrier
      add_mem' := U.add_mem
      zero_mem' := U.zero_mem
      smul_mem' := fun d x hx ↦ hU d x hx }
  let _ : Module D U := inferInstanceAs (Module D V)
  let _ : IsScalarTower k D U := inferInstanceAs (IsScalarTower k D V)
  let _ : SMulCommClass R D U := ⟨fun r d x ↦ Subtype.ext (map_smul d r x.val).symm⟩
  let H := (P.obj : Type u) →ₗ[R] U
  have : Module.Finite k (M.obj : Type u) := Module.Finite.trans R _
  have : Module.Finite k (P.obj : Type u) := Module.Finite.trans R _
  have : Module.Finite k U := Module.Finite.trans R _
  have : Module.Finite k H := inferInstanceAs (Module.Finite k ((P.obj : Type u) →ₗ[R] U))
  have he : homFinrank k M M = Module.finrank k D := by
    rw [homFinrank_eq_finrank, (finiteModuleHomLinearEquiv k M M).finrank_eq]
  have hhom : homFinrank k P (FGModuleCat.of R U) = Module.finrank k H := by
    rw [homFinrank_eq_finrank, (finiteModuleHomLinearEquiv k P _).finrank_eq]
  have hm : Module.finrank k (M.obj : Type u) = Module.finrank k D * endolength k M := by
    rw [hb.endolength_eq_finrank k]
    exact (Module.finrank_mul_finrank k D (M.obj : Type u)).symm
  have hn : Module.finrank k H = Module.finrank k D * Module.finrank D H :=
    (Module.finrank_mul_finrank k D H).symm
  refine ⟨Module.finrank D H, ?_, hhom.trans (hn.trans (by rw [he]))⟩
  have hu := LinearMap.finrank_le_finrank_of_injective (f := U.subtype.restrictScalars k) Subtype.val_injective
  have hbound := (homFinrank_le_mul k P (FGModuleCat.of R U)).trans (Nat.mul_le_mul_left _ hu)
  rw [hhom, hn, hm, ← Nat.mul_left_comm] at hbound
  exact Nat.le_of_mul_le_mul_left hbound Module.finrank_pos

/-- At bounded endolength, a finite set of data describes the integral
semistability loci. The data consist of the normalized Hom coordinates of
the whole module and the set of those of its invariant submodules. -/
theorem finite_semistability_loci_at_bounded_endolength (r : ℕ) :
    {s : Set (ProjectiveClass R) | ∃ X : FGModuleCat.{u} R, IsBrick X ∧ endolength k X ≤ r ∧
      s = {g | (projectiveClassWeight (R := R) k g).IsSemistable X}}.Finite := by
  classical
  let I := ↥(simpleIsomorphismClasses R)
  have : Finite I := finite_simpleIsomorphismClasses k
  obtain ⟨Q, hQ⟩ := exists_injective_projective_hom_coordinates (R := R) k
  let G := GrothendieckGroup (FGModuleCat.{u} R)
  let w (i : I) := projectiveClassWeight k (ProjectiveClass.of (Q i))
  let Grid := ∀ i : I, Fin (Module.finrank k ((Q i).val.obj : Type u) * r + 1)
  let code (a : ℕ) (z : G) (v : Grid) := ∀ i, w i z = (a : ℤ) * (v i).val
  let profile (X : FGModuleCat.{u} R) := {v : Grid | ∃ U : Submodule R (X.obj : Type u),
    EndInvariant (M := X) U ∧ code (homFinrank k X X) (GrothendieckGroup.of (FGModuleCat.of R U)) v}
  have grid {X : FGModuleCat.{u} R} (hX : IsBrick X) (hr : endolength k X ≤ r)
      (U : Submodule R (X.obj : Type u)) (hU : EndInvariant (M := X) U) :
      ∃ v : Grid, code (homFinrank k X X) (GrothendieckGroup.of (FGModuleCat.of R U)) v := by
    choose n hn he using fun i : I ↦ hom_dimension_of_endInvariant k hX (Q i).val hU
    refine ⟨fun i ↦ ⟨n i, Nat.lt_succ_of_le ((hn i).trans (Nat.mul_le_mul_left _ hr))⟩, fun i ↦ ?_⟩
    let := (Q i).property
    change (projectiveClassWeight k (ProjectiveClass.of (Q i))).eval (FGModuleCat.of R U) = _
    rw [projectiveClassWeight_of, projectiveHomWeight_eval]
    exact_mod_cast he i
  have whole {X : FGModuleCat.{u} R} (hX : IsBrick X) (hr : endolength k X ≤ r) :
      ∃ v : Grid, code (homFinrank k X X) (GrothendieckGroup.of X) v := by
    obtain ⟨v, hv⟩ := grid hX hr ⊤ (fun _ _ _ ↦ trivial)
    let e := (LinearEquiv.ofTop (⊤ : Submodule R (X.obj : Type u)) rfl).toFGModuleCatIso
    exact ⟨v, (GrothendieckGroup.of_eq_of_iso e) ▸ hv⟩
  have prop {a b : ℕ} {x y : G} {v : Grid} (hx : code a x v) (hy : code b y v) :
      b • x = a • y := by
    apply hQ
    funext i
    change w i (b • x) = w i (a • y)
    rw [map_nsmul, map_nsmul, hx i, hy i, nsmul_eq_mul, nsmul_eq_mul]
    ring
  let L := {s : Set (ProjectiveClass R) | ∃ X : FGModuleCat.{u} R, IsBrick X ∧ endolength k X ≤ r ∧
      s = {g | (projectiveClassWeight (R := R) k g).IsSemistable X}}
  choose X hb hr hl using fun s : L ↦ s.property
  choose v hv using fun s : L ↦ whole (hb s) (hr s)
  let f (s : L) : Grid × Set Grid := (v s, profile (X s))
  have pos (s : L) : 0 < homFinrank k (X s) (X s) :=
    (homFinrank_pos_iff k _ _).mpr ⟨𝟙 _, fun h ↦ (hb s).1 ((Limits.IsZero.iff_id_eq_zero _).2 h)⟩
  have transfer {s t : L} (hf : f s = f t) (g : ProjectiveClass R)
      (hs : (projectiveClassWeight (R := R) k g).IsSemistable (X s)) :
      (projectiveClassWeight (R := R) k g).IsSemistable (X t) := by
    let θ := projectiveClassWeight (R := R) k g
    have hvt : v t = v s := (congrArg Prod.fst hf).symm
    have hst := congrArg θ (prop (hv s) (hvt ▸ hv t))
    simp only [map_nsmul, nsmul_eq_mul] at hst
    refine (isSemistable_iff_endInvariant k (hb t) θ).2 ⟨?_, ?_⟩
    · rw [show θ (GrothendieckGroup.of (X s)) = 0 from hs.1, mul_zero] at hst
      exact (mul_eq_zero.mp hst.symm).resolve_left (by exact_mod_cast (pos s).ne')
    · intro U hU
      obtain ⟨u, hu⟩ := grid (hb t) (hr t) U hU
      have hm : u ∈ profile (X t) := ⟨U,hU,hu⟩
      have he : profile (X s) = profile (X t) := congrArg Prod.snd hf
      obtain ⟨V, hV, hv⟩ := he.symm ▸ hm
      have hθ := congrArg θ (prop hv hu)
      simp only [map_nsmul, nsmul_eq_mul] at hθ
      have hle := (isSemistable_iff_endInvariant k (hb s) θ).1 hs |>.2 V hV
      change θ (GrothendieckGroup.of (FGModuleCat.of R V)) ≤ 0 at hle
      exact nonpos_of_mul_nonpos_right (hθ ▸ mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hle)
        (by exact_mod_cast pos s)
  apply Finite.of_injective f
  intro s t he
  apply Subtype.ext
  rw [hl s, hl t]
  exact Set.ext fun g ↦ ⟨transfer he g, transfer he.symm g⟩

variable [IsArtinianRing R]

theorem finite_brickClassesOfEndolength_of_locus_injective
    (h : ∀ X Y : FGModuleCat.{u} R, IsBrick X → IsBrick Y →
      (∀ g : ProjectiveClass R, (projectiveClassWeight (R := R) k g).IsSemistable X ↔
        (projectiveClassWeight (R := R) k g).IsSemistable Y) → Nonempty (X ≅ Y)) (r : ℕ) :
    (brickClassesOfEndolength (R := R) k r).Finite := by
  classical
  choose M he hr hb using fun x : brickClassesOfEndolength (R := R) k r ↦ x.property
  let S := {s : Set (ProjectiveClass R) | ∃ X : FGModuleCat.{u} R, IsBrick X ∧ endolength k X ≤ r ∧
    s = {g | (projectiveClassWeight (R := R) k g).IsSemistable X}}
  have : Finite S := finite_semistability_loci_at_bounded_endolength k r
  let f (x : brickClassesOfEndolength (R := R) k r) : S :=
    ⟨_, M x, hb x, (hr x).le, rfl⟩
  apply Finite.of_injective f
  intro x y hxy
  have hl := congrArg Subtype.val hxy
  obtain ⟨e⟩ := h _ _ (hb x) (hb y)
    (fun g ↦ Set.ext_iff.mp hl g)
  exact Subtype.ext ((he x).symm.trans ((congr_toSkeleton_of_iso e).trans (he y)))

theorem finite_brickClassesOfEndolength_of_isEFinite (h : IsEFinite R) (r : ℕ) :
    (brickClassesOfEndolength (R := R) k r).Finite :=
  finite_brickClassesOfEndolength_of_locus_injective k
    (fun _ _ ↦ iso_of_same_integral_semistability_locus k h) r

theorem isEFinite_iff_integral_semistability_locus_injective :
    IsEFinite R ↔ ∀ X Y : FGModuleCat.{u} R, IsBrick X → IsBrick Y →
      (∀ g : ProjectiveClass R, (projectiveClassWeight (R := R) k g).IsSemistable X ↔
        (projectiveClassWeight (R := R) k g).IsSemistable Y) → Nonempty (X ≅ Y) :=
  ⟨fun h _ _ ↦ iso_of_same_integral_semistability_locus k h, fun h ↦
    isEFinite_of_finite_brickClassesOfEndolength_allFields k (fun r _ ↦
      finite_brickClassesOfEndolength_of_locus_injective k h r)⟩

theorem isEFinite_iff_endo_brick :
    IsEFinite R ↔ ∀ r : ℕ, 0 < r → (brickClassesOfEndolength (R := R) k r).Finite :=
  ⟨fun h r _ ↦ finite_brickClassesOfEndolength_of_isEFinite k h r,
    isEFinite_of_finite_brickClassesOfEndolength_allFields k⟩

end EFiniteCharacterizations
