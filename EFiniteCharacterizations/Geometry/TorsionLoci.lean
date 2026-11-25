module

public import EFiniteCharacterizations.Geometry.OpenVertexLoci
public import EFiniteCharacterizations.Stability.OppositeAlgebra
public import EFiniteCharacterizations.Subcategories.CompactTorsion

/-! # Zariski openness for torsion and torsion-free classes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace EFiniteCharacterizations

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]

omit [Abelian C] [Abelian D] in
private theorem dual_hom_subsingleton (E : Cᵒᵖ ≌ D) (X Y : C) :
    Subsingleton (E.functor.obj (op Y) ⟶ E.functor.obj (op X)) ↔ Subsingleton (X ⟶ Y) := by
  constructor
  · intro h
    exact ⟨fun f g ↦ Quiver.Hom.op_inj (E.functor.map_injective (h.elim _ _))⟩
  · intro h
    refine ⟨fun f g ↦ ?_⟩
    have hh := h.elim (E.functor.preimage f).unop (E.functor.preimage g).unop
    simpa using E.functor.congr_map (Quiver.Hom.unop_inj hh)

private theorem hom_subsingleton_iff {X Y : C} :
    Subsingleton (X ⟶ Y) ↔ ∀ f : X ⟶ Y, f = 0 :=
  ⟨fun h f ↦ h.elim f 0,fun h ↦ ⟨fun f g ↦ (h f).trans (h g).symm⟩⟩

/-- In a replete torsion pair, each half is recovered from the other by Hom vanishing. -/
theorem IsTorsionPair.left_iff {T F : ObjectProperty C} (h : IsTorsionPair T F)
    [T.IsClosedUnderIsomorphisms] (X : C) :
    T X ↔ ∀ Y, F Y → Subsingleton (X ⟶ Y) := by
  refine ⟨fun hx Y hy ↦ hom_subsingleton_iff.2 (fun f ↦ h.1 f hx hy),fun hh ↦ ?_⟩
  obtain ⟨A,Q,i,p,w,ha,hq,hs⟩ := h.2 X
  have hz := (hh Q hq).elim p 0
  have : Epi p := hs.epi_g
  have hzero : IsZero Q := (IsZero.iff_id_eq_zero Q).2 ((cancel_epi p).1 (by simp [hz]))
  have : IsIso i := hs.isIso_f_iff.2 hzero
  exact T.prop_of_iso (asIso i) ha

theorem IsTorsionPair.right_iff {T F : ObjectProperty C} (h : IsTorsionPair T F)
    [F.IsClosedUnderIsomorphisms] (X : C) :
    F X ↔ ∀ Y, T Y → Subsingleton (Y ⟶ X) := by
  refine ⟨fun hx Y hy ↦ hom_subsingleton_iff.2 (fun f ↦ h.1 f hy hx),fun hh ↦ ?_⟩
  obtain ⟨A,Q,i,p,w,ha,hq,hs⟩ := h.2 X
  have hz := (hh A ha).elim i 0
  have : Mono i := hs.mono_f
  have hzero : IsZero A := (IsZero.iff_id_eq_zero A).2 ((cancel_mono i).1 (by simp [hz]))
  have : IsIso p := hs.isIso_g_iff.2 hzero
  exact F.prop_of_iso (asIso p).symm hq

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
    [IsNoetherianRing R] [IsArtinianRing R]

include k in
private theorem left_perp_neighborhood (he : IsEFinite R) (X : FGModuleCat.{u} R)
    (F : ObjectProperty (FGModuleCat.{u} R)) (hX : ∀ Y, F Y → Subsingleton (X ⟶ Y)) :
    ∃ N, Subsingleton (X ⟶ N) ∧ ∀ Z, Subsingleton (Z ⟶ N) → ∀ Y, F Y → Subsingleton (Z ⟶ Y) := by
  obtain ⟨N,hN⟩ := exists_left_perpendicular_of_isEFinite k he X
  refine ⟨N,hom_subsingleton_iff.2 ((hN X).1 (fun _ h ↦ h)),fun Z hZ Y hY ↦ ?_⟩
  exact hom_subsingleton_iff.2 ((hN Z).2 (hom_subsingleton_iff.1 hZ) Y (hom_subsingleton_iff.1 (hX Y hY)))

include k in
omit [IsArtinianRing R] [IsNoetherianRing R] in
private theorem right_perp_neighborhood (he : IsEFinite R) (X : FGModuleCat.{u} R)
    (T : ObjectProperty (FGModuleCat.{u} R)) (hX : ∀ Y, T Y → Subsingleton (Y ⟶ X)) :
    ∃ N, Subsingleton (N ⟶ X) ∧ ∀ Z, Subsingleton (N ⟶ Z) → ∀ Y, T Y → Subsingleton (Y ⟶ Z) := by
  let _ := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  let _ := IsArtinianRing.of_finite k Rᵐᵒᵖ
  let E := Contragredient.dualityEquivalence k R
  let DX (Y : FGModuleCat.{u} R) := E.functor.obj (op Y)
  let U (W : FGModuleCat.{u} Rᵐᵒᵖ) := ∃ Y, T Y ∧ DX Y = W
  obtain ⟨N,hN,hZ⟩ := left_perp_neighborhood k ((isEFinite_iff_opposite k).1 he) (DX X) U
    (fun _ ⟨Y,hY,h⟩ ↦ h ▸ (dual_hom_subsingleton E Y X).2 (hX Y hY))
  let A := (E.inverse.obj N).unop
  let f : DX A ≅ N := E.counitIso.app N
  have equiv (Y : FGModuleCat.{u} R) : Subsingleton (A ⟶ Y) ↔ Subsingleton (DX Y ⟶ N) := by
    rw [← dual_hom_subsingleton E A Y]
    exact (Iso.homCongr (Iso.refl (DX Y)) f).subsingleton_congr
  exact ⟨A,(equiv X).2 hN,fun Z h Y hY ↦
    (dual_hom_subsingleton E Y Z).1 (hZ (DX Z) ((equiv Z).1 h) (DX Y) ⟨Y,hY,rfl⟩)⟩

namespace VertexRepresentation.SplitBasicVertices

variable {k} {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J]
    (P : SplitBasicVertices k R I) (b : Module.Basis J k R)

omit [IsNoetherianRing R] [IsArtinianRing R] in
private theorem open_perps (d : I → ℕ) (N : FGModuleCat.{u} R) :
    @IsOpen (VertexRepresentation (k := k) d P.vertex) (zariski b) {ρ | Subsingleton (N ⟶ ρ.moduleObj)} ∧
    @IsOpen (VertexRepresentation (k := k) d P.vertex) (zariski b) {ρ | Subsingleton (ρ.moduleObj ⟶ N)} := by
  exact isOpen_hom_perpendiculars (affineCoordinates b) moduleObj vertexBasis b _ (P.eval_matrix b d) N

/-- Openness of every replete torsion half in every vertex dimension. -/
def OpenTorsionLoci : Prop :=
  ∀ d (T F : ObjectProperty (FGModuleCat.{u} R)), IsTorsionPair T F → T.IsClosedUnderIsomorphisms →
    @IsOpen (VertexRepresentation (k := k) d P.vertex) (zariski b) {ρ | T ρ.moduleObj}

/-- Openness of every replete torsion-free half in every vertex dimension. -/
def OpenTorsionFreeLoci : Prop :=
  ∀ d (T F : ObjectProperty (FGModuleCat.{u} R)), IsTorsionPair T F → F.IsClosedUnderIsomorphisms →
    @IsOpen (VertexRepresentation (k := k) d P.vertex) (zariski b) {ρ | F ρ.moduleObj}

theorem openTorsionLoci_of_isEFinite (he : IsEFinite R) : P.OpenTorsionLoci b := by
  intro d T F hpair hT
  let _ := zariski (d := d) (e := P.vertex) b
  apply isOpen_iff_forall_mem_open.2
  intro ρ hρ
  obtain ⟨N,hN,hs⟩ := left_perp_neighborhood k he _ F ((hpair.left_iff _).1 hρ)
  exact ⟨_,fun η hη ↦ (hpair.left_iff _).2 (hs η.moduleObj hη), (P.open_perps b d N).2,hN⟩

omit [IsArtinianRing R] in
theorem openTorsionFreeLoci_of_isEFinite (he : IsEFinite R) : P.OpenTorsionFreeLoci b := by
  intro d T F hpair hF
  let _ := zariski (d := d) (e := P.vertex) b
  apply isOpen_iff_forall_mem_open.2
  intro ρ hρ
  obtain ⟨N,hN,hs⟩ := right_perp_neighborhood k he _ T ((hpair.right_iff _).1 hρ)
  exact ⟨_,fun η hη ↦ (hpair.right_iff _).2 (hs η.moduleObj hη), (P.open_perps b d N).1,hN⟩

omit [Module.Finite k R] [IsArtinianRing R] in
private theorem finite_stable_family_of_open_loci {L : Type*} (d : I → ℕ)
    (p : L → VertexRepresentation (k := k) d P.vertex) (θ : Weight (FGModuleCat.{u} R))
    (hs : ∀ i, θ.IsStable (p i).moduleObj) (hd : ∀ i j, Nonempty ((p i).moduleObj ≅ (p j).moduleObj) → i = j)
    (ho : P.OpenTorsionLoci b ∨ P.OpenTorsionFreeLoci b) : Finite L := by
  classical
  let Z i := (p i).moduleObj
  let gens (s : Set L) (X : FGModuleCat.{u} R) := ∃ i ∈ s, Z i = X
  let F (s : Set L) : ObjectProperty (FGModuleCat.{u} R) := fun Y ↦ ∀ B, gens s B → rightHomOrthogonal B Y
  let T s := leftHomOrthogonal (F s)
  have hp s : IsTorsionPair (T s) (F s) := isTorsionPair_generatedBy (gens s)
  have ht s : (T s).IsClosedUnderIsomorphisms := ⟨fun e h Y hY f ↦
    (cancel_epi e.hom).1 (by simpa using h Y hY (e.hom ≫ f))⟩
  have hf s : (F s).IsClosedUnderIsomorphisms := ⟨fun e h B hB f ↦
    (cancel_mono e.inv).1 (by simpa using h B hB (f ≫ e.inv))⟩
  have htmem (s : Set L) i (hi : i ∈ s) : T s (Z i) := fun _ hy ↦ hy _ ⟨i,hi,rfl⟩
  have hfmem (s : Set L) i (hi : i ∉ s) : F s (Z i) := by
    rintro _ ⟨j,hj,rfl⟩ f
    by_contra hn
    have := Weight.isIso_of_nonzero (hs j) (hs i) f hn
    exact hi (hd j i ⟨asIso f⟩ ▸ hj)
  have disj s i (h : T s (Z i)) (h' : F s (Z i)) : False :=
    (hs i).1 ((IsZero.iff_id_eq_zero _).2 ((hp s).1 (𝟙 _) h h'))
  let c := affineCoordinates b ∘ p
  let _ := coordinateZariski c
  have pull (U : Set (VertexRepresentation (k := k) d P.vertex)) (hU : @IsOpen _ (zariski b) U) :
      IsOpen (p ⁻¹' U) := by
    obtain ⟨V,hV,rfl⟩ := hU
    exact ⟨V,hV,rfl⟩
  have hsingle (i : L) : IsOpen ({i} : Set L) := by
    rcases ho with h | h
    · convert pull _ (h d (T {i}) (F {i}) (hp _) (ht _)) using 1
      ext j
      exact ⟨htmem _ j,fun hj ↦ by_contra fun hn ↦ disj _ j hj (hfmem _ j hn)⟩
    · convert pull _ (h d (T {i}ᶜ) (F {i}ᶜ) (hp _) (hf _)) using 1
      ext j
      exact ⟨fun hj ↦ hfmem _ j (fun hn ↦ hn hj),fun hj ↦ by_contra fun hn ↦ disj _ j (htmem _ j hn) hj⟩
  exact Finite.of_finite_univ (coordinateZariski_finite_open_fibers c id Set.univ
    (fun x _ ↦ ⟨x,rfl⟩) (fun i _ ↦ hsingle i))

private theorem isEFinite_of_open_loci [Infinite k] (ho : P.OpenTorsionLoci b ∨ P.OpenTorsionFreeLoci b) :
    IsEFinite R := by
  classical
  apply (isEFinite_iff_dim_stab k).2
  intro g q
  let θ := projectiveClassWeight (R := R) k g
  let s := stableClassesOfClass θ (classOfCompositionVector k q)
  choose B hB hc hs using fun x : s ↦ x.property
  choose p h using fun x : s ↦ P.exists_point_of_class (B x) q (hc x)
  let f (x : s) := (h x).some
  have := P.finite_stable_family_of_open_loci b _ p θ (fun x ↦ (hs x).of_iso (f x).symm)
    (fun x y ⟨e⟩ ↦ Subtype.ext ((hB x).symm.trans ((congr_toSkeleton_of_iso ((f x).symm ≪≫ e ≪≫ f y)).trans (hB y)))) ho
  exact Set.toFinite s

theorem isEFinite_iff_open_torsion [Infinite k] : IsEFinite R ↔ P.OpenTorsionLoci b :=
  ⟨P.openTorsionLoci_of_isEFinite b,fun h ↦ P.isEFinite_of_open_loci b (.inl h)⟩

theorem isEFinite_iff_open_torsionFree [Infinite k] : IsEFinite R ↔ P.OpenTorsionFreeLoci b :=
  ⟨P.openTorsionFreeLoci_of_isEFinite b,fun h ↦ P.isEFinite_of_open_loci b (.inr h)⟩

end VertexRepresentation.SplitBasicVertices

open VertexRepresentation in
/-- The right-module torsion and torsion-free openness characterizations,
computed in any chosen Morita equivalent split basic presentation. -/
theorem isEFinite_iff_open_torsion_loci
    {K A S I J : Type u} [Field K] [Infinite K] [Ring A] [Ring S] [Algebra K A] [Algebra K S]
    [Module.Finite K A] [Module.Finite K S] [Fintype I] [DecidableEq I] [Fintype J]
    (E : FGModuleCat.{u} Aᵐᵒᵖ ≌ FGModuleCat.{u} S)
    (P : SplitBasicVertices K S I) (b : Module.Basis J K S) :
    letI := IsNoetherianRing.of_finite K Aᵐᵒᵖ
    letI := IsNoetherianRing.of_finite K S
    (IsEFinite Aᵐᵒᵖ ↔ P.OpenTorsionLoci b) ∧ (IsEFinite Aᵐᵒᵖ ↔ P.OpenTorsionFreeLoci b) := by
  let _ := IsNoetherianRing.of_finite K Aᵐᵒᵖ
  let _ := IsNoetherianRing.of_finite K S
  let _ := IsArtinianRing.of_finite K Aᵐᵒᵖ
  let _ := IsArtinianRing.of_finite K S
  have h := isEFinite_iff_of_module_equivalence K K E
  exact ⟨h.trans (P.isEFinite_iff_open_torsion b),h.trans (P.isEFinite_iff_open_torsionFree b)⟩

end EFiniteCharacterizations
