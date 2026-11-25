module

public import EFiniteCharacterizations.LargeModules.GenericGrain
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Order.Zorn

/-! # Simultaneous solutions of linear equations in an endofinite module -/

@[expose] public section

namespace EFiniteCharacterizations

section Compactness

variable {E M ι : Type*} [Ring E] [AddCommGroup M] [Module E M]

local notation "A" => AffineSubspace E (ι → M)

private def HasFiniteSolutions (S : Set A) : Prop :=
  ∀ t : Finset A, ↑t ⊆ S → ∃ x, ∀ B ∈ t, x ∈ B

private theorem chain_hasFiniteSolutions {c : Set (Set A)} (hn : c.Nonempty)
    (hc : IsChain (· ⊆ ·) c) (hall : ∀ S ∈ c, HasFiniteSolutions S) :
    HasFiniteSolutions (⋃₀ c) := by
  classical
  intro t ht
  have covers (s : Finset A) (hs : (s : Set A) ⊆ ⋃₀ c) : ∃ S ∈ c, (s : Set A) ⊆ S := by
    induction s using Finset.induction_on with
    | empty => exact hn.imp fun S hS ↦ ⟨hS,by simp⟩
    | insert a s _ ih =>
      obtain ⟨U,hU,ha⟩ := hs (Finset.mem_insert_self a s)
      obtain ⟨V,hV,hsub⟩ := ih (fun z hz ↦ hs (Finset.mem_insert_of_mem hz))
      rcases hc.total hU hV with huv | hvu
      · exact ⟨V,hV,by simpa only [Finset.coe_insert,Set.insert_subset_iff] using And.intro (huv ha) hsub⟩
      · exact ⟨U,hU,by simpa only [Finset.coe_insert,Set.insert_subset_iff] using And.intro ha (hsub.trans hvu)⟩
  obtain ⟨S,hS,hsub⟩ := covers t ht
  exact hall S hS t hsub

private def coordinateFiber (i : ι) (a : M) : A :=
  (AffineSubspace.mk' a (⊥ : Submodule E M)).comap (LinearMap.proj i).toAffineMap

private theorem mem_coordinateFiber (i : ι) (a : M) (x : ι → M) :
    x ∈ coordinateFiber (E := E) i a ↔ x i = a := by
  change x i - a ∈ (⊥ : Submodule E M) ↔ _
  exact sub_eq_zero

/-- The Artinian condition lets us fix one more coordinate without losing finite
solvability. Among all finite tests choose one whose projected solution space
has minimal direction. Further tests can no longer shrink that projection. -/
private theorem exists_coordinate_value [IsArtinian E M] (i : ι) (S : Set A)
    (hs : HasFiniteSolutions S) :
    ∃ a : M, HasFiniteSolutions (insert (coordinateFiber i a) S) := by
  classical
  let D := {t : Finset A // ↑t ⊆ S}
  let sol (t : D) : A := ⨅ B : t.val, B.val
  have mem (t : D) (x : ι → M) : x ∈ sol t ↔ ∀ B ∈ t.val, x ∈ B := by
    simp only [sol,AffineSubspace.mem_iInf_iff,Subtype.forall]
  let F := (LinearMap.proj i : (ι → M) →ₗ[E] M).toAffineMap
  let proj (t : D) := (sol t).map F
  have nonempty (t : D) : ((proj t : AffineSubspace E M) : Set M).Nonempty := by
    obtain ⟨x,hx⟩ := hs t t.property
    exact ⟨_,AffineSubspace.mem_map_of_mem F ((mem t x).2 hx)⟩
  have hD : Nonempty D := ⟨⟨∅,by simp⟩⟩
  obtain ⟨_,⟨t,rfl⟩,hmin⟩ := wellFounded_lt.has_min
    (Set.range fun t : D ↦ (proj t).direction) (Set.range_nonempty _)
  obtain ⟨a,ha⟩ := nonempty t
  refine ⟨a,fun v hv ↦ ?_⟩
  let B := coordinateFiber (E := E) i a
  let u : D := ⟨t.val ∪ v.erase B,by
    intro W hW
    rcases Finset.mem_union.mp hW with h | h
    · exact t.property h
    · exact (hv (Finset.mem_of_mem_erase h)).resolve_left (Finset.ne_of_mem_erase h)⟩
  have hle : proj u ≤ proj t := AffineSubspace.map_mono F fun x hx ↦
    (mem t x).2 fun W hW ↦ (mem u x).1 hx W (Finset.mem_union_left _ hW)
  have he : proj u = proj t := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    ((AffineSubspace.direction_le hle).eq_of_not_lt (hmin _ ⟨u,rfl⟩)) (nonempty u) hle
  obtain ⟨x,hx,hxi⟩ := AffineSubspace.mem_map.mp (he.symm ▸ ha : a ∈ proj u)
  refine ⟨x,fun W hW ↦ ?_⟩
  by_cases h : W = B
  · subst W
    exact (mem_coordinateFiber i a x).2 hxi
  · exact (mem u x).1 hx _ (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h,hW⟩))

/-- For a product of Artinian modules, a finitely satisfiable family of affine
conditions has a point approximated on every finite coordinate set by solutions
to each condition. In particular all closed affine conditions hold there. -/
theorem exists_finite_agreement_of_artinian [IsArtinian E M] (S : Set A)
    (hs : ∀ t : Finset A, ↑t ⊆ S → ∃ x, ∀ B ∈ t, x ∈ B) :
    ∃ x : ι → M, ∀ B ∈ S, ∀ t : Finset ι, ∃ y ∈ B, ∀ i ∈ t, y i = x i := by
  classical
  obtain ⟨T,hST,hmax⟩ := zorn_subset_nonempty {T : Set A | HasFiniteSolutions T}
    (fun c hc hchain hn ↦ ⟨⋃₀ c,chain_hasFiniteSolutions hn hchain hc,fun _ ↦ Set.subset_sUnion_of_mem⟩)
    S hs
  have coord (i : ι) : ∃ a : M, coordinateFiber (E := E) i a ∈ T := by
    obtain ⟨a,ha⟩ := exists_coordinate_value i T hmax.prop
    exact ⟨a,hmax.le_of_ge ha (Set.subset_insert ..) (Set.mem_insert ..)⟩
  choose x hx using coord
  refine ⟨x,fun B hB t ↦ ?_⟩
  let v := t.image (fun i ↦ coordinateFiber (E := E) i (x i))
  have hv : (↑(insert B v) : Set A) ⊆ T := by
    simp only [v,Finset.coe_insert,Finset.coe_image,Set.insert_subset_iff,Set.image_subset_iff]
    exact ⟨hST hB,fun i _ ↦ hx i⟩
  obtain ⟨y,hy⟩ := hmax.prop (insert B v) hv
  exact ⟨y,hy B (Finset.mem_insert_self ..),fun i hi ↦ (mem_coordinateFiber i (x i) y).1
    (hy _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi)))⟩

end Compactness

section Extension

open scoped ModuleCat.Algebra

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {N : ModuleCat R}
    (U : Submodule R V) (f : U →ₗ[R] N)

/-- Assignments agreeing on a finite span with a linear map extending the
prescribed values. The map on the span may vary with the assignment. -/
private def extensionTest (B : Submodule R V) :
    AffineSubspace (Module.End R N) (V → N) where
  carrier := {x | ∃ h : B →ₗ[R] N, (∀ z : B, x z = h z) ∧
    ∀ z : U, ∀ hz : z.val ∈ B, h ⟨z.val,hz⟩ = f z}
  smul_vsub_vadd_mem' a := by
    rintro x y z ⟨p,hp,hp'⟩ ⟨q,hq,hq'⟩ ⟨r,hr,hr'⟩
    refine ⟨a.comp (p-q) + r,fun t ↦ ?_,fun t ht ↦ ?_⟩
    · change a (x t - y t) + z t = a (p t - q t) + r t
      rw [hp,hq,hr]
    · change a (p _ - q _) + r _ = _
      rw [hp',hq',hr',sub_self,map_zero,zero_add]

private theorem extensionTest_antitone : Antitone (extensionTest U f) := by
  rintro B D h x ⟨g,hg,he⟩
  exact ⟨g.comp (Submodule.inclusion h),fun t ↦ hg ⟨_,h t.property⟩,fun t ht ↦ he t (h ht)⟩

/-- A map from a submodule into an endofinite module extends to the whole
ambient module if it extends on the intersection with every finitely generated
submodule. The ambient module can have arbitrary dimension. -/
theorem IsEndofinite.extend_of_finite_spans (hn : IsEndofinite N)
    (localExt : ∀ B : Submodule R V, B.FG → ∃ h : B →ₗ[R] N,
      ∀ z : U, ∀ hz : z.val ∈ B, h ⟨z.val,hz⟩ = f z) :
    ∃ h : V →ₗ[R] N, h.comp U.subtype = f := by
  classical
  let : IsArtinian (Module.End R N) N := (isFiniteLength_iff_isNoetherian_isArtinian.mp hn).2
  let B (s : Finset V) := Submodule.span R (s : Set V)
  let T (s : Finset V) := extensionTest U f (B s)
  have hT (s : Finset V) : (T s : Set (V → N)).Nonempty := by
    obtain ⟨g,hg⟩ := localExt (B s) (Submodule.fg_span s.finite_toSet)
    refine ⟨fun x ↦ if h : x ∈ B s then g ⟨x,h⟩ else 0,g,fun x ↦ ?_,hg⟩
    simp [x.property]
  have hfin (t : Finset (AffineSubspace (Module.End R N) (V → N)))
      (ht : (t : Set _) ⊆ Set.range T) : ∃ x, ∀ A ∈ t, x ∈ A := by
    choose s hs using fun A : t ↦ ht A.property
    let v := Finset.univ.biUnion s
    obtain ⟨x,hx⟩ := hT v
    refine ⟨x,fun A hA ↦ ?_⟩
    rw [← show T (s ⟨A,hA⟩) = A from hs ⟨A,hA⟩]
    apply extensionTest_antitone U f (Submodule.span_mono ?_) hx
    exact fun a ha ↦ Finset.mem_biUnion.mpr ⟨⟨A,hA⟩,Finset.mem_univ _,ha⟩
  obtain ⟨x,hx⟩ := exists_finite_agreement_of_artinian (Set.range T) hfin
  have localMap (s : Finset V) : ∃ g : B s →ₗ[R] N,
      (∀ z : U, ∀ hz : z.val ∈ B s, g ⟨z.val,hz⟩ = f z) ∧
      ∀ z, ∀ hz : z ∈ s, x z = g ⟨z,Submodule.subset_span hz⟩ := by
    obtain ⟨y,⟨g,hy,he⟩,hxy⟩ := hx (T s) ⟨s,rfl⟩ s
    exact ⟨g,he,fun z hz ↦ (hxy z hz).symm.trans (hy ⟨z,Submodule.subset_span hz⟩)⟩
  let h : V →ₗ[R] N :=
    { toFun := x
      map_add' a b := by
        obtain ⟨g,_,hg⟩ := localMap {a,b,a+b}
        rw [hg a (by simp),hg b (by simp),hg (a+b) (by simp)]
        rw [← g.map_add]; rfl
      map_smul' r a := by
        obtain ⟨g,_,hg⟩ := localMap {a,r • a}
        rw [hg a (by simp),hg (r • a) (by simp)]
        change _ = r • g _
        rw [← g.map_smul]; rfl }
  refine ⟨h,LinearMap.ext fun z ↦ ?_⟩
  obtain ⟨g,he,hg⟩ := localMap {z.val}
  exact (hg _ (Finset.mem_singleton_self _)).trans (he z _)

end Extension

end EFiniteCharacterizations
