module

public import EFiniteCharacterizations.LargeModules.EndofiniteLocal
public import EFiniteCharacterizations.LargeModules.GrainTorsionPair

/-! # Finite cogeneration tests for an endofinite module -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u
namespace EFiniteCharacterizations

variable {R : Type u} [Ring R]

/-- Common kernel of all maps to M. Precomposition preserves the family of
maps, so the common kernel is a submodule over the endomorphism ring of N. -/
private def commonKernel (N M : ModuleCat.{u} R) : Submodule (Module.End R N) N where
  carrier := {x | ∀ f : N →ₗ[R] M, f x = 0}
  zero_mem' _ := map_zero _
  add_mem' := fun hx hy f ↦ by rw [map_add,hx f,hy f,add_zero]
  smul_mem' := fun a _ hx f ↦ hx (f.comp a)

private theorem injective_evaluation (N M : ModuleCat.{u} R) (h : commonKernel N M = ⊥) :
    Function.Injective (LinearMap.pi (fun f : N →ₗ[R] M ↦ f)) := by
  apply (injective_iff_map_eq_zero _).2
  intro x hx
  apply (Submodule.mem_bot (Module.End R N)).mp
  rw [← h]
  exact fun f ↦ congrFun hx f

/-- If every indecomposable summand is finitely generated, a single finitely
generated module has the same cogeneration tests as N. Each module embeds in
a product of copies of the other. -/
theorem IsEndofinite.exists_fg_mutual_embeddings {N : ModuleCat.{u} R} (hN : IsEndofinite N)
    (hs : ∀ (G : ModuleCat.{u} R), Retract G N → Indecomposable G → Module.Finite R G) :
    ∃ M : FGModuleCat.{u} R,
      Function.Injective (LinearMap.pi (fun f : N →ₗ[R] M ↦ f)) ∧
      Function.Injective (LinearMap.pi (fun f : M →ₗ[R] N ↦ f)) := by
  classical
  let : IsArtinian (Module.End R N) N := (isFiniteLength_iff_isNoetherian_isArtinian.mp hN).2
  let C := {U : Submodule (Module.End R N) N | ∃ M : FGModuleCat.{u} R,
    U = commonKernel N M.obj ∧ Function.Injective (LinearMap.pi (fun f : M →ₗ[R] N ↦ f))}
  let Z := FGModuleCat.of R (⊥ : Submodule R N)
  have hC : C.Nonempty := ⟨_,Z,rfl,fun _ _ _ ↦ Subsingleton.elim ..⟩
  obtain ⟨U,⟨M,rfl,hM⟩,hmin⟩ := wellFounded_lt.has_min C hC
  refine ⟨M,injective_evaluation N M.obj (eq_bot_iff.mpr ?_),hM⟩
  intro x hx
  by_contra hn
  have hne : x ≠ 0 := fun hz ↦ hn ((Submodule.mem_bot _).2 hz)
  obtain ⟨G,r,hi,hxG⟩ := hN.exists_indecomposable_retract x hne
  let := hs G r hi
  let B := FGModuleCat.of R (M × G)
  have hB : Function.Injective (LinearMap.pi (fun f : B →ₗ[R] N ↦ f)) := by
    intro a b h
    apply Prod.ext
    · exact hM (funext fun f ↦ congrFun h (f.comp (LinearMap.fst R M G)))
    · have eq := congrFun h (r.i.hom.comp (LinearMap.snd R M G))
      have ri (z : G) : r.r.hom (r.i.hom z) = z :=
        LinearMap.congr_fun (congrArg ModuleCat.Hom.hom r.retract) z
      exact (ri a.2).symm.trans ((congrArg r.r.hom eq).trans (ri b.2))
  have le : commonKernel N B.obj ≤ commonKernel N M.obj := by
    intro z hz f
    exact congrArg Prod.fst (hz ((LinearMap.inl R M G).comp f))
  have eq := le.eq_of_not_lt (hmin _ ⟨B,rfl,hB⟩)
  have hx' : x ∈ commonKernel N B.obj := eq.symm ▸ hx
  exact hxG (congrArg Prod.snd (hx' ((LinearMap.inr R M G).comp r.r.hom)))

/-- An endofinite splitting witness either has the same finite cogenerated
modules and left perpendicular as one finite module, or has a generic grain
as an indecomposable summand. -/
theorem finite_cogenerator_or_grain_retract [IsArtinianRing R] (k : Type u) [Field k]
    [Algebra k R] {N : ModuleCat.{u} R} (he : IsEndofinite N) (hs : SplitsOnCogeneratedModules k N) :
    (∃ M : FGModuleCat.{u} R, perpendicularToModule N = perpendicularToModule M.obj ∧
      cogeneratedByModule N = cogeneratedByModule M.obj) ∨
      ∃ G : ModuleCat.{u} R, Nonempty (Retract G N) ∧ IsGenericGrain k G := by
  classical
  by_cases h : ∀ (G : ModuleCat.{u} R), Retract G N → Indecomposable G → Module.Finite k G
  · obtain ⟨M,hn,hm⟩ := he.exists_fg_mutual_embeddings (fun G r hi ↦ by
      let := h G r hi
      exact Module.Finite.of_restrictScalars_finite k R G)
    exact Or.inl ⟨M,le_antisymm (perp_le_of_product_embedding _ hm) (perp_le_of_product_embedding _ hn),
      le_antisymm (cogeneratedByModule_le_of_product_embedding _ hn) (cogeneratedByModule_le_of_product_embedding _ hm)⟩
  · push Not at h
    obtain ⟨G,r,hi,hf⟩ := h
    exact Or.inr ⟨G,⟨r⟩,isGenericGrain_of_retract k r he hs hf hi⟩

end EFiniteCharacterizations
