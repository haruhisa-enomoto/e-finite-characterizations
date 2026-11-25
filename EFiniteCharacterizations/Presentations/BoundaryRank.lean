module

public import EFiniteCharacterizations.Presentations.RigidPencil
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Rank of homotopy boundaries under an isomorphism of differentials -/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

namespace EFiniteCharacterizations

private theorem finrank_range_eq_of_conjugate {k U U' V V' : Type*} [Field k]
    [AddCommGroup U] [AddCommGroup U'] [AddCommGroup V] [AddCommGroup V']
    [Module k U] [Module k U'] [Module k V] [Module k V']
    (f : U →ₗ[k] V) (g : U' →ₗ[k] V') (a : U ≃ₗ[k] U') (b : V ≃ₗ[k] V')
    (h : ∀ x, g (a x) = b (f x)) :
    Module.finrank k (LinearMap.range g) = Module.finrank k (LinearMap.range f) := by
  have hc : g.comp a.toLinearMap = b.toLinearMap.comp f := LinearMap.ext h
  have hr := congrArg LinearMap.range hc
  rw [LinearMap.range_comp_of_range_eq_top _ a.range, LinearMap.range_comp] at hr
  rw [hr]
  exact b.finrank_map_eq _

variable (k : Type*) [Field k] {C : Type*} [Category C] [Preadditive C] [Linear k C]

/-- Isomorphic source differentials give the same rank of the homotopy boundary. -/
theorem boundaryLinear_rank_eq_of_source_iso {X Y X' Y' A B : C}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (q : A ⟶ B) (a : X ≅ X') (b : Y ≅ Y')
    (e : a.hom ≫ p' = p ≫ b.hom) :
    Module.finrank k (LinearMap.range (boundaryLinear k p q)) =
      Module.finrank k (LinearMap.range (boundaryLinear k p' q)) := by
  apply finrank_range_eq_of_conjugate (boundaryLinear k p' q) (boundaryLinear k p q)
    ((Linear.homCongr k a.symm (Iso.refl A)).prodCongr (Linear.homCongr k b.symm (Iso.refl B)))
    (Linear.homCongr k a.symm (Iso.refl B))
  intro f
  simp only [boundaryLinear_apply, LinearEquiv.prodCongr_apply, Linear.homCongr_apply,
    Iso.symm_inv, Iso.refl_hom, Category.comp_id, Preadditive.comp_sub, Category.assoc]
  rw [← Category.assoc p b.hom, ← e, Category.assoc]

/-- Isomorphic target differentials give the same rank of the homotopy boundary. -/
theorem boundaryLinear_rank_eq_of_target_iso {X Y X' Y' A B : C}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (q : A ⟶ B) (a : X ≅ X') (b : Y ≅ Y')
    (e : a.hom ≫ p' = p ≫ b.hom) :
    Module.finrank k (LinearMap.range (boundaryLinear k q p')) =
      Module.finrank k (LinearMap.range (boundaryLinear k q p)) := by
  apply finrank_range_eq_of_conjugate (boundaryLinear k q p) (boundaryLinear k q p')
    ((Linear.homCongr k (Iso.refl A) a).prodCongr (Linear.homCongr k (Iso.refl B) b))
    (Linear.homCongr k (Iso.refl A) b)
  intro f
  simp only [boundaryLinear_apply, LinearEquiv.prodCongr_apply, Linear.homCongr_apply,
    Iso.refl_inv, Category.id_comp, Preadditive.sub_comp, Category.assoc, e]

theorem boundaryLinear_add_smul {X Y A B : C} (p r : X ⟶ Y) (q s : A ⟶ B) (a : k) :
    boundaryLinear k (p + a • r) (q + a • s) =
      boundaryLinear k p q + a • boundaryLinear k r s := by
  apply LinearMap.ext
  intro x
  simp only [boundaryLinear_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Preadditive.comp_add, Preadditive.add_comp, Linear.smul_comp, Linear.comp_smul, smul_sub]
  abel

variable (F : Type*) [Field F] [Algebra k F]

/-- A boundary after extending its two differentials is the scalar extension
of the original boundary under the product comparison. -/
theorem boundaryLinear_scalarExtension {X Y A B : C} (p : X ⟶ Y) (q : A ⟶ B) :
    let G : C ⥤ ScalarCategory k F C := ScalarCategory.of
    let E := TensorProduct.prodRight k F F (X ⟶ A) (Y ⟶ B)
    (boundaryLinear F (G.map p) (G.map q)).comp E.toLinearMap = (boundaryLinear k p q).baseChange F := by
  let G : C ⥤ ScalarCategory k F C := ScalarCategory.of
  let E := TensorProduct.prodRight k F F (X ⟶ A) (Y ⟶ B)
  let f : ((F ⊗[k] (X ⟶ A)) × (F ⊗[k] (Y ⟶ B))) →ₗ[F] F ⊗[k] (X ⟶ B) :=
    boundaryLinear F (G.map p) (G.map q)
  change f.comp E.toLinearMap = (boundaryLinear k p q).baseChange F
  apply TensorProduct.AlgebraTensorModule.ext
  intro s x
  simp only [f, boundaryLinear_apply, LinearMap.baseChange_tmul]
  change ScalarCategory.compLinear (s ⊗ₜ[k] x.1) ((1 : F) ⊗ₜ[k] q) -
    ScalarCategory.compLinear ((1 : F) ⊗ₜ[k] p) (s ⊗ₜ[k] x.2) =
      s ⊗ₜ[k] (x.1 ≫ q - p ≫ x.2)
  simp [ScalarCategory.compLinear, TensorProduct.tmul_sub]

/-- Extension of the Hom spaces along a field extension preserves and
reflects surjectivity of a boundary. -/
theorem boundaryLinear_scalarExtension_surjective_iff {X Y A B : C} (p : X ⟶ Y) (q : A ⟶ B) :
    let G : C ⥤ ScalarCategory k F C := ScalarCategory.of
    Function.Surjective (boundaryLinear F (G.map p) (G.map q)) ↔
      Function.Surjective (boundaryLinear k p q) := by
  let G : C ⥤ ScalarCategory k F C := ScalarCategory.of
  let E := TensorProduct.prodRight k F F (X ⟶ A) (Y ⟶ B)
  let D := boundaryLinear F (G.map p) (G.map q)
  have h : D.comp E.toLinearMap = (boundaryLinear k p q).baseChange F :=
    boundaryLinear_scalarExtension k F p q
  change Function.Surjective D ↔ _
  rw [← Module.FaithfullyFlat.lTensor_surjective_iff_surjective k F (boundaryLinear k p q)]
  change Function.Surjective D ↔ Function.Surjective ((boundaryLinear k p q).baseChange F)
  rw [← h]
  exact ⟨fun H ↦ H.comp E.surjective, fun H ↦ Function.Surjective.of_comp H⟩

/-- The range of a boundary on an affine pair of differentials is the range
of the corresponding affine pencil of linear maps on the extended Hom spaces. -/
theorem boundaryLinear_scalarExtension_affine_range {X Y A B : C}
    (p p' : X ⟶ Y) (q q' : A ⟶ B) (s : F) :
    let G : C ⥤ ScalarCategory k F C := ScalarCategory.of
    LinearMap.range (boundaryLinear F (G.map p + s • G.map p') (G.map q + s • G.map q')) =
      LinearMap.range ((boundaryLinear k p q).baseChange F + s • (boundaryLinear k p' q').baseChange F) := by
  let G : C ⥤ ScalarCategory k F C := ScalarCategory.of
  let E := TensorProduct.prodRight k F F (X ⟶ A) (Y ⟶ B)
  let f : ((F ⊗[k] (X ⟶ A)) × (F ⊗[k] (Y ⟶ B))) →ₗ[F] F ⊗[k] (X ⟶ B) :=
    boundaryLinear F (G.map p + s • G.map p') (G.map q + s • G.map q')
  let d : ((F ⊗[k] (X ⟶ A)) × (F ⊗[k] (Y ⟶ B))) →ₗ[F] F ⊗[k] (X ⟶ B) :=
    boundaryLinear F (G.map p) (G.map q)
  let d' : ((F ⊗[k] (X ⟶ A)) × (F ⊗[k] (Y ⟶ B))) →ₗ[F] F ⊗[k] (X ⟶ B) :=
    boundaryLinear F (G.map p') (G.map q')
  change LinearMap.range f = _
  have hf : f = d + s • d' := boundaryLinear_add_smul F _ _ _ _ s
  have hd : d.comp E.toLinearMap = (boundaryLinear k p q).baseChange F :=
    boundaryLinear_scalarExtension k F p q
  have hd' : d'.comp E.toLinearMap = (boundaryLinear k p' q').baseChange F :=
    boundaryLinear_scalarExtension k F p' q'
  rw [← LinearMap.range_comp_of_range_eq_top f E.range, hf, LinearMap.add_comp, LinearMap.smul_comp, hd, hd']

end EFiniteCharacterizations
