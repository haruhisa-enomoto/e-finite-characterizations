module

public import EFiniteCharacterizations.Geometry.VertexDifferentialMatrix
public import EFiniteCharacterizations.Stability.GroundStableDeterminant

/-! # A common inversion chart on one list of vertex summands -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ModuleCat.Algebra
universe u
namespace EFiniteCharacterizations.VertexRepresentation.SplitBasicVertices

variable {k R I : Type u} [Field k] [Ring R] [Algebra k R] [Fintype I] [DecidableEq I]
    (P : SplitBasicVertices k R I)

/-- Flatten a biproduct of copies of a vertex term into one indexed vertex term. -/
noncomputable def copiesVertexTermIso {S : Type u} [Fintype S] [DecidableEq S] (s : S → I) (n : ℕ) :
    (⨁ fun _ : Fin n ↦ (P.vertexTerm s).val) ≅
      (P.vertexTerm (fun j : Σ _ : Fin n, S ↦ s j.2)).val := by
  let A := (P.vertexTerm s).val
  let F := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  let _ : PreservesBiproduct (fun _ : Fin n ↦ A) F := preservesBiproduct_of_preservesCoproduct F
  let f := (F.mapBiproduct (fun _ : Fin n ↦ A)).trans (ModuleCat.biproductIsoPi (fun _ : Fin n ↦ A.obj))
  let l := f.toLinearEquiv ≪≫ₗ (LinearEquiv.piCurry R (fun (_ : Fin n) j ↦ vertexIdeal P.vertex (s j))).symm
  let : Module.Finite R (F.obj (⨁ fun _ : Fin n ↦ A)) := (⨁ fun _ : Fin n ↦ A : FGModuleCat R).property
  exact l.toFGModuleCatIso

variable [IsNoetherianRing R] [Module.Finite k R]

/-- Over an algebraically closed field, one differential between actual
vertex terms has infinitely many stable inverting classes of one fixed class. -/
theorem exists_explicit_vertex_chart [IsAlgClosed k] (hn : ¬ IsEFinite R) :
    ∃ (S T : Type u) (_ : Fintype S) (_ : DecidableEq S) (_ : Fintype T) (_ : DecidableEq T)
      (s : S → I) (t : T → I) (p : (P.vertexTerm t).val ⟶ (P.vertexTerm s).val)
      (θ : Weight (FGModuleCat.{u} R)) (c : GrothendieckGroup (FGModuleCat.{u} R)),
      let Q := TwoTerm.mk (P.vertexTerm t).val (P.vertexTerm s).val (P.vertexTerm t).property
        (P.vertexTerm s).property p
      (Q.stableInvertingClasses k ∩ stableClassesOfClass θ c).Infinite := by
  classical
  obtain ⟨g,n,p,c,hc⟩ := P.exists_infinite_vertex_chart hn
  let w := P.characterExponents g
  let s := (Sigma.fst : vertexCopies (fun i ↦ (w i).toNat) → I)
  let t := (Sigma.fst : vertexCopies (fun i ↦ (-w i).toNat) → I)
  let A := (P.vertexPresentation g).blockDifferentialOnCopies p
  let es := P.copiesVertexTermIso s n
  let et := P.copiesVertexTermIso t n
  let S := Σ _ : Fin n, vertexCopies (fun i ↦ (w i).toNat)
  let T := Σ _ : Fin n, vertexCopies (fun i ↦ (-w i).toNat)
  let s' (j : S) := s j.2
  let t' (j : T) := t j.2
  let q := et.inv ≫ A.differential ≫ es.hom
  let B := TwoTerm.mk (P.vertexTerm t').val (P.vertexTerm s').val (P.vertexTerm t').property
    (P.vertexTerm s').property q
  have hg : B.projectiveClass = A.projectiveClass :=
    congrArg₂ (· - ·) (ProjectiveClass.of_eq_of_iso _ _ es.symm) (ProjectiveClass.of_eq_of_iso _ _ et.symm)
  have hw : B.eulerWeight k = A.eulerWeight k := by
    rw [← B.projectiveClassWeight_eq_eulerWeight k,← A.projectiveClassWeight_eq_eulerWeight k,hg]
  refine ⟨S,T,inferInstance,inferInstance,inferInstance,inferInstance,s',t',q,projectiveClassWeight k g,c,hc.mono ?_⟩
  rintro z ⟨⟨X,hX,hs,hi⟩,hz⟩
  refine ⟨⟨X,hX,hw.symm ▸ hs,?_⟩,hz⟩
  apply TwoTerm.invertedOn_of_commuting_isos (P := B) (Q := A) et.symm es.symm _ hi
  change (et.inv ≫ A.differential ≫ es.hom) ≫ es.inv = et.inv ≫ A.differential
  exact (Category.assoc _ _ _).trans (congrArg (et.inv ≫ ·) ((Category.assoc A.differential es.hom es.inv).trans ((congrArg (A.differential ≫ ·) es.hom_inv_id).trans (Category.comp_id _))))

variable {S T : Type u} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (s : S → I) (t : T → I) (p : (P.vertexTerm t).val ⟶ (P.vertexTerm s).val)

noncomputable abbrev chartComplex := TwoTerm.mk (P.vertexTerm t).val (P.vertexTerm s).val
  (P.vertexTerm t).property (P.vertexTerm s).property p

private theorem square_of_stable {d : I → ℕ} (x : VertexRepresentation (k := k) d P.vertex)
    (hs : ((chartComplex P s t p).eulerWeight k).IsStable x.moduleObj) :
    Nonempty ((Σ j, Fin (d (s j))) ≃ (Σ j, Fin (d (t j)))) := by
  apply Fintype.card_eq.mp
  have h := hs.2.1
  rw [TwoTerm.eulerWeight_eval,sub_eq_zero,homFinrank_eq_finrank,homFinrank_eq_finrank] at h
  change (Module.finrank k ((P.vertexTerm s).val ⟶ x.moduleObj) : ℤ) =
    Module.finrank k ((P.vertexTerm t).val ⟶ x.moduleObj) at h
  rw [(P.termCoordinates s x).finrank_eq,(P.termCoordinates t x).finrank_eq,
    Module.finrank_pi,Module.finrank_pi] at h
  exact_mod_cast h

theorem exists_stable_points_on_component {J : Type u} [Fintype J] (b : Module.Basis J k R)
    {θ : Weight (FGModuleCat.{u} R)} {c : GrothendieckGroup (FGModuleCat.{u} R)}
    (hi : ((chartComplex P s t p).stableInvertingClasses k ∩ stableClassesOfClass θ c).Infinite) :
    ∃ (d : I → ℕ) (h : (Σ j, Fin (d (s j))) ≃ (Σ j, Fin (d (t j))))
      (x y : VertexRepresentation (k := k) d P.vertex),
      let Q := chartComplex P s t p
      let g := vertexBlockDeterminant b d P.vertex s t (P.differentialEntries s t p) h
      (∃ C ∈ @irreducibleComponents _ (zariski (d := d) (e := P.vertex) b), x ∈ C ∧ y ∈ C) ∧
      toSkeleton x.moduleObj ≠ toSkeleton y.moduleObj ∧
        (Q.eulerWeight k).IsStable x.moduleObj ∧ (Q.eulerWeight k).IsStable y.moduleObj ∧
        g.val.val x ≠ 0 ∧ g.val.val y ≠ 0 := by
  let := IsArtinianRing.of_finite k R
  classical
  obtain ⟨a,ha⟩ := hi.nonempty
  obtain ⟨M,_,hM,_⟩ := ha.2
  obtain ⟨q,hq⟩ := exists_compositionVector_of_module k M
  let d := q ∘ P.simpleIndex.symm
  let Q := chartComplex P s t p
  have point {v} (hv : v ∈ Q.stableInvertingClasses k ∩ stableClassesOfClass θ c) :
      ∃ x : VertexRepresentation (k := k) d P.vertex, toSkeleton x.moduleObj = v ∧
        (Q.eulerWeight k).IsStable x.moduleObj ∧ Q.InvertedOn x.moduleObj.obj := by
    obtain ⟨A,hA,hs,hinv⟩ := hv.1
    obtain ⟨B,hB,hc,_⟩ := hv.2
    obtain ⟨f⟩ := toSkeleton_eq_toSkeleton_iff.mp (hA.trans hB.symm)
    obtain ⟨x,⟨e⟩⟩ := P.exists_point_of_class A q
      ((GrothendieckGroup.of_eq_of_iso f).trans (hc.trans (hM.symm.trans hq.symm)))
    exact ⟨x,(congr_toSkeleton_of_iso e).trans hA,hs.of_iso e.symm,
      TwoTerm.invertedOn_of_iso ((forget₂ _ (ModuleCat.{u} R)).mapIso e) hinv⟩
  let X := VertexRepresentation (k := k) d P.vertex
  let := zariski (d := d) (e := P.vertex) b
  let : NoetherianSpace X := coordinateZariski_noetherian (affineCoordinates b)
  let A := Q.stableInvertingClasses k ∩ stableClassesOfClass θ c
  let : Infinite A := hi.to_subtype
  choose rep hrep using fun v : A ↦ point v.property
  let comp (v : A) : irreducibleComponents X :=
    ⟨irreducibleComponent (rep v), irreducibleComponent_mem_irreducibleComponents _⟩
  let := (NoetherianSpace.finite_irreducibleComponents (α := X)).to_subtype
  obtain ⟨i,j,hij,he⟩ := Finite.exists_ne_map_eq_of_infinite comp
  obtain ⟨hx,hsx,hix⟩ := hrep i
  obtain ⟨hy,hsy,hiy⟩ := hrep j
  obtain ⟨h⟩ := square_of_stable P s t p (rep i) hsx
  refine ⟨d,h,rep i,rep j,⟨(comp i).val,(comp i).property,mem_irreducibleComponent,?_⟩,
    fun eq ↦ hij (Subtype.ext (hx.symm.trans (eq.trans hy))),hsx,hsy,
    (P.vertexBlockDeterminant_ne_zero_iff s t _ b p h).2 hix,
    (P.vertexBlockDeterminant_ne_zero_iff s t _ b p h).2 hiy⟩
  rw [he]
  exact mem_irreducibleComponent

theorem exists_stable_points_on_determinant {J : Type u} [Fintype J] (b : Module.Basis J k R)
    {θ : Weight (FGModuleCat.{u} R)} {c : GrothendieckGroup (FGModuleCat.{u} R)}
    (hi : ((chartComplex P s t p).stableInvertingClasses k ∩ stableClassesOfClass θ c).Infinite) :
    ∃ (d : I → ℕ) (h : (Σ j, Fin (d (s j))) ≃ (Σ j, Fin (d (t j))))
      (x y : VertexRepresentation (k := k) d P.vertex),
      let Q := chartComplex P s t p
      let g := vertexBlockDeterminant b d P.vertex s t (P.differentialEntries s t p) h
      toSkeleton x.moduleObj ≠ toSkeleton y.moduleObj ∧
        (Q.eulerWeight k).IsStable x.moduleObj ∧ (Q.eulerWeight k).IsStable y.moduleObj ∧
        g.val.val x ≠ 0 ∧ g.val.val y ≠ 0 := by
  obtain ⟨d,h,x,y,_,hs⟩ := P.exists_stable_points_on_component s t p b hi
  exact ⟨d,h,x,y,hs⟩

end EFiniteCharacterizations.VertexRepresentation.SplitBasicVertices
