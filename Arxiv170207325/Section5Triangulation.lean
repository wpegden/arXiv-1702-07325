import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Finset.Insert
import PaperDefinitions

noncomputable section

namespace Arxiv170207325

/-- The common vertex set of two facets. -/
def SimplexFacet.commonVertices {n : ℕ} (τ₁ τ₂ : SimplexFacet n) : Finset (RentSimplex n) :=
  τ₁.vertices ∩ τ₂.vertices

@[simp]
theorem mem_commonVertices_iff {n : ℕ} {τ₁ τ₂ : SimplexFacet n} {v : RentSimplex n} :
    v ∈ τ₁.commonVertices τ₂ ↔ v ∈ τ₁.vertices ∧ v ∈ τ₂.vertices := by
  simp [SimplexFacet.commonVertices]

/-- One simplex is a subface of another when its vertices are a subset of the larger simplex's
vertices. -/
def SimplexFacet.IsSubfaceOf {n : ℕ} (σ τ : SimplexFacet n) : Prop :=
  σ.vertices ⊆ τ.vertices

@[simp]
theorem SimplexFacet.isSubfaceOf_refl {n : ℕ} (τ : SimplexFacet n) : τ.IsSubfaceOf τ :=
  Finset.Subset.refl _

theorem SimplexFacet.isSubfaceOf_trans {n : ℕ} {ρ σ τ : SimplexFacet n}
    (hρσ : ρ.IsSubfaceOf σ) (hστ : σ.IsSubfaceOf τ) : ρ.IsSubfaceOf τ :=
  hρσ.trans hστ

/-- The common face spanned by the shared vertices of two facets. -/
def SimplexFacet.commonFace {n : ℕ} (τ₁ τ₂ : SimplexFacet n) : SimplexFacet n where
  vertices := τ₁.commonVertices τ₂

theorem SimplexFacet.commonFace_isSubfaceLeft {n : ℕ} (τ₁ τ₂ : SimplexFacet n) :
    (τ₁.commonFace τ₂).IsSubfaceOf τ₁ := by
  intro v hv
  exact (mem_commonVertices_iff.mp hv).1

theorem SimplexFacet.commonFace_isSubfaceRight {n : ℕ} (τ₁ τ₂ : SimplexFacet n) :
    (τ₁.commonFace τ₂).IsSubfaceOf τ₂ := by
  intro v hv
  exact (mem_commonVertices_iff.mp hv).2

theorem SimplexFacet.commonVertices_subset_left {n : ℕ} (τ₁ τ₂ : SimplexFacet n) :
    τ₁.commonVertices τ₂ ⊆ τ₁.vertices :=
  (τ₁.commonFace_isSubfaceLeft τ₂)

theorem SimplexFacet.commonVertices_subset_right {n : ℕ} (τ₁ τ₂ : SimplexFacet n) :
  τ₁.commonVertices τ₂ ⊆ τ₂.vertices :=
  (τ₁.commonFace_isSubfaceRight τ₂)

theorem SimplexFacet.stdSimplexVertex_mem_vertices_of_mem_realization {n : ℕ}
    (τ : SimplexFacet n) (i : RoomIndex n)
    (hx : ((stdSimplex.vertex (S := ℝ) i : RentSimplex n) : RentCoordinates n) ∈ τ.realization) :
    stdSimplex.vertex (S := ℝ) i ∈ τ.vertices := by
  have hproj :
      ConvexOn ℝ (Set.univ : Set (RentCoordinates n)) (LinearMap.proj (R := ℝ) i) :=
    (LinearMap.proj (R := ℝ) i).convexOn convex_univ
  have hx' :
      ((stdSimplex.vertex (S := ℝ) i : RentSimplex n) : RentCoordinates n) ∈
        convexHull ℝ τ.pointSet := by
    simpa [SimplexFacet.realization] using hx
  obtain ⟨y, hyτ, hyge⟩ := hproj.exists_ge_of_mem_convexHull
    (t := τ.pointSet) (by intro y _; simp) hx'
  rcases hyτ with ⟨v, hv, rfl⟩
  have hcoord : (1 : ℝ) ≤ v i := by
    simpa using hyge
  have hEqCoord : v i = 1 := le_antisymm (stdSimplex.le_one v i) hcoord
  simpa [eq_stdSimplex_vertex_of_apply_eq_one hEqCoord] using hv

theorem SimplexTriangulation.mem_subset_of_vertex_mem_convexHull {n : ℕ}
    {T : SimplexTriangulation n} {τ : SimplexFacet n} (hτ : τ ∈ T.facets)
    {S : Finset (RentSimplex n)} (hS : S ⊆ τ.vertices) {v : RentSimplex n} (hv : v ∈ τ.vertices)
    (hx :
      ((v : RentSimplex n) : RentCoordinates n) ∈
        convexHull ℝ (((↑) : RentSimplex n → RentCoordinates n) '' (S : Set (RentSimplex n)))) :
    v ∈ S := by
  classical
  let p : τ.vertices → RentCoordinates n := fun x => ((x : RentSimplex n) : RentCoordinates n)
  let s : Set τ.vertices := {x | (x : RentSimplex n) ∈ S}
  let i : τ.vertices := ⟨v, hv⟩
  have hAffine : AffineIndependent ℝ p := T.facet_affineIndependent τ hτ
  have hs_image :
      p '' s = (((↑) : RentSimplex n → RentCoordinates n) '' (S : Set (RentSimplex n))) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x : RentSimplex n), hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hS hx⟩, by simpa [s], rfl⟩
  have hi_mem :
      p i ∈ affineSpan ℝ (p '' s) := by
    have hx' : p i ∈ convexHull ℝ (p '' s) := by
      rw [hs_image]
      simpa [p, i] using hx
    exact (convexHull_subset_affineSpan (𝕜 := ℝ) (p '' s)) hx'
  have hsum :
      ∑ j, Function.update (fun _ : τ.vertices => (0 : ℝ)) i 1 j = 1 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Function.update, hji]
    · simp
  by_contra hvS
  have hi_not : i ∉ s := by
    simp [s, i, hvS]
  have hi_eq :
      (Finset.univ.affineCombination ℝ p
        (Function.update (fun _ : τ.vertices => (0 : ℝ)) i 1)) = p i := by
    refine Finset.univ.affineCombination_of_eq_one_of_eq_zero
      (Function.update (fun _ : τ.vertices => (0 : ℝ)) i 1) p (by simp) (by simp) ?_
    intro j _ hji
    simp [Function.update, hji]
  have hzero := hAffine.eq_zero_of_affineCombination_mem_affineSpan hsum
    (by rwa [hi_eq]) (i := i) (by simp) hi_not
  simpa [i] using hzero

theorem SimplexTriangulation.mem_vertices_of_vertex_mem_realization {n : ℕ}
    {T : SimplexTriangulation n} {τ₁ τ₂ : SimplexFacet n}
    (hτ₁ : τ₁ ∈ T.facets) (hτ₂ : τ₂ ∈ T.facets) {v : RentSimplex n} (hv₂ : v ∈ τ₂.vertices)
    (hv₁ : ((v : RentSimplex n) : RentCoordinates n) ∈ τ₁.realization) :
    v ∈ τ₁.vertices := by
  have hv₂' :
      ((v : RentSimplex n) : RentCoordinates n) ∈ τ₂.realization := by
    rw [SimplexFacet.realization]
    exact subset_convexHull ℝ _ <| by
      exact Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n) hv₂
  have hv_inter :
      ((v : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ (τ₁.intersectionPointSet τ₂) := by
    rw [← T.face_intersection hτ₁ hτ₂]
    exact ⟨hv₁, hv₂'⟩
  have hv_common :
      v ∈ τ₁.commonVertices τ₂ := by
    refine T.mem_subset_of_vertex_mem_convexHull hτ₂ (S := τ₁.commonVertices τ₂)
      (SimplexFacet.commonVertices_subset_right τ₁ τ₂) hv₂ ?_
    simpa [SimplexFacet.intersectionPointSet, SimplexFacet.commonVertices] using hv_inter
  exact (mem_commonVertices_iff.mp hv_common).1

theorem SimplexFacet.realization_mono_of_isSubface {n : ℕ} {σ τ : SimplexFacet n}
    (hστ : σ.IsSubfaceOf τ) : σ.realization ⊆ τ.realization := by
  rw [SimplexFacet.realization, SimplexFacet.realization]
  refine convexHull_mono ?_
  rintro x ⟨v, hv, rfl⟩
  exact Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n) (hστ hv)

theorem SimplexFacet.realization_eq_segment_of_vertices_eq_pair {n : ℕ} (τ : SimplexFacet n)
    {x y : RentSimplex n} (hτ : τ.vertices = {x, y}) :
    τ.realization =
      segment ℝ ((x : RentSimplex n) : RentCoordinates n) ((y : RentSimplex n) : RentCoordinates n) := by
  rw [SimplexFacet.realization, SimplexFacet.pointSet, hτ]
  have himage :
      (((↑) : RentSimplex n → RentCoordinates n) '' ↑({x, y} : Finset (RentSimplex n))) =
        ({((x : RentSimplex n) : RentCoordinates n), ((y : RentSimplex n) : RentCoordinates n)} :
          Set (RentCoordinates n)) := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      simp [Finset.coe_insert, Finset.coe_singleton] at ha
      rcases ha with rfl | rfl <;> simp
    · intro hz
      rcases hz with rfl | rfl
      · exact ⟨x, by simp [Finset.coe_insert, Finset.coe_singleton], rfl⟩
      · exact ⟨y, by simp [Finset.coe_insert, Finset.coe_singleton], rfl⟩
  rw [himage]
  exact convexHull_pair
    (((x : RentSimplex n) : RentCoordinates n))
    (((y : RentSimplex n) : RentCoordinates n))

/-- The codimension-one adjacency relation on triangulation facets used by the Section 5 graph. -/
def SimplexTriangulation.AdjacentFacets {n : ℕ} (T : SimplexTriangulation n)
    (τ₁ τ₂ : SimplexFacet n) : Prop :=
  τ₁ ∈ T.facets ∧ τ₂ ∈ T.facets ∧ τ₁ ≠ τ₂ ∧ (τ₁.commonVertices τ₂).card = n - 1

theorem SimplexTriangulation.adjacentFacets_left_mem {n : ℕ} {T : SimplexTriangulation n}
    {τ₁ τ₂ : SimplexFacet n} (h : T.AdjacentFacets τ₁ τ₂) : τ₁ ∈ T.facets :=
  h.1

theorem SimplexTriangulation.adjacentFacets_right_mem {n : ℕ} {T : SimplexTriangulation n}
    {τ₁ τ₂ : SimplexFacet n} (h : T.AdjacentFacets τ₁ τ₂) : τ₂ ∈ T.facets :=
  h.2.1

theorem SimplexTriangulation.adjacentFacets_ne {n : ℕ} {T : SimplexTriangulation n}
    {τ₁ τ₂ : SimplexFacet n} (h : T.AdjacentFacets τ₁ τ₂) : τ₁ ≠ τ₂ :=
  h.2.2.1

theorem SimplexTriangulation.adjacentFacets_commonVertices_card {n : ℕ}
    {T : SimplexTriangulation n} {τ₁ τ₂ : SimplexFacet n} (h : T.AdjacentFacets τ₁ τ₂) :
    (τ₁.commonVertices τ₂).card = n - 1 :=
  h.2.2.2

theorem SimplexTriangulation.adjacentFacets_symm {n : ℕ} {T : SimplexTriangulation n}
    {τ₁ τ₂ : SimplexFacet n} (h : T.AdjacentFacets τ₁ τ₂) : T.AdjacentFacets τ₂ τ₁ := by
  refine ⟨adjacentFacets_right_mem h, adjacentFacets_left_mem h, ?_, ?_⟩
  · exact (adjacentFacets_ne h).symm
  · rw [SimplexFacet.commonVertices, Finset.inter_comm]
    exact adjacentFacets_commonVertices_card h

theorem SimplexTriangulation.adjacentFacets_commonFace_left {n : ℕ}
    {T : SimplexTriangulation n} {τ₁ τ₂ : SimplexFacet n} (_h : T.AdjacentFacets τ₁ τ₂) :
    (τ₁.commonFace τ₂).IsSubfaceOf τ₁ :=
  τ₁.commonFace_isSubfaceLeft τ₂

theorem SimplexTriangulation.adjacentFacets_commonFace_right {n : ℕ}
    {T : SimplexTriangulation n} {τ₁ τ₂ : SimplexFacet n} (_h : T.AdjacentFacets τ₁ τ₂) :
    (τ₁.commonFace τ₂).IsSubfaceOf τ₂ :=
  τ₁.commonFace_isSubfaceRight τ₂

/-- A cell of the triangulation is any simplex that occurs as a subface of one of its facets. -/
def SimplexTriangulation.IsFace {n : ℕ} (T : SimplexTriangulation n) (σ : SimplexFacet n) : Prop :=
  ∃ τ ∈ T.facets, σ.IsSubfaceOf τ

theorem SimplexTriangulation.facet_isFace {n : ℕ} {T : SimplexTriangulation n}
    {τ : SimplexFacet n} (hτ : τ ∈ T.facets) : T.IsFace τ :=
  ⟨τ, hτ, SimplexFacet.isSubfaceOf_refl _⟩

/-- The facets of `T` incident to a cell `σ`. -/
def SimplexTriangulation.incidentFacets {n : ℕ} (T : SimplexTriangulation n)
    (σ : SimplexFacet n) : Finset (SimplexFacet n) := by
  classical
  exact T.facets.filter fun τ => σ.IsSubfaceOf τ

@[simp]
theorem SimplexTriangulation.mem_incidentFacets_iff {n : ℕ} {T : SimplexTriangulation n}
    {σ τ : SimplexFacet n} :
    τ ∈ T.incidentFacets σ ↔ τ ∈ T.facets ∧ σ.IsSubfaceOf τ := by
  classical
  simp [SimplexTriangulation.incidentFacets]

theorem SimplexTriangulation.incidentFacets_nonempty_of_isFace {n : ℕ}
    {T : SimplexTriangulation n} {σ : SimplexFacet n} (hσ : T.IsFace σ) :
    (T.incidentFacets σ).Nonempty := by
  rcases hσ with ⟨τ, hτ, hστ⟩
  exact ⟨τ, mem_incidentFacets_iff.mpr ⟨hτ, hστ⟩⟩

theorem SimplexTriangulation.mem_facets_of_isFace_of_card {n : ℕ}
    {T : SimplexTriangulation n} {σ : SimplexFacet n} (hσ : T.IsFace σ)
    (hcard : σ.vertices.card = n) : σ ∈ T.facets := by
  rcases hσ with ⟨τ, hτ, hστ⟩
  have hEqVerts : σ.vertices = τ.vertices := by
    refine Finset.eq_of_subset_of_card_le hστ ?_
    simp [hcard, T.facet_card τ hτ]
  have hEq : σ = τ := by
    cases σ
    cases τ
    cases hEqVerts
    rfl
  exact hEq ▸ hτ

theorem SimplexTriangulation.adjacentFacets_mem_incidentFacets_commonFace_left {n : ℕ}
    {T : SimplexTriangulation n} {τ₁ τ₂ : SimplexFacet n} (h : T.AdjacentFacets τ₁ τ₂) :
    τ₁ ∈ T.incidentFacets (τ₁.commonFace τ₂) := by
  exact mem_incidentFacets_iff.mpr ⟨adjacentFacets_left_mem h, adjacentFacets_commonFace_left h⟩

theorem SimplexTriangulation.adjacentFacets_mem_incidentFacets_commonFace_right {n : ℕ}
    {T : SimplexTriangulation n} {τ₁ τ₂ : SimplexFacet n} (h : T.AdjacentFacets τ₁ τ₂) :
    τ₂ ∈ T.incidentFacets (τ₁.commonFace τ₂) := by
  exact mem_incidentFacets_iff.mpr ⟨adjacentFacets_right_mem h, adjacentFacets_commonFace_right h⟩

theorem SimplexTriangulation.two_le_card_incidentFacets_commonFace {n : ℕ}
    {T : SimplexTriangulation n} {τ₁ τ₂ : SimplexFacet n} (h : T.AdjacentFacets τ₁ τ₂) :
    2 ≤ (T.incidentFacets (τ₁.commonFace τ₂)).card := by
  classical
  have hsubset :
      ({τ₁, τ₂} : Finset (SimplexFacet n)) ⊆ T.incidentFacets (τ₁.commonFace τ₂) := by
    intro τ hτ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
    rcases hτ with rfl | rfl
    · exact adjacentFacets_mem_incidentFacets_commonFace_left h
    · exact adjacentFacets_mem_incidentFacets_commonFace_right h
  calc
    2 = ({τ₁, τ₂} : Finset (SimplexFacet n)).card := by
          simp [adjacentFacets_ne h]
    _ ≤ (T.incidentFacets (τ₁.commonFace τ₂)).card := Finset.card_le_card hsubset

end Arxiv170207325
