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

theorem SimplexFacet.pointSet_subset_of_isSubface {n : ℕ} {σ τ : SimplexFacet n}
    (hστ : σ.IsSubfaceOf τ) :
    σ.pointSet ⊆ τ.pointSet := by
  rintro x ⟨v, hv, rfl⟩
  exact Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n) (hστ hv)

theorem SimplexFacet.realization_subset_of_isSubface {n : ℕ} {σ τ : SimplexFacet n}
    (hστ : σ.IsSubfaceOf τ) :
    σ.realization ⊆ τ.realization :=
  convexHull_mono (σ.pointSet_subset_of_isSubface hστ)

theorem SimplexFacet.mem_realization_of_mem_vertices {n : ℕ} {τ : SimplexFacet n}
    {v : RentSimplex n} (hv : v ∈ τ.vertices) :
    ((v : RentSimplex n) : RentCoordinates n) ∈ τ.realization := by
  exact subset_convexHull ℝ τ.pointSet <|
    Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n) hv

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
