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

end Arxiv170207325
