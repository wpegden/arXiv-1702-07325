import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import PaperDefinitions
import Arxiv170207325.Section5Triangulation

noncomputable section

namespace Arxiv170207325

theorem SimplexFacet.image_pointSet_eq_vertexImage {n : ℕ} (σ : SimplexFacet n)
    (g : RentCoordinates n →ᵃ[ℝ] RentCoordinates n) :
    g '' σ.pointSet =
      (fun v : RentSimplex n => g (v : RentCoordinates n)) ''
        (σ.vertices : Set (RentSimplex n)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨(v : RentCoordinates n), ⟨v, hv, rfl⟩, rfl⟩

theorem SimplexFacet.image_pointSet_eq_facetVertexImage_of_isSubface {n : ℕ}
    {f : SelfMapOnRentSimplex n} {σ τ : SimplexFacet n} (hστ : σ.IsSubfaceOf τ)
    {g : RentCoordinates n →ᵃ[ℝ] RentCoordinates n}
    (hg : ∀ v ∈ (τ.vertices : Set (RentSimplex n)), g v = f v) :
    g '' σ.pointSet = (fun v : RentSimplex n => f v) '' (σ.vertices : Set (RentSimplex n)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨v, hv, rfl⟩
    exact ⟨v, hv, by rw [hg v (hστ hv)]⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨(v : RentCoordinates n), ⟨v, hv, rfl⟩, by rw [hg v (hστ hv)]⟩

theorem SimplexFacet.image_realization_eq_facetImageHull_of_isSubface {n : ℕ}
    {f : SelfMapOnRentSimplex n} {σ τ : SimplexFacet n} (hστ : σ.IsSubfaceOf τ)
    {g : RentCoordinates n →ᵃ[ℝ] RentCoordinates n}
    (hg : ∀ v ∈ (τ.vertices : Set (RentSimplex n)), g v = f v) :
    g '' σ.realization = FacetImageHull f σ := by
  rw [SimplexFacet.realization, FacetImageHull, AffineMap.image_convexHull,
    σ.image_pointSet_eq_facetVertexImage_of_isSubface hστ hg]

theorem SimplexTriangulation.eqOn_realization_of_isFace_piecewiseAffine {n : ℕ}
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {σ τ₁ τ₂ : SimplexFacet n}
    (_hτ₁ : τ₁ ∈ T.facets) (hστ₁ : σ.IsSubfaceOf τ₁)
    (_hτ₂ : τ₂ ∈ T.facets) (hστ₂ : σ.IsSubfaceOf τ₂)
    {g₁ g₂ : RentCoordinates n →ᵃ[ℝ] RentCoordinates n}
    (hg₁ : ∀ v ∈ (τ₁.vertices : Set (RentSimplex n)), g₁ v = f v)
    (hg₂ : ∀ v ∈ (τ₂.vertices : Set (RentSimplex n)), g₂ v = f v) :
    Set.EqOn g₁ g₂ σ.realization := by
  have hpoint : Set.EqOn g₁ g₂ σ.pointSet := by
    intro x hx
    rcases hx with ⟨v, hv, rfl⟩
    rw [hg₁ v (hστ₁ hv), hg₂ v (hστ₂ hv)]
  have hspan : Set.EqOn g₁ g₂ (affineSpan ℝ σ.pointSet : Set (RentCoordinates n)) :=
    AffineMap.eqOn_affineSpan hpoint
  intro x hx
  exact hspan <|
    (convexHull_subset_affineSpan (𝕜 := ℝ) (s := σ.pointSet)) <|
      by simpa [SimplexFacet.realization] using hx

theorem SimplexTriangulation.exists_point_in_realization_of_facetImageContains {n : ℕ}
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {σ : SimplexFacet n}
    (hσ : T.IsFace σ) (hpa : IsPiecewiseAffineOn T f) {y : RentCoordinates n}
    (hy : FacetImageContains f σ y) :
    ∃ τ ∈ T.facets, σ.IsSubfaceOf τ ∧
      ∃ g : RentCoordinates n →ᵃ[ℝ] RentCoordinates n,
        (∀ v ∈ (τ.vertices : Set (RentSimplex n)), g v = f v) ∧
        ∃ x ∈ σ.realization, g x = y := by
  rcases hσ with ⟨τ, hτ, hστ⟩
  rcases hpa τ hτ with ⟨g, hg⟩
  have hy' : y ∈ g '' σ.realization := by
    rw [σ.image_realization_eq_facetImageHull_of_isSubface hστ hg]
    exact hy
  rcases hy' with ⟨x, hx, hxy⟩
  exact ⟨τ, hτ, hστ, g, hg, x, hx, hxy⟩

end Arxiv170207325
