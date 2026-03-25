import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Arxiv170207325.SimplexModel

open scoped BigOperators

noncomputable section

namespace Arxiv170207325

abbrev VisibleRoommateIndex (n : ℕ) := Fin (n - 1)

def scaledSimplex (total labelCount : ℕ) : Set (RentCoordinates labelCount) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = (total : ℝ)}

def IsInteriorSimplexPoint {n : ℕ} (y : RentCoordinates n) : Prop :=
  y ∈ scaledSimplex 1 n ∧ coordSupport y = Finset.univ

structure SimplexFacet (n : ℕ) where
  vertices : Finset (RentSimplex n)

structure SimplexTriangulation (n : ℕ) where
  facets : Finset (SimplexFacet n)
  facet_card : ∀ τ ∈ facets, τ.vertices.card = n

def SimplexTriangulation.vertices {n : ℕ} (T : SimplexTriangulation n) : Finset (RentSimplex n) :=
  T.facets.biUnion SimplexFacet.vertices

abbrev VertexColoring (n : ℕ) := RentSimplex n → RoomIndex n

def IsSpernerLabeling {n : ℕ} (T : SimplexTriangulation n) (L : VertexColoring n) : Prop :=
  ∀ ⦃v : RentSimplex n⦄, v ∈ T.vertices → L v ∈ simplexSupport v

def FacetLabelSet {n : ℕ} (L : VertexColoring n) (τ : SimplexFacet n) : Finset (RoomIndex n) :=
  τ.vertices.image L

def FacetDistinctLabelCount {n : ℕ} (L : VertexColoring n) (τ : SimplexFacet n) : ℕ :=
  (FacetLabelSet L τ).card

def IsFullyLabeledFacet {n : ℕ} (L : VertexColoring n) (τ : SimplexFacet n) : Prop :=
  FacetLabelSet L τ = Finset.univ

def FacetUsesAtLeast {n : ℕ} (L : VertexColoring n) (τ : SimplexFacet n) (k : ℕ) : Prop :=
  k ≤ FacetDistinctLabelCount L τ

abbrev SelfMapOnRentSimplex (n : ℕ) := RentSimplex n → RentCoordinates n

def IsFaceRespecting {n : ℕ} (f : SelfMapOnRentSimplex n) : Prop :=
  ∀ x, f x ∈ scaledSimplex 1 n ∧ coordSupport (f x) ⊆ simplexSupport x

def IsPiecewiseAffineOn {n : ℕ} (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n) : Prop :=
  ∀ τ ∈ T.facets, ∃ g : RentCoordinates n →ᵃ[ℝ] RentCoordinates n,
    ∀ v ∈ (τ.vertices : Set (RentSimplex n)), g v = f v

def FacetImageHull {n : ℕ} (f : SelfMapOnRentSimplex n) (τ : SimplexFacet n) :
    Set (RentCoordinates n) :=
  convexHull ℝ ((fun v : RentSimplex n => f v) '' (τ.vertices : Set (RentSimplex n)))

def FacetImageContains {n : ℕ} (f : SelfMapOnRentSimplex n) (τ : SimplexFacet n)
    (y : RentCoordinates n) : Prop :=
  y ∈ FacetImageHull f τ

def FacetSupportsSecretiveAssignment {n : ℕ}
    (visible : VisibleRoommateIndex n → VertexColoring n) (τ : SimplexFacet n) : Prop :=
  ∀ secretRoom : RoomIndex n,
    ∃ assignment : VisibleRoommateIndex n → RoomIndex n,
      Function.Injective assignment ∧
      (∀ j, assignment j ≠ secretRoom) ∧
      (∀ j, assignment j ∈ FacetLabelSet (visible j) τ)

def vertexMultiplicityVector {n m : ℕ} (labelings : Fin m → VertexColoring n)
    (v : RentSimplex n) : RentCoordinates n :=
  fun i => ((Finset.univ.filter fun j : Fin m => labelings j v = i).card : ℝ)

def FacetMultiplicitySet {n m : ℕ} (labelings : Fin m → VertexColoring n) (τ : SimplexFacet n) :
    Set (RentCoordinates n) :=
  vertexMultiplicityVector labelings '' (τ.vertices : Set (RentSimplex n))

def FacetCapturesMultiplicityTarget {n m : ℕ} (labelings : Fin m → VertexColoring n)
    (τ : SimplexFacet n) (y : RentCoordinates n) : Prop :=
  y ∈ convexHull ℝ (FacetMultiplicitySet labelings τ)

def IsScaledLatticePoint (total labelCount : ℕ) (x : RentCoordinates labelCount) : Prop :=
  x ∈ scaledSimplex total labelCount ∧ ∀ i, ∃ z : ℕ, x i = z

def AvoidsLatticeHulls (total labelCount maxCard : ℕ) (y : RentCoordinates labelCount) : Prop :=
  ∀ S : Finset (RentCoordinates labelCount),
    S.card ≤ maxCard →
    (∀ x ∈ S, IsScaledLatticePoint total labelCount x) →
    y ∉ convexHull ℝ (S : Set (RentCoordinates labelCount))

end Arxiv170207325
