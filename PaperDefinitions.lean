import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Arxiv170207325.SimplexModel

open scoped BigOperators

noncomputable section

namespace Arxiv170207325

/-- The `n - 1` visible roommates in the secretive-roommate theorem. -/
abbrev VisibleRoommateIndex (n : ℕ) := Fin (n - 1)

/-- The scaled simplex `m · Δ` used in the multiple-labeling theorems. -/
def scaledSimplex (total labelCount : ℕ) : Set (RentCoordinates labelCount) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = (total : ℝ)}

/-- A point of the simplex lying in the relative interior, encoded by positive support. -/
def IsInteriorSimplexPoint {n : ℕ} (y : RentCoordinates n) : Prop :=
  y ∈ scaledSimplex 1 n ∧ coordSupport y = Finset.univ

/-- A simplex in a triangulation, represented by its vertices in the rent simplex. -/
structure SimplexFacet (n : ℕ) where
  vertices : Finset (RentSimplex n)

/-- The ambient point set of a facet, viewed inside `Fin n → ℝ`. -/
def SimplexFacet.pointSet {n : ℕ} (τ : SimplexFacet n) : Set (RentCoordinates n) :=
  ((↑) : RentSimplex n → RentCoordinates n) '' (τ.vertices : Set (RentSimplex n))

/-- The common vertex set of two facets, viewed in the ambient coordinate space. -/
def SimplexFacet.intersectionPointSet {n : ℕ} (τ₁ τ₂ : SimplexFacet n) :
    Set (RentCoordinates n) :=
  ((↑) : RentSimplex n → RentCoordinates n) ''
    ((τ₁.vertices ∩ τ₂.vertices : Finset (RentSimplex n)) : Set (RentSimplex n))

/-- The geometric simplex spanned by the vertices of a facet. -/
def SimplexFacet.realization {n : ℕ} (τ : SimplexFacet n) : Set (RentCoordinates n) :=
  convexHull ℝ τ.pointSet

/-- A finite triangulation of the standard rent simplex.

The extra fields record the paper's intended triangulation axioms: each facet has the expected
number of vertices, those vertices are affinely independent, the facets cover the simplex, and
facet intersections are exactly the common faces determined by shared vertices. -/
structure SimplexTriangulation (n : ℕ) where
  facets : Finset (SimplexFacet n)
  facet_card : ∀ τ ∈ facets, τ.vertices.card = n
  facet_affineIndependent :
    ∀ τ ∈ facets,
      AffineIndependent ℝ (fun v : τ.vertices => ((v : RentSimplex n) : RentCoordinates n))
  face_intersection :
    ∀ ⦃τ₁ τ₂ : SimplexFacet n⦄, τ₁ ∈ facets → τ₂ ∈ facets →
      τ₁.realization ∩ τ₂.realization = convexHull ℝ (τ₁.intersectionPointSet τ₂)
  covers_simplex :
    ∀ x : RentSimplex n, ∃ τ ∈ facets, ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization

/-- The vertex set of the whole triangulation. -/
def SimplexTriangulation.vertices {n : ℕ} (T : SimplexTriangulation n) : Finset (RentSimplex n) :=
  T.facets.biUnion SimplexFacet.vertices

/-- A vertex-coloring by room labels. -/
abbrev VertexColoring (n : ℕ) := RentSimplex n → RoomIndex n

/-- The boundary condition for a Sperner labeling: every triangulation vertex is labeled by a room
that is available on the smallest coordinate face containing that vertex. -/
def IsSpernerLabeling {n : ℕ} (T : SimplexTriangulation n) (L : VertexColoring n) : Prop :=
  ∀ ⦃v : RentSimplex n⦄, v ∈ T.vertices → L v ∈ simplexSupport v

/-- A paper-facing Sperner labeling object on a fixed triangulation. -/
structure SpernerLabeling {n : ℕ} (T : SimplexTriangulation n) where
  toColoring : VertexColoring n
  isSperner : IsSpernerLabeling T toColoring

instance {n : ℕ} {T : SimplexTriangulation n} :
    CoeFun (SpernerLabeling T) (fun _ => RentSimplex n → RoomIndex n) where
  coe L := L.toColoring

/-- The `n - 1` visible Sperner labelings used in the secretive-roommate theorem. -/
abbrev VisibleSpernerProfile {n : ℕ} (T : SimplexTriangulation n) :=
  VisibleRoommateIndex n → SpernerLabeling T

/-- An `m`-tuple of Sperner labelings on one triangulation. -/
abbrev SpernerLabelingFamily {n : ℕ} (T : SimplexTriangulation n) (m : ℕ) :=
  Fin m → SpernerLabeling T

/-- The raw encoded profile, before bundling the Sperner condition into the type. -/
abbrev EncodedVisiblePreferenceProfile (n : ℕ) :=
  VisibleRoommateIndex n → VertexColoring n

/-- Forget the bundled Sperner proofs and recover the raw visible profile used by the combinatorial
matching statement. -/
def VisibleSpernerProfile.toEncoded {n : ℕ} {T : SimplexTriangulation n}
    (visible : VisibleSpernerProfile T) : EncodedVisiblePreferenceProfile n :=
  fun j v => visible j v

/-- Forget the bundled Sperner proofs and recover the raw family of colorings. -/
def SpernerLabelingFamily.toColorings {n m : ℕ} {T : SimplexTriangulation n}
    (labelings : SpernerLabelingFamily T m) : Fin m → VertexColoring n :=
  fun j v => labelings j v

/-- Every visible roommate's encoding satisfies the Sperner boundary rule. -/
def IsSecretiveSpernerProfile {n : ℕ} (T : SimplexTriangulation n)
    (visible : EncodedVisiblePreferenceProfile n) : Prop :=
  ∀ j, IsSpernerLabeling T (visible j)

/-- The set of room labels shown on a facet. -/
def FacetLabelSet {n : ℕ} (L : VertexColoring n) (τ : SimplexFacet n) : Finset (RoomIndex n) :=
  τ.vertices.image L

/-- The number of distinct room labels shown on a facet. -/
def FacetDistinctLabelCount {n : ℕ} (L : VertexColoring n) (τ : SimplexFacet n) : ℕ :=
  (FacetLabelSet L τ).card

/-- A facet is fully labeled when every room label appears on its vertices. -/
def IsFullyLabeledFacet {n : ℕ} (L : VertexColoring n) (τ : SimplexFacet n) : Prop :=
  FacetLabelSet L τ = Finset.univ

/-- Lower bound on how many distinct labels a labeling uses on one facet. -/
def FacetUsesAtLeast {n : ℕ} (L : VertexColoring n) (τ : SimplexFacet n) (k : ℕ) : Prop :=
  k ≤ FacetDistinctLabelCount L τ

/-- The ambient map used in the piecewise-linear arguments of Sections 2, 4, 5, and 6. -/
abbrev SelfMapOnRentSimplex (n : ℕ) := RentSimplex n → RentCoordinates n

/-- Manuscript-facing name for the same object: a piecewise-linear self-map of the simplex. -/
abbrev PiecewiseLinearSimplexMap (n : ℕ) := SelfMapOnRentSimplex n

/-- A map preserves coordinate faces when the support of `f x` stays inside the support of `x`. -/
def IsFaceRespecting {n : ℕ} (f : SelfMapOnRentSimplex n) : Prop :=
  ∀ x, f x ∈ scaledSimplex 1 n ∧ coordSupport (f x) ⊆ simplexSupport x

/-- Manuscript-facing alias for the face-preserving condition. -/
abbrev PreservesCoordinateFaces {n : ℕ} (f : PiecewiseLinearSimplexMap n) : Prop :=
  IsFaceRespecting f

/-- A map is piecewise affine when each facet carries one affine interpolation matching the vertex
values of the map. -/
def IsPiecewiseAffineOn {n : ℕ} (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n) : Prop :=
  ∀ τ ∈ T.facets, ∃ g : RentCoordinates n →ᵃ[ℝ] RentCoordinates n,
    ∀ v ∈ (τ.vertices : Set (RentSimplex n)), g v = f v

/-- Manuscript-facing alias: the paper says piecewise linear, while the Lean statement uses affine
interpolation on each simplex. -/
abbrev IsPiecewiseLinearOn {n : ℕ} (T : SimplexTriangulation n)
    (f : PiecewiseLinearSimplexMap n) : Prop :=
  IsPiecewiseAffineOn T f

/-- The convex hull of the image of one facet under a piecewise-linear simplex map. -/
def FacetImageHull {n : ℕ} (f : SelfMapOnRentSimplex n) (τ : SimplexFacet n) :
    Set (RentCoordinates n) :=
  convexHull ℝ ((fun v : RentSimplex n => f v) '' (τ.vertices : Set (RentSimplex n)))

/-- A target point is hit on one facet when it lies in the convex hull of the facet image. -/
def FacetImageContains {n : ℕ} (f : SelfMapOnRentSimplex n) (τ : SimplexFacet n)
    (y : RentCoordinates n) : Prop :=
  y ∈ FacetImageHull f τ

/-- One facet supports a secretive assignment when, after deleting any secret room, the visible
roommates can still be matched injectively to acceptable rooms shown on that facet. -/
def FacetSupportsSecretiveAssignment {n : ℕ}
    (visible : EncodedVisiblePreferenceProfile n) (τ : SimplexFacet n) : Prop :=
  ∀ secretRoom : RoomIndex n,
    ∃ assignment : VisibleRoommateIndex n → RoomIndex n,
      Function.Injective assignment ∧
      (∀ j, assignment j ≠ secretRoom) ∧
      (∀ j, assignment j ∈ FacetLabelSet (visible j) τ)

/-- The multiplicity vector used in the first Section 6 theorem. -/
def vertexMultiplicityVector {n m : ℕ} (labelings : Fin m → VertexColoring n)
    (v : RentSimplex n) : RentCoordinates n :=
  fun i => ((Finset.univ.filter fun j : Fin m => labelings j v = i).card : ℝ)

/-- The lattice points obtained from the multiplicity vectors of a facet's vertices. -/
def FacetMultiplicitySet {n m : ℕ} (labelings : Fin m → VertexColoring n) (τ : SimplexFacet n) :
    Set (RentCoordinates n) :=
  vertexMultiplicityVector labelings '' (τ.vertices : Set (RentSimplex n))

/-- A facet captures the target multiplicity point `y` when `y` lies in the convex hull of the
multiplicity vectors attached to its vertices. -/
def FacetCapturesMultiplicityTarget {n m : ℕ} (labelings : Fin m → VertexColoring n)
    (τ : SimplexFacet n) (y : RentCoordinates n) : Prop :=
  y ∈ convexHull ℝ (FacetMultiplicitySet labelings τ)

/-- Integer lattice points inside the scaled simplex `m · Δ`. -/
def IsScaledLatticePoint (total labelCount : ℕ) (x : RentCoordinates labelCount) : Prop :=
  x ∈ scaledSimplex total labelCount ∧ ∀ i, ∃ z : ℕ, x i = z

/-- The genericity condition from the first multiple-labeling theorem: the target avoids convex
hulls of small lattice sets. -/
def AvoidsLatticeHulls (total labelCount maxCard : ℕ) (y : RentCoordinates labelCount) : Prop :=
  ∀ S : Finset (RentCoordinates labelCount),
    S.card ≤ maxCard →
    (∀ x ∈ S, IsScaledLatticePoint total labelCount x) →
    y ∉ convexHull ℝ (S : Set (RentCoordinates labelCount))

end Arxiv170207325
