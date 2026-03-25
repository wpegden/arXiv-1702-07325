import Arxiv170207325.PaperDefinitionsCore

noncomputable section

namespace Arxiv170207325

/-- Section 5's central target-hitting theorem in the interior-point form used by the later paper
results. -/
def InteriorTargetFacetStatement (n : ℕ) [NeZero n] : Prop :=
  ∀ (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n) (y : RentCoordinates n),
    IsPiecewiseAffineOn T f →
    IsFaceRespecting f →
    IsInteriorSimplexPoint y →
    ∃ τ ∈ T.facets, FacetImageContains f τ y

/-- Paper Section 2, higher-dimensional Sperner lemma in the existence form used by the rest of
the manuscript. -/
def SpernerLemmaStatement (n : ℕ) [NeZero n] : Prop :=
  ∀ (T : SimplexTriangulation n) (L : VertexColoring n),
    IsSpernerLabeling T L →
    ∃ τ ∈ T.facets, IsFullyLabeledFacet L τ

/-- Paper Theorem 1.1 specialized to the `n = 3` case. -/
def ThreeRoommateStatement : Prop :=
  ∀ (T : SimplexTriangulation 3) (visible : VisibleRoommateIndex 3 → VertexColoring 3),
    (∀ j, IsSpernerLabeling T (visible j)) →
    ∃ τ ∈ T.facets, FacetSupportsSecretiveAssignment visible τ

/-- Paper Theorem 1.1 in the encoded combinatorial form used in Sections 3 and 4. -/
def SecretiveRentalHarmonyStatement (n : ℕ) [NeZero n] : Prop :=
  ∀ (T : SimplexTriangulation n) (visible : VisibleRoommateIndex n → VertexColoring n),
    (∀ j, IsSpernerLabeling T (visible j)) →
    ∃ τ ∈ T.facets, FacetSupportsSecretiveAssignment visible τ

/-- Section 6, first multiple-labeling theorem, stated using multiplicity vectors in the scaled
simplex. -/
def PrimalMultipleLabelingStatement (n m : ℕ) : Prop :=
  ∀ (T : SimplexTriangulation (n + 1)) (labelings : Fin m → VertexColoring (n + 1))
    (y : RentCoordinates (n + 1)),
    (∀ j, IsSpernerLabeling T (labelings j)) →
    y ∈ scaledSimplex m (n + 1) →
    AvoidsLatticeHulls m (n + 1) n y →
    ∃ τ ∈ T.facets, FacetCapturesMultiplicityTarget labelings τ y

/-- Section 6, second multiple-labeling theorem, phrased as lower bounds on the number of
distinct labels shown by each labeling on one facet. -/
def DualMultipleLabelingStatement (n m : ℕ) : Prop :=
  ∀ (T : SimplexTriangulation (n + 1)) (labelings : Fin m → VertexColoring (n + 1))
    (k : Fin m → ℕ),
    (∀ j, IsSpernerLabeling T (labelings j)) →
    (∀ j, 0 < k j) →
    (∑ j, k j) = n + m →
    ∃ τ ∈ T.facets, ∀ j, FacetUsesAtLeast (labelings j) τ (k j)

end Arxiv170207325
