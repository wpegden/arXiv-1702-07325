import PaperDefinitions

noncomputable section

namespace Arxiv170207325

/-! ## Support-level geometric statements -/

/-- Section 5's central support theorem: a face-preserving piecewise-linear self-map of a
triangulated simplex hits any chosen interior target on some facet. -/
def InteriorTargetFacetStatement (n : ℕ) [NeZero n] : Prop :=
  ∀ (T : SimplexTriangulation n) (f : PiecewiseLinearSimplexMap n) (y : RentCoordinates n),
    IsPiecewiseLinearOn T f →
    PreservesCoordinateFaces f →
    IsInteriorSimplexPoint y →
    ∃ τ ∈ T.facets, FacetImageContains f τ y

/-- The barycenter-specialized form used directly in the second proof of Sperner's lemma and in
the secretive-roommate theorem. -/
def BarycenterFacetStatement (n : ℕ) [NeZero n] : Prop :=
  ∀ (T : SimplexTriangulation n) (f : PiecewiseLinearSimplexMap n),
    IsPiecewiseLinearOn T f →
    PreservesCoordinateFaces f →
    ∃ τ ∈ T.facets, FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n)

/-! ## Paper-facing combinatorial statements -/

/-- Paper Section 2, Sperner's lemma in the higher-dimensional existence form used later in the
manuscript. -/
def SpernerLemmaStatement (n : ℕ) [NeZero n] : Prop :=
  ∀ (T : SimplexTriangulation n) (L : SpernerLabeling T),
    ∃ τ ∈ T.facets, IsFullyLabeledFacet L τ

/-- Encoded combinatorial form of Theorem 1.1, before bundling the Sperner condition into the
type of the visible profiles. -/
def EncodedSecretiveRentalHarmonyStatement (n : ℕ) [NeZero n] : Prop :=
  ∀ (T : SimplexTriangulation n) (visible : EncodedVisiblePreferenceProfile n),
    IsSecretiveSpernerProfile T visible →
    ∃ τ ∈ T.facets, FacetSupportsSecretiveAssignment visible τ

/-- Paper Theorem 1.1, specialized to the `n = 3` case and written directly in terms of two
visible Sperner labelings. -/
def ThreeRoommateStatement : Prop :=
  ∀ (T : SimplexTriangulation 3) (visible : VisibleSpernerProfile T),
    ∃ τ ∈ T.facets,
      FacetSupportsSecretiveAssignment (VisibleSpernerProfile.toEncoded visible) τ

/-- Paper Theorem 1.1, formalized via the visible roommates' Sperner encodings. -/
def SecretiveRentalHarmonyStatement (n : ℕ) [NeZero n] : Prop :=
  ∀ (T : SimplexTriangulation n) (visible : VisibleSpernerProfile T),
    ∃ τ ∈ T.facets,
      FacetSupportsSecretiveAssignment (VisibleSpernerProfile.toEncoded visible) τ

/-- Section 6, first multiple-labeling theorem, stated using multiplicity vectors in the scaled
simplex `m · Δ_n`. -/
def PrimalMultipleLabelingStatement (n m : ℕ) : Prop :=
  ∀ (T : SimplexTriangulation (n + 1)) (labelings : SpernerLabelingFamily T m)
    (y : RentCoordinates (n + 1)),
    y ∈ scaledSimplex m (n + 1) →
    AvoidsLatticeHulls m (n + 1) n y →
    ∃ τ ∈ T.facets,
      FacetCapturesMultiplicityTarget (SpernerLabelingFamily.toColorings labelings) τ y

/-- Section 6, second multiple-labeling theorem, phrased as lower bounds on the number of
distinct labels shown by each labeling on one facet. -/
def DualMultipleLabelingStatement (n m : ℕ) : Prop :=
  ∀ (T : SimplexTriangulation (n + 1)) (labelings : SpernerLabelingFamily T m)
    (k : Fin m → ℕ),
    (∀ j, 0 < k j) →
    (∑ j, k j) = n + m →
    ∃ τ ∈ T.facets, ∀ j, FacetUsesAtLeast (labelings j) τ (k j)

end Arxiv170207325
