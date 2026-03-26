import PaperDefinitions
import Arxiv170207325.SimplexModel

noncomputable section

namespace Arxiv170207325

/-- The ambient-coordinate version of a coordinate face, used for codomain statements about
face-preserving maps. -/
def ambientCoordinateFace {n : ℕ} (I : Finset (RoomIndex n)) : Set (RentCoordinates n) :=
  {y | y ∈ scaledSimplex 1 n ∧ coordSupport y ⊆ I}

@[simp]
theorem mem_ambientCoordinateFace_iff {n : ℕ} {I : Finset (RoomIndex n)} {y : RentCoordinates n} :
    y ∈ ambientCoordinateFace I ↔ y ∈ scaledSimplex 1 n ∧ coordSupport y ⊆ I :=
  Iff.rfl

theorem ambientCoordinateFace_mono {n : ℕ} {I J : Finset (RoomIndex n)} (hIJ : I ⊆ J) :
    ambientCoordinateFace I ⊆ ambientCoordinateFace J := by
  intro y hy
  exact ⟨hy.1, hy.2.trans hIJ⟩

theorem mem_ambientCoordinateFace_of_mem_coordinateFace {n : ℕ} {I : Finset (RoomIndex n)}
    {x : RentSimplex n} (hx : x ∈ coordinateFace I) :
    ((x : RentSimplex n) : RentCoordinates n) ∈ ambientCoordinateFace I := by
  refine ⟨?_, hx⟩
  simpa [RentSimplex, scaledSimplex] using x.2

@[simp]
theorem ambientCoordinateFace_univ (n : ℕ) :
    ambientCoordinateFace (Finset.univ : Finset (RoomIndex n)) = scaledSimplex 1 n := by
  ext y
  simp [ambientCoordinateFace]

theorem convex_ambientCoordinateFace {n : ℕ} (I : Finset (RoomIndex n)) :
    Convex ℝ (ambientCoordinateFace I) := by
  have hs : Convex ℝ (scaledSimplex 1 n) := by
    simpa [scaledSimplex, RentSimplex] using (convex_stdSimplex ℝ (RoomIndex n))
  intro x hx y hy a b ha hb hab
  refine ⟨hs hx.1 hy.1 ha hb hab, ?_⟩
  rw [coordSupport_subset_iff]
  intro i hi
  have hx0 : x i = 0 := (coordSupport_subset_iff.mp hx.2) i hi
  have hy0 : y i = 0 := (coordSupport_subset_iff.mp hy.2) i hi
  simp [hx0, hy0]

theorem IsFaceRespecting.mem_scaledSimplex {n : ℕ} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (x : RentSimplex n) :
    f x ∈ scaledSimplex 1 n :=
  (hf x).1

theorem IsFaceRespecting.coordSupport_subset {n : ℕ} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (x : RentSimplex n) :
    coordSupport (f x) ⊆ simplexSupport x :=
  (hf x).2

theorem IsFaceRespecting.mapsTo_ambientCoordinateFace {n : ℕ} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (I : Finset (RoomIndex n)) :
    Set.MapsTo f (coordinateFace I) (ambientCoordinateFace I) := by
  intro x hx
  exact ⟨hf.mem_scaledSimplex x, (hf.coordSupport_subset x).trans hx⟩

theorem rentBarycenter_mem_scaledSimplex (n : ℕ) [NeZero n] :
    ((rentBarycenter n : RentSimplex n) : RentCoordinates n) ∈ scaledSimplex 1 n := by
  constructor
  · intro i
    exact le_of_lt (rentBarycenter_apply_pos i)
  · convert (stdSimplex.sum_eq_one (rentBarycenter n)) using 1
    norm_num

theorem rentBarycenter_isInteriorSimplexPoint (n : ℕ) [NeZero n] :
    IsInteriorSimplexPoint ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  refine ⟨rentBarycenter_mem_scaledSimplex n, ?_⟩
  simpa [simplexSupport] using (simplexSupport_rentBarycenter (n := n))

theorem interiorPoint_mem_ambientCoordinateFace_iff {n : ℕ} {I : Finset (RoomIndex n)}
    {y : RentCoordinates n} (hy : IsInteriorSimplexPoint y) :
    y ∈ ambientCoordinateFace I ↔ I = Finset.univ := by
  rcases hy with ⟨hySimplex, hySupport⟩
  constructor
  · intro hyI
    exact Finset.Subset.antisymm (Finset.subset_univ I) (hySupport ▸ hyI.2)
  · intro hI
    exact ⟨hySimplex, hI ▸ Finset.subset_univ _⟩

@[simp]
theorem rentBarycenter_mem_ambientCoordinateFace_iff {n : ℕ} [NeZero n]
    {I : Finset (RoomIndex n)} :
    ((rentBarycenter n : RentSimplex n) : RentCoordinates n) ∈ ambientCoordinateFace I ↔
      I = Finset.univ := by
  exact interiorPoint_mem_ambientCoordinateFace_iff (rentBarycenter_isInteriorSimplexPoint n)

theorem facetImageHull_subset_ambientCoordinateFace {n : ℕ} {f : SelfMapOnRentSimplex n}
    {τ : SimplexFacet n} {I : Finset (RoomIndex n)}
    (hverts : ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices → f v ∈ ambientCoordinateFace I) :
    FacetImageHull f τ ⊆ ambientCoordinateFace I := by
  refine convexHull_min ?_ (convex_ambientCoordinateFace I)
  intro z hz
  rcases hz with ⟨v, hv, rfl⟩
  exact hverts hv

theorem IsFaceRespecting.eq_interiorPoint_of_mem_coordinateFace {n : ℕ}
    {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f) {x : RentSimplex n}
    {I : Finset (RoomIndex n)} {y : RentCoordinates n} (hx : x ∈ coordinateFace I)
    (hy : IsInteriorSimplexPoint y) (hxy : f x = y) :
    I = Finset.univ := by
  exact (interiorPoint_mem_ambientCoordinateFace_iff hy).mp <| by
    rw [← hxy]
    exact hf.mapsTo_ambientCoordinateFace I hx

theorem IsFaceRespecting.ne_interiorPoint_of_mem_coordinateFace {n : ℕ}
    {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f) {x : RentSimplex n}
    {I : Finset (RoomIndex n)} {y : RentCoordinates n} (hx : x ∈ coordinateFace I)
    (hI : I ≠ Finset.univ) (hy : IsInteriorSimplexPoint y) :
    f x ≠ y := by
  intro hxy
  exact hI (hf.eq_interiorPoint_of_mem_coordinateFace hx hy hxy)

theorem facetImageContains_interiorPoint_of_vertexImages {n : ℕ} {f : SelfMapOnRentSimplex n}
    {τ : SimplexFacet n} {I : Finset (RoomIndex n)} {y : RentCoordinates n}
    (hverts : ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices → f v ∈ ambientCoordinateFace I)
    (hy : IsInteriorSimplexPoint y) (hyτ : FacetImageContains f τ y) :
    I = Finset.univ := by
  exact (interiorPoint_mem_ambientCoordinateFace_iff hy).mp <|
    facetImageHull_subset_ambientCoordinateFace hverts hyτ

theorem IsFaceRespecting.facetImageContains_interiorPoint_of_vertices {n : ℕ}
    {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f) {τ : SimplexFacet n}
    {I : Finset (RoomIndex n)} {y : RentCoordinates n}
    (hτ : ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices → v ∈ coordinateFace I)
    (hy : IsInteriorSimplexPoint y) (hyτ : FacetImageContains f τ y) :
    I = Finset.univ := by
  refine facetImageContains_interiorPoint_of_vertexImages ?_ hy hyτ
  intro v hv
  exact hf.mapsTo_ambientCoordinateFace I (hτ hv)

end Arxiv170207325
