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

@[simp]
theorem ambientCoordinateFace_univ (n : ℕ) :
    ambientCoordinateFace (Finset.univ : Finset (RoomIndex n)) = scaledSimplex 1 n := by
  ext y
  simp [ambientCoordinateFace]

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
  · simpa using (stdSimplex.sum_eq_one (rentBarycenter n) : ∑ i, (rentBarycenter n) i = (1 : ℝ))

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

end Arxiv170207325
