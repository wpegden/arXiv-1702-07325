import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Arxiv170207325.InteriorTarget
import Arxiv170207325.PiecewiseAffine
import Arxiv170207325.Section5Triangulation

noncomputable section

namespace Arxiv170207325

/-- The prefix face `conv{e_1, ..., e_k}` from Section 5, encoded by its coordinate support. -/
def prefixRooms (n k : ℕ) : Finset (RoomIndex n) :=
  Finset.univ.filter fun i => i.1 < k

@[simp]
theorem mem_prefixRooms_iff {n k : ℕ} {i : RoomIndex n} :
    i ∈ prefixRooms n k ↔ i.1 < k := by
  simp [prefixRooms]

theorem prefixRooms_mono {n k l : ℕ} (hkl : k ≤ l) :
    prefixRooms n k ⊆ prefixRooms n l := by
  intro i hi
  exact mem_prefixRooms_iff.mpr <| lt_of_lt_of_le (mem_prefixRooms_iff.mp hi) hkl

@[simp]
theorem prefixRooms_self (n : ℕ) :
    prefixRooms n n = Finset.univ := by
  ext i
  simp [prefixRooms]

theorem prefixRooms_card {n k : ℕ} (hk : k ≤ n) :
    (prefixRooms n k).card = k := by
  classical
  have hcard :
      (Finset.univ : Finset (Fin k)).card = (prefixRooms n k).card := by
    refine Finset.card_bij
      (s := (Finset.univ : Finset (Fin k)))
      (t := prefixRooms n k)
      (fun i _ => ⟨i.1, lt_of_lt_of_le i.2 hk⟩)
      ?_ ?_ ?_
    · intro i hi
      exact mem_prefixRooms_iff.mpr i.2
    · intro i _ j _ hij
      apply Fin.ext
      simpa using congrArg Fin.val hij
    · intro b hb
      refine ⟨⟨b.1, mem_prefixRooms_iff.mp hb⟩, by simp, ?_⟩
      exact Fin.ext rfl
  simpa using hcard.symm

theorem prefixRooms_eq_univ_iff {n k : ℕ} (hk : k ≤ n) :
    prefixRooms n k = Finset.univ ↔ k = n := by
  constructor
  · intro h
    have hcard : k = n := by
      simpa [prefixRooms_card hk] using congrArg Finset.card h
    exact hcard
  · intro h
    subst h
    simp [prefixRooms_self]

/-- The first standard simplex vertex on the boundary edge `[e₁,e₂]`. -/
def section5FirstIndex {n : ℕ} (hn : 2 ≤ n) : RoomIndex n :=
  ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hn⟩

@[simp]
theorem section5FirstIndex_val {n : ℕ} (hn : 2 ≤ n) :
    (section5FirstIndex hn).1 = 0 :=
  rfl

/-- The second standard simplex vertex on the boundary edge `[e₁,e₂]`. -/
def section5SecondIndex {n : ℕ} (hn : 2 ≤ n) : RoomIndex n :=
  ⟨1, lt_of_lt_of_le (by decide : 1 < 2) hn⟩

@[simp]
theorem section5SecondIndex_val {n : ℕ} (hn : 2 ≤ n) :
    (section5SecondIndex hn).1 = 1 :=
  rfl

theorem section5SecondIndex_ne_zero {n : ℕ} (hn : 2 ≤ n) :
    section5SecondIndex hn ≠ section5FirstIndex hn := by
  intro h
  have hval := congrArg Fin.val h
  simp [section5SecondIndex] at hval

theorem prefixRooms_two_eq_pair {n : ℕ} (hn : 2 ≤ n) :
    prefixRooms n 2 = {section5FirstIndex hn, section5SecondIndex hn} := by
  ext i
  constructor
  · intro hi
    have hi_lt : i.1 < 2 := mem_prefixRooms_iff.mp hi
    have hi' : i.1 = 0 ∨ i.1 = 1 := by
      omega
    rcases hi' with hi' | hi'
    · refine Finset.mem_insert.mpr <| Or.inl ?_
      apply Fin.ext
      simpa [section5FirstIndex] using hi'
    · have : i = section5SecondIndex hn := by
        apply Fin.ext
        simpa [section5SecondIndex] using hi'
      simp [this]
  · intro hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · have : i = section5FirstIndex hn := by simpa using hi
      subst this
      simp [mem_prefixRooms_iff, section5FirstIndex]
    · have : i = section5SecondIndex hn := by simpa using hi
      subst this
      simp [mem_prefixRooms_iff, section5SecondIndex]

theorem section5FirstIndex_eq_zero {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    section5FirstIndex hn = (0 : RoomIndex n) := by
  apply Fin.ext
  simp [section5FirstIndex]

/-- The second endpoint `e₂` of the Section 5 boundary edge `[e₁,e₂]`. -/
def section5SecondVertex (n : ℕ) (hn : 2 ≤ n) : RentSimplex n :=
  stdSimplex.vertex (S := ℝ) (section5SecondIndex hn)

/-- The barycenter `b_k` of the prefix face `conv{e_1, ..., e_k}` from Section 5. -/
def prefixBarycenter (n k : ℕ) : RentCoordinates n :=
  fun i => if i.1 < k then (k : ℝ)⁻¹ else 0

@[simp]
theorem prefixBarycenter_apply_of_lt {n k : ℕ} {i : RoomIndex n} (hi : i.1 < k) :
    prefixBarycenter n k i = (k : ℝ)⁻¹ := by
  simp [prefixBarycenter, hi]

@[simp]
theorem prefixBarycenter_apply_of_not_lt {n k : ℕ} {i : RoomIndex n} (hi : ¬ i.1 < k) :
    prefixBarycenter n k i = 0 := by
  simp [prefixBarycenter, hi]

theorem coordSupport_prefixBarycenter {n k : ℕ} [NeZero k] :
    coordSupport (prefixBarycenter n k) = prefixRooms n k := by
  ext i
  have hkR : (k : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne k)
  by_cases hi : i.1 < k
  · simp [coordSupport, prefixRooms, prefixBarycenter, hi, hkR]
  · simp [coordSupport, prefixRooms, prefixBarycenter, hi, hkR]

theorem prefixBarycenter_mem_scaledSimplex {n k : ℕ} [NeZero k] (hk : k ≤ n) :
    prefixBarycenter n k ∈ scaledSimplex 1 n := by
  constructor
  · intro i
    by_cases hi : i.1 < k
    · have hk0 : 0 < (k : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
      simp [prefixBarycenter, hi, le_of_lt (inv_pos.mpr hk0)]
    · simp [prefixBarycenter, hi]
  · have hkR : (k : ℝ) ≠ 0 := by
      exact_mod_cast (NeZero.ne k)
    let s : ℝ := Finset.sum (prefixRooms n k) (fun _ : RoomIndex n => (k : ℝ)⁻¹)
    have hsum : (∑ i, prefixBarycenter n k i) = s := by
      dsimp [s, prefixRooms]
      rw [Finset.sum_filter]
      simp [prefixBarycenter]
    calc
      (∑ i, prefixBarycenter n k i) = s := hsum
      _ = ((prefixRooms n k).card : ℝ) * (k : ℝ)⁻¹ := by
            dsimp [s]
            simp
      _ = (k : ℝ) * (k : ℝ)⁻¹ := by
            simp [prefixRooms_card hk]
      _ = (1 : ℝ) := by
            exact mul_inv_cancel₀ hkR
      _ = ((1 : ℕ) : ℝ) := by
            norm_num

/-- Relative-interior membership in one ambient coordinate face, encoded by full support on that
face. -/
def IsInteriorPointOfAmbientFace {n : ℕ} (I : Finset (RoomIndex n))
    (y : RentCoordinates n) : Prop :=
  y ∈ ambientCoordinateFace I ∧ coordSupport y = I

theorem prefixBarycenter_mem_ambientCoordinateFace {n k : ℕ} [NeZero k] (hk : k ≤ n) :
    prefixBarycenter n k ∈ ambientCoordinateFace (prefixRooms n k) := by
  refine ⟨prefixBarycenter_mem_scaledSimplex hk, ?_⟩
  simp [coordSupport_prefixBarycenter]

theorem prefixBarycenter_isInteriorPointOfAmbientFace {n k : ℕ} [NeZero k] (hk : k ≤ n) :
    IsInteriorPointOfAmbientFace (prefixRooms n k) (prefixBarycenter n k) := by
  exact ⟨prefixBarycenter_mem_ambientCoordinateFace hk, coordSupport_prefixBarycenter⟩

@[simp]
theorem prefixBarycenter_self_eq_rentBarycenter (n : ℕ) [NeZero n] :
    prefixBarycenter n n = ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  funext i
  rw [prefixBarycenter_apply_of_lt i.2]
  exact (rentBarycenter_apply (n := n) i).symm

/-- The Section 5 chain segment joining consecutive prefix-face barycenters. -/
def prefixBarycenterSegment (n k : ℕ) : Set (RentCoordinates n) :=
  segment ℝ (prefixBarycenter n k) (prefixBarycenter n (k + 1))

theorem mem_prefixBarycenterSegment_iff_exists_lineMap {n k : ℕ}
    {y : RentCoordinates n} :
    y ∈ prefixBarycenterSegment n k ↔
      ∃ t ∈ Set.Icc (0 : ℝ) 1,
        AffineMap.lineMap (prefixBarycenter n k) (prefixBarycenter n (k + 1)) t = y := by
  rw [prefixBarycenterSegment, segment_eq_image_lineMap, Set.mem_image]

theorem LinearMap.map_eq_prefixBarycenter_of_mem_prefixBarycenterSegment
    {n k : ℕ} {β : Type*} [AddCommGroup β] [Module ℝ β]
    (L : RentCoordinates n →ₗ[ℝ] β)
    (hL : L (prefixBarycenter n (k + 1) - prefixBarycenter n k) = 0)
    {y : RentCoordinates n} (hy : y ∈ prefixBarycenterSegment n k) :
    L y = L (prefixBarycenter n k) := by
  rcases mem_prefixBarycenterSegment_iff_exists_lineMap.mp hy with ⟨t, _ht, rfl⟩
  have hEq : L (prefixBarycenter n (k + 1)) = L (prefixBarycenter n k) := by
    exact sub_eq_zero.mp <| by simpa using hL
  calc
    L (AffineMap.lineMap (prefixBarycenter n k) (prefixBarycenter n (k + 1)) t) =
        (1 - t) • L (prefixBarycenter n k) + t • L (prefixBarycenter n (k + 1)) := by
          simp [AffineMap.lineMap_apply_module, map_add]
    _ = (1 - t) • L (prefixBarycenter n k) + t • L (prefixBarycenter n k) := by
          rw [hEq]
    _ = ((1 - t) + t) • L (prefixBarycenter n k) := by
          rw [← add_smul]
    _ = L (prefixBarycenter n k) := by
          simp

theorem FaceHitWitness.eq_under_segmentCollapse_of_mem_prefixBarycenterSegment
    {n : ℕ} {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {σ : SimplexFacet n} {y : RentCoordinates n}
    (hw : FaceHitWitness T f σ y) {k : ℕ}
    {β : Type*} [AddCommGroup β] [Module ℝ β]
    (L : RentCoordinates n →ₗ[ℝ] β)
    (hL : L (prefixBarycenter n (k + 1) - prefixBarycenter n k) = 0)
    (hy : y ∈ prefixBarycenterSegment n k) :
    L (hw.affineMap hw.point) = L (prefixBarycenter n k) := by
  simpa [hw.point_image] using
    LinearMap.map_eq_prefixBarycenter_of_mem_prefixBarycenterSegment
      (n := n) (k := k) L hL hy

theorem prefixBarycenterSegment_subset_ambientCoordinateFace {n k : ℕ} [NeZero k]
    (hk : k + 1 ≤ n) :
    prefixBarycenterSegment n k ⊆ ambientCoordinateFace (prefixRooms n (k + 1)) := by
  have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
  haveI : NeZero (k + 1) := ⟨Nat.succ_ne_zero k⟩
  refine (convex_ambientCoordinateFace _).segment_subset ?_ ?_
  · exact ambientCoordinateFace_mono (prefixRooms_mono (Nat.le_succ k))
      (prefixBarycenter_mem_ambientCoordinateFace hk')
  · exact prefixBarycenter_mem_ambientCoordinateFace hk

theorem eq_prefixBarycenter_of_mem_prefixBarycenterSegment_of_mem_lowerAmbientFace
    {n k : ℕ} [NeZero k] (hk : k + 1 ≤ n) {y : RentCoordinates n}
    (hySeg : y ∈ prefixBarycenterSegment n k)
    (hyFace : y ∈ ambientCoordinateFace (prefixRooms n k)) :
    y = prefixBarycenter n k := by
  rcases mem_prefixBarycenterSegment_iff_exists_lineMap.mp hySeg with ⟨t, _ht, hline⟩
  let i : RoomIndex n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
  have hi_not_mem : i ∉ prefixRooms n k := by
    simp [i, mem_prefixRooms_iff]
  have hyi0 : y i = 0 := (coordSupport_subset_iff.mp hyFace.2) i hi_not_mem
  have hi_not_lt : ¬ i.1 < k := by
    simp [i]
  have hi_lt_succ : i.1 < k + 1 := by
    simp [i]
  have hyi :
      y i = t * ((k + 1 : ℝ)⁻¹) := by
    rw [← hline, AffineMap.lineMap_apply_module]
    simp [prefixBarycenter, hi_not_lt, hi_lt_succ, mul_comm]
  have hmul :
      t * ((k + 1 : ℝ)⁻¹) = 0 := by
    rw [hyi0] at hyi
    exact hyi.symm
  have hk1_ne : ((k + 1 : ℝ)⁻¹) ≠ 0 := by
    exact inv_ne_zero <| by exact_mod_cast Nat.succ_ne_zero k
  have ht0 : t = 0 := (mul_eq_zero.mp hmul).resolve_right hk1_ne
  calc
    y = AffineMap.lineMap (prefixBarycenter n k) (prefixBarycenter n (k + 1)) t := by
          exact hline.symm
    _ = prefixBarycenter n k := by
          simp [ht0]

/-- The first barycenter `b_1`, viewed as a simplex vertex, is the Section 5 start point. -/
def section5StartVertex (n : ℕ) [NeZero n] : RentSimplex n :=
  ⟨prefixBarycenter n 1, by
    simpa [RentSimplex, scaledSimplex] using
      (prefixBarycenter_mem_scaledSimplex (n := n) (k := 1) <|
        Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n)))⟩

/-- The singleton cell at the Section 5 starting vertex. -/
def section5StartCell (n : ℕ) [NeZero n] : SimplexFacet n where
  vertices := {section5StartVertex n}

theorem section5StartVertex_eq_vertex_zero (n : ℕ) [NeZero n] :
    section5StartVertex n = stdSimplex.vertex (S := ℝ) (0 : RoomIndex n) := by
  refine eq_vertex_of_apply_eq_one ?_
  simp [section5StartVertex, prefixBarycenter]

theorem section5StartVertex_mem_coordinateFace (n : ℕ) [NeZero n] :
    section5StartVertex n ∈ coordinateFace (prefixRooms n 1) := by
  rw [mem_coordinateFace_iff]
  intro i hi
  have hi' : ¬ i.1 < 1 := by
    simpa [mem_prefixRooms_iff] using hi
  simp [section5StartVertex, prefixBarycenter, hi']

@[simp]
theorem section5SecondVertex_apply_second {n : ℕ} (hn : 2 ≤ n) :
    (section5SecondVertex n hn).1 (section5SecondIndex hn) = 1 := by
  simp [section5SecondVertex]

@[simp]
theorem section5SecondVertex_apply_first {n : ℕ} (hn : 2 ≤ n) :
    (section5SecondVertex n hn).1 (section5FirstIndex hn) = 0 := by
  simp [section5SecondVertex, section5SecondIndex_ne_zero hn]

theorem section5SecondVertex_mem_coordinateFace_two (n : ℕ) (hn : 2 ≤ n) :
    section5SecondVertex n hn ∈ coordinateFace (prefixRooms n 2) := by
  rw [mem_coordinateFace_iff]
  intro i hi
  have hne : i ≠ section5SecondIndex hn := by
    intro h
    subst h
    exact hi (by simp [mem_prefixRooms_iff, section5SecondIndex])
  simp [section5SecondVertex, hne]

theorem section5Boundary_sum_two {n : ℕ} [NeZero n] (hn : 2 ≤ n) {x : RentSimplex n}
    (hx : x ∈ coordinateFace (prefixRooms n 2)) :
    x.1 (0 : RoomIndex n) + x.1 (section5SecondIndex hn) = 1 := by
  have hsum :
      ∑ i ∈ prefixRooms n 2, x.1 i = (1 : ℝ) := by
    calc
      ∑ i ∈ prefixRooms n 2, x.1 i
          = ∑ i, x.1 i := by
              rw [prefixRooms, Finset.sum_filter]
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hi2 : i.1 < 2
              · simp [hi2]
              · have hxi : x.1 i = 0 := by
                  exact (mem_coordinateFace_iff.mp hx) i
                    (by simpa [mem_prefixRooms_iff] using hi2)
                simp [hi2, hxi]
      _ = (1 : ℝ) := by simpa using x.2.2
  rw [prefixRooms_two_eq_pair hn, Finset.sum_insert, Finset.sum_singleton] at hsum
  · simpa [section5FirstIndex_eq_zero hn, add_comm] using hsum
  · simpa [Finset.mem_singleton] using (section5SecondIndex_ne_zero hn).symm

theorem section5Boundary_eq_lineMap_of_mem_coordinateFace_two {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    {x : RentSimplex n} (hx : x ∈ coordinateFace (prefixRooms n 2)) :
    ((x : RentSimplex n) : RentCoordinates n) =
      AffineMap.lineMap (section5StartVertex n : RentCoordinates n)
        (section5SecondVertex n hn : RentCoordinates n) (x.1 (section5SecondIndex hn)) := by
  ext i
  by_cases h0 : i = (0 : RoomIndex n)
  · subst h0
    have hsum := section5Boundary_sum_two hn hx
    have hx0 :
        x.1 (0 : RoomIndex n) = 1 - x.1 (section5SecondIndex hn) := by
      linarith
    have hsecond0 : section5SecondIndex hn ≠ (0 : RoomIndex n) := by
      simpa [section5FirstIndex_eq_zero hn] using section5SecondIndex_ne_zero hn
    rw [AffineMap.lineMap_apply_module]
    rw [section5StartVertex_eq_vertex_zero]
    simpa [section5SecondVertex, hsecond0] using hx0
  · by_cases h1 : i = section5SecondIndex hn
    · subst h1
      have hsecond0 : section5SecondIndex hn ≠ (0 : RoomIndex n) := by
        simpa [section5FirstIndex_eq_zero hn] using section5SecondIndex_ne_zero hn
      rw [AffineMap.lineMap_apply_module]
      rw [section5StartVertex_eq_vertex_zero]
      simp [section5SecondVertex, hsecond0]
      rfl
    · have hi : i ∉ prefixRooms n 2 := by
        rw [prefixRooms_two_eq_pair hn]
        simp [section5FirstIndex_eq_zero hn, h0, h1]
      have hxi : x.1 i = 0 := (mem_coordinateFace_iff.mp hx) i hi
      rw [AffineMap.lineMap_apply_module]
      rw [section5StartVertex_eq_vertex_zero]
      simpa [section5SecondVertex, h0, h1] using hxi

theorem collinear_boundary_vertices {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    {x y z : RentSimplex n}
    (hx : x ∈ coordinateFace (prefixRooms n 2))
    (hy : y ∈ coordinateFace (prefixRooms n 2))
    (hz : z ∈ coordinateFace (prefixRooms n 2)) :
    Collinear ℝ ({((x : RentSimplex n) : RentCoordinates n),
      ((y : RentSimplex n) : RentCoordinates n),
      ((z : RentSimplex n) : RentCoordinates n)} : Set (RentCoordinates n)) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨(section5StartVertex n : RentCoordinates n),
    (section5SecondVertex n hn : RentCoordinates n) - section5StartVertex n, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · refine ⟨x.1 (section5SecondIndex hn), ?_⟩
    rw [section5Boundary_eq_lineMap_of_mem_coordinateFace_two hn hx, AffineMap.lineMap_apply]
    simp
  · refine ⟨y.1 (section5SecondIndex hn), ?_⟩
    rw [section5Boundary_eq_lineMap_of_mem_coordinateFace_two hn hy, AffineMap.lineMap_apply]
    simp
  · refine ⟨z.1 (section5SecondIndex hn), ?_⟩
    rw [section5Boundary_eq_lineMap_of_mem_coordinateFace_two hn hz, AffineMap.lineMap_apply]
    simp

/-- The triangulation vertices of one facet that lie on the prefix face
`conv{e₁, ..., e_{k+1}}`. -/
def SimplexFacet.section5PrefixVertices {n : ℕ}
    (τ : SimplexFacet n) (k : ℕ) : Finset (RentSimplex n) := by
  classical
  exact τ.vertices.filter fun v => v ∈ coordinateFace (prefixRooms n (k + 1))

@[simp]
theorem SimplexFacet.mem_section5PrefixVertices_iff {n : ℕ} {τ : SimplexFacet n} {k : ℕ}
    {v : RentSimplex n} :
    v ∈ τ.section5PrefixVertices k ↔
      v ∈ τ.vertices ∧ v ∈ coordinateFace (prefixRooms n (k + 1)) := by
  classical
  simp [SimplexFacet.section5PrefixVertices]

/-- The induced face of one facet lying on the prefix face `conv{e₁, ..., e_{k+1}}`. -/
def SimplexFacet.section5PrefixFace {n : ℕ} (τ : SimplexFacet n) (k : ℕ) : SimplexFacet n where
  vertices := τ.section5PrefixVertices k

@[simp]
theorem SimplexFacet.section5PrefixFace_vertices {n : ℕ} (τ : SimplexFacet n) (k : ℕ) :
    (τ.section5PrefixFace k).vertices = τ.section5PrefixVertices k :=
  rfl

theorem SimplexFacet.section5PrefixFace_isSubface {n : ℕ} (τ : SimplexFacet n) (k : ℕ) :
    (τ.section5PrefixFace k).IsSubfaceOf τ := by
  intro v hv
  exact (τ.mem_section5PrefixVertices_iff.mp hv).1

theorem SimplexTriangulation.section5PrefixFace_isFace {n : ℕ} {T : SimplexTriangulation n}
    {τ : SimplexFacet n} (hτ : τ ∈ T.facets) (k : ℕ) :
    T.IsFace (τ.section5PrefixFace k) :=
  ⟨τ, hτ, τ.section5PrefixFace_isSubface k⟩

/-- The standard vertices spanning the prefix face `conv{e₁, ..., e_{k+1}}`. -/
def prefixFaceStdVertices (n k : ℕ) : Finset (RentCoordinates n) :=
  (prefixRooms n (k + 1)).image fun i : RoomIndex n =>
    ((stdSimplex.vertex (S := ℝ) i : RentSimplex n) : RentCoordinates n)

theorem prefixFaceStdVertices_card {n k : ℕ} (hk : k + 1 ≤ n) :
    (prefixFaceStdVertices n k).card = k + 1 := by
  classical
  unfold prefixFaceStdVertices
  rw [Finset.card_image_of_injective]
  · exact prefixRooms_card hk
  · intro i j hij
    have hval : i.1 = j.1 := by
      by_contra hne
      have hcoord :
          (((stdSimplex.vertex (S := ℝ) j : RentSimplex n) : RentCoordinates n) i) = 1 := by
        simpa using congrArg (fun p : RentCoordinates n => p i) hij.symm
      have hcoord0 :
          (((stdSimplex.vertex (S := ℝ) j : RentSimplex n) : RentCoordinates n) i) = 0 := by
        have hji : j ≠ i := by
          intro h
          exact hne (congrArg Fin.val h.symm)
        simp [hji]
      linarith
    exact Fin.ext hval

theorem mem_affineSpan_prefixFaceStdVertices_of_mem_coordinateFace {n k : ℕ}
    {x : RentSimplex n} (hx : x ∈ coordinateFace (prefixRooms n (k + 1))) :
    ((x : RentSimplex n) : RentCoordinates n) ∈
      affineSpan ℝ ((prefixFaceStdVertices n k : Finset (RentCoordinates n)) :
        Set (RentCoordinates n)) := by
  classical
  let I : Finset (RoomIndex n) := prefixRooms n (k + 1)
  let p : I → RentCoordinates n := fun i =>
    ((stdSimplex.vertex (S := ℝ) (i : RoomIndex n) : RentSimplex n) : RentCoordinates n)
  let w : I → ℝ := fun i => x.1 i
  have hsumI : ∑ i ∈ I, x.1 i = (1 : ℝ) := by
    calc
      ∑ i ∈ I, x.1 i = ∑ i, x.1 i := by
        dsimp [I]
        rw [prefixRooms, Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hi' : i.1 < k + 1
        · simp [hi']
        · have hxi : x.1 i = 0 := by
            exact (mem_coordinateFace_iff.mp hx) i
              (by simpa [mem_prefixRooms_iff] using hi')
          simp [hi', hxi]
      _ = (1 : ℝ) := by simpa using x.2.2
  have hw1 : ∑ i, w i = (1 : ℝ) := by
    rw [← Finset.attach_eq_univ (s := I)]
    rw [Finset.sum_attach]
    simpa [w] using hsumI
  have hcomb :
      (Finset.univ.affineCombination ℝ p w : RentCoordinates n) =
        ((x : RentSimplex n) : RentCoordinates n) := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1]
    ext j
    by_cases hj : j ∈ I
    · let jI : I := ⟨j, hj⟩
      rw [show (∑ i : I, w i • p i) j =
          ∑ i : I, x.1 i *
            (((stdSimplex.vertex (S := ℝ) (i : RoomIndex n) : RentSimplex n) :
              RentCoordinates n) j) by
            simp [w, p]]
      rw [Finset.sum_eq_single jI]
      · have hjVertex :
            (((stdSimplex.vertex (S := ℝ) (jI : RoomIndex n) : RentSimplex n) :
              RentCoordinates n) j) = 1 := by
          simp [jI]
        rw [hjVertex]
        rw [mul_one]
        rfl
      · intro i _ hij
        have hij' : (i : RoomIndex n) ≠ j := by
          intro hEq
          exact hij (Subtype.ext hEq)
        simp [hij']
      · simp [jI]
    · have hsum_zero :
          ∑ i : I, x.1 i *
            (((stdSimplex.vertex (S := ℝ) (i : RoomIndex n) : RentSimplex n) :
              RentCoordinates n) j) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hij' : (i : RoomIndex n) ≠ j := by
          intro hEq
          exact hj (hEq ▸ i.2)
        simp [hij']
      have hxj : x.1 j = 0 := by
        exact (mem_coordinateFace_iff.mp hx) j hj
      rw [show (∑ i : I, w i • p i) j =
          ∑ i : I, x.1 i *
            (((stdSimplex.vertex (S := ℝ) (i : RoomIndex n) : RentSimplex n) :
              RentCoordinates n) j) by
            simp [w, p]]
      calc
        ∑ i : I, x.1 i *
            (((stdSimplex.vertex (S := ℝ) (i : RoomIndex n) : RentSimplex n) :
              RentCoordinates n) j) = 0 := hsum_zero
        _ = x j := by simpa using hxj.symm
  have hrange :
      Set.range p =
        ((prefixFaceStdVertices n k : Finset (RentCoordinates n)) : Set (RentCoordinates n)) := by
    ext y
    simp [prefixFaceStdVertices, p, I]
  have hxSpan :
      ((x : RentSimplex n) : RentCoordinates n) ∈ affineSpan ℝ (Set.range p) := by
    rw [← hcomb]
    exact affineCombination_mem_affineSpan hw1 p
  simpa [hrange] using hxSpan

theorem SimplexTriangulation.prefixVertices_card_le_of_isFace {n : ℕ}
    (T : SimplexTriangulation n) {σ : SimplexFacet n} (hσ : T.IsFace σ)
    {k : ℕ} (hk : k + 1 ≤ n) :
    (σ.section5PrefixVertices k).card ≤ k + 1 := by
  classical
  rcases hσ with ⟨τ, hτ, hστ⟩
  let sCoords : Finset (RentCoordinates n) :=
    (σ.section5PrefixVertices k).image fun v : RentSimplex n =>
      ((v : RentSimplex n) : RentCoordinates n)
  let pτ : τ.vertices → RentCoordinates n := fun v =>
    ((v : RentSimplex n) : RentCoordinates n)
  have hτind :
      AffineIndependent ℝ (fun x => x : Set.range pτ → RentCoordinates n) :=
    (T.facet_affineIndependent τ hτ).range
  have hsSubset : (sCoords : Set (RentCoordinates n)) ⊆ Set.range pτ := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
    exact ⟨⟨v, hστ (σ.mem_section5PrefixVertices_iff.mp hv).1⟩, rfl⟩
  let emb : sCoords ↪ Set.range pτ := {
    toFun := fun y => ⟨y, hsSubset y.2⟩
    inj' := by
      intro y z hyz
      have hval : (y : RentCoordinates n) = (z : RentCoordinates n) :=
        by simpa using congrArg (fun t : Set.range pτ => (t : RentCoordinates n)) hyz
      exact Subtype.ext hval }
  have hsAff : AffineIndependent ℝ (fun x : sCoords => (x : RentCoordinates n)) := by
    simpa [emb] using hτind.comp_embedding emb
  have hsSpan :
      (sCoords : Set (RentCoordinates n)) ⊆
        affineSpan ℝ ((prefixFaceStdVertices n k : Finset (RentCoordinates n)) :
          Set (RentCoordinates n)) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
    exact mem_affineSpan_prefixFaceStdVertices_of_mem_coordinateFace
      ((σ.mem_section5PrefixVertices_iff.mp hv).2)
  have hsCard :
      sCoords.card ≤ (prefixFaceStdVertices n k).card :=
    hsAff.card_le_card_of_subset_affineSpan hsSpan
  have hsCard' : sCoords.card = (σ.section5PrefixVertices k).card := by
    dsimp [sCoords]
    rw [Finset.card_image_of_injective]
    intro a b hab
    exact Subtype.ext hab
  calc
    (σ.section5PrefixVertices k).card = sCoords.card := hsCard'.symm
    _ ≤ (prefixFaceStdVertices n k).card := hsCard
    _ = k + 1 := prefixFaceStdVertices_card hk

/-- The triangulation vertices of one facet that lie on the boundary edge `[e₁,e₂]`. -/
abbrev SimplexFacet.section5BoundaryVertices {n : ℕ}
    (τ : SimplexFacet n) : Finset (RentSimplex n) :=
  τ.section5PrefixVertices 1

/-- The induced face of one facet lying on the boundary edge `[e₁,e₂]`. -/
abbrev SimplexFacet.section5BoundaryFace {n : ℕ} (τ : SimplexFacet n) : SimplexFacet n :=
  τ.section5PrefixFace 1

@[simp]
theorem SimplexFacet.mem_section5BoundaryVertices_iff {n : ℕ} {τ : SimplexFacet n}
    {v : RentSimplex n} :
    v ∈ τ.section5BoundaryVertices ↔ v ∈ τ.vertices ∧ v ∈ coordinateFace (prefixRooms n 2) := by
  simp [SimplexFacet.section5BoundaryVertices, SimplexFacet.section5PrefixVertices]

@[simp]
theorem SimplexFacet.section5BoundaryFace_vertices {n : ℕ} (τ : SimplexFacet n) :
    τ.section5BoundaryFace.vertices = τ.section5BoundaryVertices :=
  rfl

theorem SimplexFacet.section5BoundaryFace_isSubface {n : ℕ} (τ : SimplexFacet n) :
    τ.section5BoundaryFace.IsSubfaceOf τ := by
  simpa [SimplexFacet.section5BoundaryFace] using τ.section5PrefixFace_isSubface 1

theorem SimplexTriangulation.section5BoundaryFace_isFace {n : ℕ} {T : SimplexTriangulation n}
    {τ : SimplexFacet n} (hτ : τ ∈ T.facets) :
    T.IsFace τ.section5BoundaryFace := by
  simpa [SimplexFacet.section5BoundaryFace] using T.section5PrefixFace_isFace hτ 1

theorem SimplexTriangulation.boundaryVertices_card_le_two {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (T : SimplexTriangulation n) {τ : SimplexFacet n} (hτ : τ ∈ T.facets) :
    τ.section5BoundaryVertices.card ≤ 2 := by
  simpa [SimplexFacet.section5BoundaryVertices] using
    T.prefixVertices_card_le_of_isFace (T.facet_isFace hτ) (k := 1) hn

theorem exists_nonstart_boundary_vertex_of_mem_convexHull {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    {s : Finset (RentSimplex n)} {y : RentSimplex n}
    (hy : y ∈ coordinateFace (prefixRooms n 2))
    (hy_ne : y ≠ section5StartVertex n)
    (hyConv :
      ((y : RentSimplex n) : RentCoordinates n) ∈
        convexHull ℝ
          ((s.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n)) :
            Set (RentCoordinates n))) :
    ∃ v ∈ s, v ∈ coordinateFace (prefixRooms n 2) ∧ v ≠ section5StartVertex n := by
  classical
  let s' : Finset (RentCoordinates n) :=
    s.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n)
  have hyConv' : ((y : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ (s' : Set _) := by
    simpa [s'] using hyConv
  rcases (Finset.mem_convexHull (R := ℝ) (s := s')
      (x := ((y : RentSimplex n) : RentCoordinates n))).mp hyConv' with
    ⟨w, hw0, hw1, hcenter⟩
  rw [Finset.centerMass_eq_of_sum_1 (t := s') (w := w) (z := id) hw1] at hcenter
  have hy_pos : 0 < y.1 (section5SecondIndex hn) := by
    have hy_nonneg : 0 ≤ y.1 (section5SecondIndex hn) := y.2.1 (section5SecondIndex hn)
    by_cases hy_zero : y.1 (section5SecondIndex hn) = 0
    · have hy_first : y.1 (0 : RoomIndex n) = 1 := by
        have hsum := section5Boundary_sum_two hn hy
        linarith
      have hy_eq_start : y = section5StartVertex n := by
        rw [section5StartVertex_eq_vertex_zero]
        exact eq_vertex_of_apply_eq_one hy_first
      exact False.elim (hy_ne hy_eq_start)
    · exact lt_of_le_of_ne hy_nonneg (Ne.symm hy_zero)
  have hcoord_second :
      ∑ p ∈ s', w p * p (section5SecondIndex hn) = y.1 (section5SecondIndex hn) := by
    have := congrArg (fun z : RentCoordinates n => z (section5SecondIndex hn)) hcenter
    simpa [Finset.sum_apply, Pi.smul_apply, mul_comm, mul_left_comm, mul_assoc] using this
  have hexists :
      ∃ p ∈ s', w p ≠ 0 ∧ p (section5SecondIndex hn) ≠ 0 := by
    by_contra hnone
    have hsum_zero : ∑ p ∈ s', w p * p (section5SecondIndex hn) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      by_cases hwp : w p = 0
      · simp [hwp]
      · have hpzero : p (section5SecondIndex hn) = 0 := by
          by_contra hpzero
          exact hnone ⟨p, hp, hwp, hpzero⟩
        simp [hpzero]
    exact hy_pos.ne' (hcoord_second.symm.trans hsum_zero)
  rcases hexists with ⟨p, hp, hwp, hpsecond⟩
  rcases Finset.mem_image.mp hp with ⟨v, hv, rfl⟩
  have hvFace : v ∈ coordinateFace (prefixRooms n 2) := by
    rw [mem_coordinateFace_iff]
    intro i hi
    have hcoord_i :
        ∑ q ∈ s', w q * q i = 0 := by
      have := congrArg (fun z : RentCoordinates n => z i) hcenter
      have hyi : y.1 i = 0 := (mem_coordinateFace_iff.mp hy) i hi
      have hyi' : (((y : RentSimplex n) : RentCoordinates n) i) = 0 := by
        simpa using hyi
      simpa [Finset.sum_apply, Pi.smul_apply, mul_comm, mul_left_comm, mul_assoc, hyi'] using this
    have hnonneg : ∀ q ∈ s', 0 ≤ w q * q i := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨u, hu, rfl⟩
      exact mul_nonneg (hw0 _ (by exact Finset.mem_image.mpr ⟨u, hu, rfl⟩)) (u.2.1 i)
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hcoord_i
    exact (mul_eq_zero.mp (hterms _ hp)).resolve_left hwp
  have hv_ne : v ≠ section5StartVertex n := by
    intro hvEq
    have hsecond0 : section5SecondIndex hn ≠ (0 : RoomIndex n) := by
      simpa [section5FirstIndex_eq_zero hn] using section5SecondIndex_ne_zero hn
    have : (section5StartVertex n).1 (section5SecondIndex hn) = 0 := by
      rw [section5StartVertex_eq_vertex_zero]
      simp [hsecond0]
    exact hpsecond (by simpa [hvEq] using this)
  exact ⟨v, hv, hvFace, hv_ne⟩

theorem secondCoord_lower_bound_of_mem_convexHull {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    {s : Finset (RentSimplex n)} {x : RentSimplex n} {c : ℝ}
    (hxConv :
      ((x : RentSimplex n) : RentCoordinates n) ∈
        convexHull ℝ
          ((s.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n)) :
            Set (RentCoordinates n)))
    (hbound : ∀ v ∈ s, c ≤ v.1 (section5SecondIndex hn)) :
    c ≤ x.1 (section5SecondIndex hn) := by
  let s' : Finset (RentCoordinates n) :=
    s.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n)
  have hxConv' : ((x : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ (s' : Set _) := by
    simpa [s'] using hxConv
  rcases (Finset.mem_convexHull (R := ℝ) (s := s')
      (x := ((x : RentSimplex n) : RentCoordinates n))).mp hxConv' with
    ⟨w, hw0, hw1, hcenter⟩
  rw [Finset.centerMass_eq_of_sum_1 (t := s') (w := w) (z := id) hw1] at hcenter
  have hcoord_second :
      ∑ p ∈ s', w p * p (section5SecondIndex hn) = x.1 (section5SecondIndex hn) := by
    have := congrArg (fun z : RentCoordinates n => z (section5SecondIndex hn)) hcenter
    simpa [Finset.sum_apply, Pi.smul_apply, mul_comm, mul_left_comm, mul_assoc] using this
  have hsum_bound :
      c * ∑ p ∈ s', w p ≤ ∑ p ∈ s', w p * p (section5SecondIndex hn) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨v, hv, rfl⟩
    simpa [mul_comm c, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_left (hbound v hv) <|
        hw0 _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
  calc
    c = c * ∑ p ∈ s', w p := by rw [hw1]; ring
    _ ≤ ∑ p ∈ s', w p * p (section5SecondIndex hn) := hsum_bound
    _ = x.1 (section5SecondIndex hn) := hcoord_second

theorem secondCoord_lower_bound_of_mem_realization {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    {τ : SimplexFacet n} {x : RentSimplex n} {c : ℝ}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization)
    (hbound : ∀ v ∈ τ.vertices, c ≤ v.1 (section5SecondIndex hn)) :
    c ≤ x.1 (section5SecondIndex hn) := by
  exact secondCoord_lower_bound_of_mem_convexHull hn
    (by simpa [SimplexFacet.realization, SimplexFacet.pointSet] using hxτ) hbound

theorem
    SimplexFacet.mem_section5PrefixFace_realization_of_mem_realization_of_mem_coordinateFace
    {n : ℕ} [NeZero n] {τ : SimplexFacet n} {x : RentSimplex n}
    {k : ℕ} (hx : x ∈ coordinateFace (prefixRooms n (k + 1)))
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization) :
    ((x : RentSimplex n) : RentCoordinates n) ∈ (τ.section5PrefixFace k).realization := by
  classical
  let s' : Finset (RentCoordinates n) :=
    τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n)
  let b' : Finset (RentCoordinates n) :=
    (τ.section5PrefixVertices k).image fun v : RentSimplex n =>
      ((v : RentSimplex n) : RentCoordinates n)
  have hxConv : ((x : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ (s' : Set _) := by
    simpa [s'] using hxτ
  rcases (Finset.mem_convexHull (R := ℝ) (s := s')
      (x := ((x : RentSimplex n) : RentCoordinates n))).mp hxConv with
    ⟨w, hw0, hw1, hcenter⟩
  rw [Finset.centerMass_eq_of_sum_1 (t := s') (w := w) (z := id) hw1] at hcenter
  have hbSubset : b' ⊆ s' := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨v, hv, rfl⟩
    exact Finset.mem_image.mpr ⟨v, (τ.mem_section5PrefixVertices_iff.mp hv).1, rfl⟩
  have hw_zero_outside :
      ∀ p ∈ s', p ∉ b' → w p = 0 := by
    intro p hp hpb
    by_contra hwp
    rcases Finset.mem_image.mp hp with ⟨v, hv, rfl⟩
    have hvFace : v ∈ coordinateFace (prefixRooms n (k + 1)) := by
      rw [mem_coordinateFace_iff]
      intro i hi
      have hcoord_i :
          ∑ q ∈ s', w q * q i = 0 := by
        have := congrArg (fun z : RentCoordinates n => z i) hcenter
        have hxi : x.1 i = 0 := (mem_coordinateFace_iff.mp hx) i hi
        have hxi' : (((x : RentSimplex n) : RentCoordinates n) i) = 0 := by
          simpa using hxi
        simpa [Finset.sum_apply, Pi.smul_apply, mul_comm, mul_left_comm, mul_assoc, hxi'] using this
      have hnonneg : ∀ q ∈ s', 0 ≤ w q * q i := by
        intro q hq
        rcases Finset.mem_image.mp hq with ⟨u, hu, rfl⟩
        exact mul_nonneg (hw0 _ (by exact Finset.mem_image.mpr ⟨u, hu, rfl⟩)) (u.2.1 i)
      have hterms := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hcoord_i
      exact (mul_eq_zero.mp (hterms _ hp)).resolve_left hwp
    exact hpb <| Finset.mem_image.mpr
      ⟨v, τ.mem_section5PrefixVertices_iff.mpr ⟨hv, hvFace⟩, rfl⟩
  have hw0b : ∀ p ∈ b', 0 ≤ w p := by
    intro p hp
    exact hw0 _ (hbSubset hp)
  have hw1b : ∑ p ∈ b', w p = 1 := by
    calc
      ∑ p ∈ b', w p = ∑ p ∈ s', w p := by
        exact Finset.sum_subset hbSubset (by
          intro p hp hpb
          exact hw_zero_outside p hp hpb)
      _ = 1 := hw1
  have hxBoundary :
      ((x : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ (b' : Set (RentCoordinates n)) := by
    refine (Finset.mem_convexHull (R := ℝ) (s := b')
      (x := ((x : RentSimplex n) : RentCoordinates n))).mpr ?_
    refine ⟨w, hw0b, hw1b, ?_⟩
    rw [Finset.centerMass_eq_of_sum_1 (t := b') (w := w) (z := id) hw1b]
    calc
      ∑ p ∈ b', w p • p = ∑ p ∈ s', w p • p := by
        exact Finset.sum_subset hbSubset (by
          intro p hp hpb
          simp [hw_zero_outside p hp hpb])
      _ = ((x : RentSimplex n) : RentCoordinates n) := by
        simpa using hcenter
  rw [SimplexFacet.section5PrefixFace, SimplexFacet.realization, SimplexFacet.pointSet]
  simpa [b'] using hxBoundary

theorem
    SimplexFacet.mem_section5BoundaryFace_realization_of_mem_realization_of_mem_coordinateFace_two
    {n : ℕ} [NeZero n] {τ : SimplexFacet n} {x : RentSimplex n}
    (hx : x ∈ coordinateFace (prefixRooms n 2))
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization) :
    ((x : RentSimplex n) : RentCoordinates n) ∈ τ.section5BoundaryFace.realization := by
  simpa [SimplexFacet.section5BoundaryFace] using
    (τ.mem_section5PrefixFace_realization_of_mem_realization_of_mem_coordinateFace
      (k := 1) hx hxτ)

theorem section5SecondVertex_ne_start {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    section5SecondVertex n hn ≠ section5StartVertex n := by
  intro h
  have hsecond : (section5SecondVertex n hn).1 (section5SecondIndex hn) = 1 :=
    section5SecondVertex_apply_second hn
  have hstart : (section5StartVertex n).1 (section5SecondIndex hn) = 0 := by
    rw [section5StartVertex_eq_vertex_zero]
    have hneq : section5SecondIndex hn ≠ (0 : RoomIndex n) := by
      simpa [section5FirstIndex_eq_zero hn] using section5SecondIndex_ne_zero hn
    simp [hneq]
  rw [h] at hsecond
  linarith [hsecond, hstart]

theorem SimplexTriangulation.exists_nonstart_section5BoundaryVertex {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (T : SimplexTriangulation n) :
    ∃ v ∈ T.vertices, v ∈ coordinateFace (prefixRooms n 2) ∧ v ≠ section5StartVertex n := by
  rcases T.covers_simplex (section5SecondVertex n hn) with ⟨τ, hτ, hreal⟩
  rcases exists_nonstart_boundary_vertex_of_mem_convexHull hn
      (section5SecondVertex_mem_coordinateFace_two n hn)
      (section5SecondVertex_ne_start hn)
      (by simpa [SimplexFacet.realization, SimplexFacet.pointSet] using hreal) with
    ⟨v, hvτ, hvFace, hvNe⟩
  exact ⟨v, T.mem_vertices_of_mem_facet hτ hvτ, hvFace, hvNe⟩

theorem SimplexTriangulation.exists_min_nonstart_section5BoundaryVertex {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (T : SimplexTriangulation n) :
    ∃ v ∈ T.vertices, v ∈ coordinateFace (prefixRooms n 2) ∧ v ≠ section5StartVertex n ∧
      ∀ w ∈ T.vertices, w ∈ coordinateFace (prefixRooms n 2) → w ≠ section5StartVertex n →
        v.1 (section5SecondIndex hn) ≤ w.1 (section5SecondIndex hn) := by
  classical
  let S : Finset (RentSimplex n) :=
    T.vertices.filter fun v => v ∈ coordinateFace (prefixRooms n 2) ∧ v ≠ section5StartVertex n
  have hSnonempty : S.Nonempty := by
    rcases T.exists_nonstart_section5BoundaryVertex hn with ⟨v, hvT, hvFace, hvNe⟩
    exact ⟨v, Finset.mem_filter.mpr ⟨hvT, hvFace, hvNe⟩⟩
  rcases Finset.exists_min_image S (fun v : RentSimplex n => v.1 (section5SecondIndex hn))
      hSnonempty with ⟨v, hvS, hmin⟩
  refine ⟨v, (Finset.mem_filter.mp hvS).1, (Finset.mem_filter.mp hvS).2.1,
    (Finset.mem_filter.mp hvS).2.2, ?_⟩
  intro w hwT hwFace hwNe
  exact hmin w (Finset.mem_filter.mpr ⟨hwT, hwFace, hwNe⟩)

/-- The midpoint of the boundary segment joining `e₁` to another simplex point. -/
def section5StartSegmentMidpoint {n : ℕ} [NeZero n] (v : RentSimplex n) : RentSimplex n := by
  refine ⟨AffineMap.lineMap (section5StartVertex n : RentCoordinates n)
    (v : RentCoordinates n) ((1 : ℝ) / 2), ?_⟩
  have hs : Convex ℝ (scaledSimplex 1 n) := by
    simpa [scaledSimplex, RentSimplex] using (convex_stdSimplex ℝ (RoomIndex n))
  have hstartSimplex : (section5StartVertex n : RentCoordinates n) ∈ scaledSimplex 1 n := by
    refine ⟨(section5StartVertex n).2.1, ?_⟩
    convert (section5StartVertex n).2.2 using 1
    simp
  have hvSimplex : (v : RentCoordinates n) ∈ scaledSimplex 1 n := by
    refine ⟨v.2.1, ?_⟩
    convert v.2.2 using 1
    simp
  have hmidSimplex :
      (AffineMap.lineMap (section5StartVertex n : RentCoordinates n)
        (v : RentCoordinates n) ((1 : ℝ) / 2)) ∈ scaledSimplex 1 n := by
    refine hs.segment_subset hstartSimplex hvSimplex ?_
    rw [segment_eq_image_lineMap, Set.mem_image]
    exact ⟨(1 : ℝ) / 2, by norm_num, rfl⟩
  simpa [RentSimplex, scaledSimplex] using hmidSimplex

theorem section5StartSegmentMidpoint_mem_coordinateFace_two {n : ℕ} [NeZero n]
    {v : RentSimplex n} (hv : v ∈ coordinateFace (prefixRooms n 2)) :
    section5StartSegmentMidpoint v ∈ coordinateFace (prefixRooms n 2) := by
  have hstartFace : section5StartVertex n ∈ coordinateFace (prefixRooms n 2) :=
    coordinateFace_mono (prefixRooms_mono (by decide : 1 ≤ 2))
      (section5StartVertex_mem_coordinateFace n)
  rw [mem_coordinateFace_iff]
  intro i hi
  have hstart0 : (section5StartVertex n).1 i = 0 := (mem_coordinateFace_iff.mp hstartFace) i hi
  have hv0 : v.1 i = 0 := (mem_coordinateFace_iff.mp hv) i hi
  change (AffineMap.lineMap (section5StartVertex n : RentCoordinates n)
      (v : RentCoordinates n) ((1 : ℝ) / 2)) i = 0
  rw [AffineMap.lineMap_apply_module]
  change (1 - (1 : ℝ) / 2) * (section5StartVertex n).1 i + ((1 : ℝ) / 2) * v.1 i = 0
  rw [hstart0, hv0]
  ring

theorem section5StartSegmentMidpoint_apply_second {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    {v : RentSimplex n} :
    (section5StartSegmentMidpoint v).1 (section5SecondIndex hn) =
      v.1 (section5SecondIndex hn) / 2 := by
  have hstart0 : (section5StartVertex n).1 (section5SecondIndex hn) = 0 := by
    rw [section5StartVertex_eq_vertex_zero]
    have hneq : section5SecondIndex hn ≠ (0 : RoomIndex n) := by
      simpa [section5FirstIndex_eq_zero hn] using section5SecondIndex_ne_zero hn
    simp [hneq]
  change (AffineMap.lineMap (section5StartVertex n : RentCoordinates n)
      (v : RentCoordinates n) ((1 : ℝ) / 2)) (section5SecondIndex hn) =
    v.1 (section5SecondIndex hn) / 2
  rw [AffineMap.lineMap_apply_module]
  change (1 - (1 : ℝ) / 2) * (section5StartVertex n).1 (section5SecondIndex hn) +
      ((1 : ℝ) / 2) * v.1 (section5SecondIndex hn) = v.1 (section5SecondIndex hn) / 2
  rw [hstart0]
  ring_nf

theorem secondCoord_pos_of_ne_start_of_mem_coordinateFace_two {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    {y : RentSimplex n} (hy : y ∈ coordinateFace (prefixRooms n 2))
    (hy_ne : y ≠ section5StartVertex n) :
    0 < y.1 (section5SecondIndex hn) := by
  have hy_nonneg : 0 ≤ y.1 (section5SecondIndex hn) := y.2.1 (section5SecondIndex hn)
  by_cases hy_zero : y.1 (section5SecondIndex hn) = 0
  · have hy_first : y.1 (0 : RoomIndex n) = 1 := by
      have hsum := section5Boundary_sum_two hn hy
      linarith
    have hy_eq_start : y = section5StartVertex n := by
      rw [section5StartVertex_eq_vertex_zero]
      exact eq_vertex_of_apply_eq_one hy_first
    exact False.elim (hy_ne hy_eq_start)
  · exact lt_of_le_of_ne hy_nonneg (Ne.symm hy_zero)

theorem section5StartSegmentMidpoint_ne_start {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    {v : RentSimplex n} (hv : v ∈ coordinateFace (prefixRooms n 2))
    (hvNe : v ≠ section5StartVertex n) :
    section5StartSegmentMidpoint v ≠ section5StartVertex n := by
  intro hmid
  have hvPos : 0 < v.1 (section5SecondIndex hn) :=
    secondCoord_pos_of_ne_start_of_mem_coordinateFace_two hn hv hvNe
  have hmidPos : 0 < (section5StartSegmentMidpoint v).1 (section5SecondIndex hn) := by
    rw [section5StartSegmentMidpoint_apply_second hn]
    nlinarith
  have hstartZero : (section5StartVertex n).1 (section5SecondIndex hn) = 0 := by
    rw [section5StartVertex_eq_vertex_zero]
    have hneq : section5SecondIndex hn ≠ (0 : RoomIndex n) := by
      simpa [section5FirstIndex_eq_zero hn] using section5SecondIndex_ne_zero hn
    simp [hneq]
  rw [hmid] at hmidPos
  linarith

theorem SimplexTriangulation.section5StartVertex_mem_boundaryFace_of_midpoint_realization
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (T : SimplexTriangulation n)
    {τ : SimplexFacet n} (hτ : τ ∈ T.facets) {v : RentSimplex n}
    (hvFace : v ∈ coordinateFace (prefixRooms n 2))
    (hvNe : v ≠ section5StartVertex n)
    (hmin : ∀ w ∈ T.vertices, w ∈ coordinateFace (prefixRooms n 2) →
      w ≠ section5StartVertex n →
        v.1 (section5SecondIndex hn) ≤ w.1 (section5SecondIndex hn))
    (hmidτ :
      ((section5StartSegmentMidpoint v : RentSimplex n) : RentCoordinates n) ∈
        τ.section5BoundaryFace.realization) :
    section5StartVertex n ∈ τ.section5BoundaryFace.vertices := by
  by_contra hstart
  have hbound :
      ∀ w ∈ τ.section5BoundaryFace.vertices,
        v.1 (section5SecondIndex hn) ≤ w.1 (section5SecondIndex hn) := by
    intro w hw
    have hw' : w ∈ τ.section5BoundaryVertices := by
      simpa [SimplexFacet.section5BoundaryFace_vertices] using hw
    have hwτ : w ∈ τ.vertices := (τ.mem_section5BoundaryVertices_iff.mp hw').1
    have hwFace : w ∈ coordinateFace (prefixRooms n 2) :=
      (τ.mem_section5BoundaryVertices_iff.mp hw').2
    have hwNe : w ≠ section5StartVertex n := by
      intro hwEq
      exact hstart (hwEq ▸ hw)
    exact hmin w (T.mem_vertices_of_mem_facet hτ hwτ) hwFace hwNe
  have hmidLower :
      v.1 (section5SecondIndex hn) ≤
        (section5StartSegmentMidpoint v).1 (section5SecondIndex hn) :=
    secondCoord_lower_bound_of_mem_realization hn hmidτ hbound
  have hvPos : 0 < v.1 (section5SecondIndex hn) :=
    secondCoord_pos_of_ne_start_of_mem_coordinateFace_two hn hvFace hvNe
  rw [section5StartSegmentMidpoint_apply_second hn] at hmidLower
  nlinarith

theorem boundary_point_mem_segment_of_le_secondCoord {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    {x y : RentSimplex n}
    (hx : x ∈ coordinateFace (prefixRooms n 2))
    (hy : y ∈ coordinateFace (prefixRooms n 2))
    (hy_ne : y ≠ section5StartVertex n)
    (hxy : x.1 (section5SecondIndex hn) ≤ y.1 (section5SecondIndex hn)) :
    ((x : RentSimplex n) : RentCoordinates n) ∈
      segment ℝ (section5StartVertex n : RentCoordinates n)
        ((y : RentSimplex n) : RentCoordinates n) := by
  let t : ℝ := x.1 (section5SecondIndex hn) / y.1 (section5SecondIndex hn)
  have hy_pos : 0 < y.1 (section5SecondIndex hn) :=
    secondCoord_pos_of_ne_start_of_mem_coordinateFace_two hn hy hy_ne
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (x.2.1 (section5SecondIndex hn)) hy_pos.le
  have ht1 : t ≤ 1 := by
    dsimp [t]
    have hy_ne_zero : y.1 (section5SecondIndex hn) ≠ 0 := hy_pos.ne'
    field_simp [hy_ne_zero]
    linarith
  rw [segment_eq_image_lineMap, Set.mem_image]
  refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
  rw [section5Boundary_eq_lineMap_of_mem_coordinateFace_two hn hy,
    AffineMap.lineMap_lineMap_right,
    section5Boundary_eq_lineMap_of_mem_coordinateFace_two hn hx]
  have hy_ne_zero : y.1 (section5SecondIndex hn) ≠ 0 := hy_pos.ne'
  congr 1
  dsimp [t]
  field_simp [hy_ne_zero]

@[simp]
theorem section5StartCell_card (n : ℕ) [NeZero n] :
    (section5StartCell n).vertices.card = 1 := by
  simp [section5StartCell]

theorem SimplexFacet.section5StartVertex_mem_vertices_of_mem_realization {n : ℕ} [NeZero n]
    {τ : SimplexFacet n}
    (hτ : ((section5StartVertex n : RentSimplex n) : RentCoordinates n) ∈ τ.realization) :
    section5StartVertex n ∈ τ.vertices := by
  have hcoord :
      ConvexOn ℝ (Set.univ : Set (RentCoordinates n))
        ((LinearMap.proj (0 : RoomIndex n)) : RentCoordinates n →ₗ[ℝ] ℝ) :=
    (LinearMap.proj (0 : RoomIndex n)).convexOn convex_univ
  obtain ⟨y, hyPointSet, hyMax⟩ := hcoord.exists_ge_of_mem_convexHull
      (by intro y hy; simp)
      (by simpa [SimplexFacet.realization, SimplexFacet.pointSet] using hτ)
  rcases hyPointSet with ⟨v, hv, rfl⟩
  have hge : (1 : ℝ) ≤ v.1 (0 : RoomIndex n) := by
    simpa [LinearMap.proj_apply, section5StartVertex_eq_vertex_zero] using hyMax
  have hle : v.1 (0 : RoomIndex n) ≤ 1 :=
    stdSimplex.le_one v (0 : RoomIndex n)
  have hv0 : v.1 (0 : RoomIndex n) = 1 :=
    le_antisymm hle hge
  have hvEq : v = section5StartVertex n := by
    rw [section5StartVertex_eq_vertex_zero]
    exact eq_vertex_of_apply_eq_one hv0
  simpa [hvEq] using hv

theorem SimplexTriangulation.section5StartCell_isFace {n : ℕ} [NeZero n]
    (T : SimplexTriangulation n) :
    T.IsFace (section5StartCell n) := by
  rcases T.covers_simplex (section5StartVertex n) with ⟨τ, hτ, hreal⟩
  refine ⟨τ, hτ, ?_⟩
  intro v hv
  have hv' : v = section5StartVertex n := by
    simpa [section5StartCell] using hv
  subst hv'
  exact τ.section5StartVertex_mem_vertices_of_mem_realization hreal

@[simp]
theorem facetImageContains_section5StartCell_iff {n : ℕ} [NeZero n]
    {f : SelfMapOnRentSimplex n} {y : RentCoordinates n} :
    FacetImageContains f (section5StartCell n) y ↔ y = f (section5StartVertex n) := by
  rw [FacetImageContains, FacetImageHull, section5StartCell]
  simp [convexHull_singleton]

theorem eq_prefixBarycenter_one_of_mem_ambientCoordinateFace {n : ℕ} [NeZero n]
    {y : RentCoordinates n} (hy : y ∈ ambientCoordinateFace (prefixRooms n 1)) :
    y = prefixBarycenter n 1 := by
  ext i
  by_cases hi : i.1 < 1
  · have hsum_single : (∑ j, y j) = y i := by
      classical
      rw [Finset.sum_eq_single i]
      · intro j _ hji
        have hjnot : j ∉ prefixRooms n 1 := by
          intro hj
          have hi0 : i.1 = 0 := by omega
          have hj0 : j.1 = 0 := by
            simpa [mem_prefixRooms_iff] using hj
          apply hji
          apply Fin.ext
          omega
        exact (coordSupport_subset_iff.mp hy.2) j hjnot
      · intro hi_not_mem
        exact False.elim (hi_not_mem (Finset.mem_univ i))
    have hyi : y i = (1 : ℝ) := by
      calc
        y i = ∑ j, y j := hsum_single.symm
        _ = ((1 : ℕ) : ℝ) := hy.1.2
        _ = (1 : ℝ) := by norm_num
    simp [prefixBarycenter, hi, hyi]
  · have hyi : y i = 0 := by
      exact (coordSupport_subset_iff.mp hy.2) i (by simpa [mem_prefixRooms_iff] using hi)
    simp [prefixBarycenter, hi, hyi]

theorem eq_section5StartVertex_of_mem_coordinateFace_one {n : ℕ} [NeZero n]
    {x : RentSimplex n} (hx : x ∈ coordinateFace (prefixRooms n 1)) :
    x = section5StartVertex n := by
  have hxSimplex : ((x : RentSimplex n) : RentCoordinates n) ∈ scaledSimplex 1 n := by
    refine ⟨x.2.1, ?_⟩
    exact_mod_cast x.2.2
  apply Subtype.ext
  exact eq_prefixBarycenter_one_of_mem_ambientCoordinateFace <|
    mem_ambientCoordinateFace_iff.mpr
      ⟨hxSimplex, coordSupport_subset_iff.mpr <| mem_coordinateFace_iff.mp hx⟩

theorem IsFaceRespecting.map_section5StartVertex_eq_prefixBarycenter {n : ℕ} [NeZero n]
    {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f) :
  f (section5StartVertex n) = prefixBarycenter n 1 := by
  exact eq_prefixBarycenter_one_of_mem_ambientCoordinateFace <|
    hf.mapsTo_ambientCoordinateFace (prefixRooms n 1) (section5StartVertex_mem_coordinateFace n)

theorem IsFaceRespecting.startCell_hits_prefixBarycenter {n : ℕ} [NeZero n]
    {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f) :
    FacetImageContains f (section5StartCell n) (prefixBarycenter n 1) := by
  rw [facetImageContains_section5StartCell_iff]
  exact (hf.map_section5StartVertex_eq_prefixBarycenter).symm

/-- A vertex of the Section 5 graph: a simplex cell together with its level in the barycenter
chain. -/
structure Section5Node (n : ℕ) where
  level : ℕ
  cell : SimplexFacet n

/-- The graph node corresponding to the starting vertex `e_1 = b_1`. -/
def section5StartNode (n : ℕ) [NeZero n] : Section5Node n where
  level := 0
  cell := section5StartCell n

@[simp]
theorem section5StartNode_level (n : ℕ) [NeZero n] :
    (section5StartNode n).level = 0 :=
  rfl

@[simp]
theorem section5StartNode_cell (n : ℕ) [NeZero n] :
    (section5StartNode n).cell = section5StartCell n :=
  rfl

/-- The local conditions for a Section 5 graph node. -/
structure IsSection5GraphNode {n : ℕ} (T : SimplexTriangulation n)
    (f : SelfMapOnRentSimplex n) (u : Section5Node n) : Prop where
  level_le : u.level + 1 ≤ n
  isFace : SimplexTriangulation.IsFace T u.cell
  card_eq : u.cell.vertices.card = u.level + 1
  prefix_vertices :
    ∀ ⦃v : RentSimplex n⦄, v ∈ u.cell.vertices →
      v ∈ coordinateFace (prefixRooms n (u.level + 1))
  meets_chain : (FacetImageHull f u.cell ∩ prefixBarycenterSegment n u.level).Nonempty

theorem IsSection5GraphNode.cell_nonempty {n : ℕ} {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n} {u : Section5Node n} (hu : IsSection5GraphNode T f u) :
    u.cell.vertices.Nonempty := by
  refine Finset.card_ne_zero.mp ?_
  rw [hu.card_eq]
  omega

theorem IsSection5GraphNode.level_eq_card_pred {n : ℕ} {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n} {u : Section5Node n} (hu : IsSection5GraphNode T f u) :
    u.level = u.cell.vertices.card - 1 := by
  rw [hu.card_eq]
  omega

theorem IsSection5GraphNode.exists_realizationPoint_mem_chain_of_piecewiseAffineOn {n : ℕ}
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hpa : IsPiecewiseAffineOn T f) :
    ∃ τ ∈ T.facets, u.cell.IsSubfaceOf τ ∧
      ∃ g : RentCoordinates n →ᵃ[ℝ] RentCoordinates n,
        (∀ v ∈ (τ.vertices : Set (RentSimplex n)), g v = f v) ∧
        ∃ x ∈ u.cell.realization, g x ∈ prefixBarycenterSegment n u.level := by
  rcases hu.meets_chain with ⟨y, hyHull, hySeg⟩
  rcases T.exists_point_in_realization_of_facetImageContains hu.isFace hpa hyHull with
    ⟨τ, hτ, hsub, g, hg, x, hx, hxy⟩
  refine ⟨τ, hτ, hsub, g, hg, x, hx, ?_⟩
  simpa [hxy] using hySeg

theorem
    IsSection5GraphNode.exists_faceHitWitness_eq_under_segmentCollapse_of_piecewiseAffineOn
    {n : ℕ} {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hpa : IsPiecewiseAffineOn T f)
    {β : Type*} [AddCommGroup β] [Module ℝ β]
    (L : RentCoordinates n →ₗ[ℝ] β)
    (hL : L (prefixBarycenter n (u.level + 1) - prefixBarycenter n u.level) = 0) :
    ∃ y, y ∈ prefixBarycenterSegment n u.level ∧
      ∃ hw : FaceHitWitness T f u.cell y,
        L (hw.affineMap hw.point) = L (prefixBarycenter n u.level) := by
  rcases hu.meets_chain with ⟨y, hyHull, hySeg⟩
  let hw : FaceHitWitness T f u.cell y :=
    T.faceHitWitnessOfFacetImageContains hu.isFace hpa hyHull
  exact ⟨y, hySeg, hw,
    hw.eq_under_segmentCollapse_of_mem_prefixBarycenterSegment L hL hySeg⟩

theorem IsSection5GraphNode.levelOne_cell_eq_boundaryVertices_of_incidentFacet {n : ℕ}
    [NeZero n] (hn : 2 ≤ n) {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {u : Section5Node n} (hu : IsSection5GraphNode T f u) (hu1 : u.level = 1)
    {τ : SimplexFacet n} (hτ : τ ∈ T.facets) (huτ : u.cell.IsSubfaceOf τ) :
    u.cell.vertices = τ.section5BoundaryVertices := by
  have hsub : u.cell.vertices ⊆ τ.section5BoundaryVertices := by
    intro v hv
    refine τ.mem_section5BoundaryVertices_iff.mpr ⟨huτ hv, ?_⟩
    simpa [hu1] using hu.prefix_vertices hv
  have hucard : u.cell.vertices.card = 2 := by
    simpa [hu1] using hu.card_eq
  have hτcard : τ.section5BoundaryVertices.card ≤ 2 :=
    T.boundaryVertices_card_le_two hn hτ
  have hτcard' : τ.section5BoundaryVertices.card ≤ u.cell.vertices.card := by
    omega
  exact Finset.eq_of_subset_of_card_le hsub hτcard'

theorem IsSection5GraphNode.levelOne_vertices_eq_startPair {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hu1 : u.level = 1)
    (hstart : (section5StartCell n).IsSubfaceOf u.cell) :
    ∃ a : RentSimplex n, a ≠ section5StartVertex n ∧
      u.cell.vertices = {section5StartVertex n, a} := by
  have hucard : u.cell.vertices.card = 2 := by
    simpa [hu1] using hu.card_eq
  have hstart_mem : section5StartVertex n ∈ u.cell.vertices := by
    exact hstart (by simp [section5StartCell])
  rcases Finset.card_eq_two.mp hucard with ⟨x, y, hxy, hverts⟩
  have hstart' : section5StartVertex n = x ∨ section5StartVertex n = y := by
    simpa [hverts] using hstart_mem
  rcases hstart' with rfl | rfl
  · exact ⟨y, hxy.symm, by simp [hverts]⟩
  · exact ⟨x, hxy, by simp [hverts, Finset.pair_comm]⟩

theorem eq_of_mem_startPair_of_ne_start {n : ℕ} [NeZero n] {x a : RentSimplex n}
    (hx : x ≠ section5StartVertex n)
    (hmem : x ∈ ({section5StartVertex n, a} : Finset (RentSimplex n))) :
    x = a := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | hEq
  · exact False.elim (hx rfl)
  · exact hEq

theorem IsSection5GraphNode.levelOne_cell_eq_of_start_subface {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {u v : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hu1 : u.level = 1)
    (hustart : (section5StartCell n).IsSubfaceOf u.cell)
    (hv : IsSection5GraphNode T f v) (hv1 : v.level = 1)
    (hvstart : (section5StartCell n).IsSubfaceOf v.cell) :
    u.cell = v.cell := by
  have hn : 2 ≤ n := by
    simpa [hu1] using hu.level_le
  rcases hu.isFace with ⟨τu, hτu, huτ⟩
  rcases hv.isFace with ⟨τv, hτv, hvτ⟩
  have huBoundaryEq :
      u.cell.vertices = τu.section5BoundaryVertices :=
    hu.levelOne_cell_eq_boundaryVertices_of_incidentFacet hn hu1 hτu huτ
  have hvBoundaryEq :
      v.cell.vertices = τv.section5BoundaryVertices :=
    hv.levelOne_cell_eq_boundaryVertices_of_incidentFacet hn hv1 hτv hvτ
  rcases hu.levelOne_vertices_eq_startPair hu1 hustart with ⟨a, ha_ne, hua⟩
  rcases hv.levelOne_vertices_eq_startPair hv1 hvstart with ⟨b, hb_ne, hvb⟩
  have ha_mem_u : a ∈ u.cell.vertices := by
    simp [hua]
  have hb_mem_v : b ∈ v.cell.vertices := by
    simp [hvb]
  have haFace : a ∈ coordinateFace (prefixRooms n 2) := by
    simpa [hu1] using hu.prefix_vertices ha_mem_u
  have hbFace : b ∈ coordinateFace (prefixRooms n 2) := by
    simpa [hv1] using hv.prefix_vertices hb_mem_v
  have hab_of_mem_both_realizations :
      ∀ {x : RentSimplex n},
        x ∈ coordinateFace (prefixRooms n 2) →
        x ≠ section5StartVertex n →
        ((x : RentSimplex n) : RentCoordinates n) ∈ τu.realization →
        ((x : RentSimplex n) : RentCoordinates n) ∈ τv.realization →
        a = b := by
    intro x hxFace hxNe hxτuReal hxτvReal
    have hxInter :
        ((x : RentSimplex n) : RentCoordinates n) ∈ τu.realization ∩ τv.realization :=
      ⟨hxτuReal, hxτvReal⟩
    rw [T.face_intersection hτu hτv] at hxInter
    have hxConv :
        ((x : RentSimplex n) : RentCoordinates n) ∈
          convexHull ℝ
            (((τu.commonVertices τv).image fun w : RentSimplex n =>
              ((w : RentSimplex n) : RentCoordinates n)) : Set (RentCoordinates n)) := by
      simpa [SimplexFacet.intersectionPointSet, SimplexFacet.commonVertices] using hxInter
    rcases exists_nonstart_boundary_vertex_of_mem_convexHull hn hxFace hxNe hxConv with
      ⟨c, hcCommon, hcFace, hcNe⟩
    have hcInU : c ∈ u.cell.vertices := by
      rw [huBoundaryEq]
      exact τu.mem_section5BoundaryVertices_iff.mpr
        ⟨(mem_commonVertices_iff.mp hcCommon).1, hcFace⟩
    have hcEqA : c = a := by
      rw [hua] at hcInU
      exact eq_of_mem_startPair_of_ne_start hcNe hcInU
    have hcInV : c ∈ v.cell.vertices := by
      rw [hvBoundaryEq]
      exact τv.mem_section5BoundaryVertices_iff.mpr
        ⟨(mem_commonVertices_iff.mp hcCommon).2, hcFace⟩
    have hcEqB : c = b := by
      rw [hvb] at hcInV
      exact eq_of_mem_startPair_of_ne_start hcNe hcInV
    exact hcEqA.symm.trans hcEqB
  have hab : a = b := by
    by_cases hle : a.1 (section5SecondIndex hn) ≤ b.1 (section5SecondIndex hn)
    · have haτu : a ∈ τu.vertices := huτ ha_mem_u
      have haτuReal :
          ((a : RentSimplex n) : RentCoordinates n) ∈ τu.realization :=
        Arxiv170207325.SimplexFacet.mem_realization_of_mem_vertices haτu
      have hstart_mem_v : section5StartVertex n ∈ v.cell.vertices := by
        exact hvstart (by simp [section5StartCell])
      have haSeg :
          ((a : RentSimplex n) : RentCoordinates n) ∈
            segment ℝ (section5StartVertex n : RentCoordinates n)
              ((b : RentSimplex n) : RentCoordinates n) :=
        boundary_point_mem_segment_of_le_secondCoord hn haFace hbFace hb_ne hle
      have haVCell :
          ((a : RentSimplex n) : RentCoordinates n) ∈ v.cell.realization := by
        rw [SimplexFacet.realization]
        exact segment_subset_convexHull
          (Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n) hstart_mem_v)
          (Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n) hb_mem_v)
          haSeg
      have haτvReal :
          ((a : RentSimplex n) : RentCoordinates n) ∈ τv.realization :=
        (Arxiv170207325.SimplexFacet.realization_subset_of_isSubface hvτ) haVCell
      exact hab_of_mem_both_realizations haFace ha_ne haτuReal haτvReal
    · have hle' : b.1 (section5SecondIndex hn) ≤ a.1 (section5SecondIndex hn) :=
        le_of_not_ge hle
      have hbτv : b ∈ τv.vertices := hvτ hb_mem_v
      have hbτvReal :
          ((b : RentSimplex n) : RentCoordinates n) ∈ τv.realization :=
        Arxiv170207325.SimplexFacet.mem_realization_of_mem_vertices hbτv
      have hstart_mem_u : section5StartVertex n ∈ u.cell.vertices := by
        exact hustart (by simp [section5StartCell])
      have hbSeg :
          ((b : RentSimplex n) : RentCoordinates n) ∈
            segment ℝ (section5StartVertex n : RentCoordinates n)
              ((a : RentSimplex n) : RentCoordinates n) :=
        boundary_point_mem_segment_of_le_secondCoord hn hbFace haFace ha_ne hle'
      have hbUCell :
          ((b : RentSimplex n) : RentCoordinates n) ∈ u.cell.realization := by
        rw [SimplexFacet.realization]
        exact segment_subset_convexHull
          (Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n) hstart_mem_u)
          (Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n) ha_mem_u)
          hbSeg
      have hbτuReal :
          ((b : RentSimplex n) : RentCoordinates n) ∈ τu.realization :=
        (Arxiv170207325.SimplexFacet.realization_subset_of_isSubface huτ) hbUCell
      exact hab_of_mem_both_realizations hbFace hb_ne hbτuReal hbτvReal
  have hverts : u.cell.vertices = v.cell.vertices := by
    simp [hua, hvb, hab]
  cases huCell : u.cell with
  | mk uverts =>
    cases hvCell : v.cell with
    | mk vverts =>
      simp only [SimplexFacet.mk.injEq]
      simpa [huCell, hvCell] using hverts

theorem Section5Node.eq_of_level_eq_one_of_cell_eq {n : ℕ} {u v : Section5Node n}
    (hu1 : u.level = 1) (hv1 : v.level = 1) (hcell : u.cell = v.cell) :
    u = v := by
  cases u
  cases v
  cases hu1
  cases hv1
  cases hcell
  rfl

theorem Section5Node.eq_of_level_eq_of_cell_eq {n : ℕ} {u v : Section5Node n}
    (hlevel : u.level = v.level) (hcell : u.cell = v.cell) :
    u = v := by
  cases u
  cases v
  cases hlevel
  cases hcell
  rfl

theorem IsSection5GraphNode.lower_cell_eq_prefixVertices_of_supercell {n : ℕ}
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {u w : Section5Node n} (hu : IsSection5GraphNode T f u)
    (hw : IsSection5GraphNode T f w) (hlevel : w.level + 1 = u.level)
    (hwu : w.cell.IsSubfaceOf u.cell) :
    w.cell.vertices = u.cell.section5PrefixVertices w.level := by
  have hsub : w.cell.vertices ⊆ u.cell.section5PrefixVertices w.level := by
    intro v hv
    refine u.cell.mem_section5PrefixVertices_iff.mpr ⟨hwu hv, ?_⟩
    simpa [hlevel] using hw.prefix_vertices hv
  have hprefixCard :
      (u.cell.section5PrefixVertices w.level).card ≤ w.level + 1 :=
    T.prefixVertices_card_le_of_isFace hu.isFace hw.level_le
  have hprefixCard' :
      (u.cell.section5PrefixVertices w.level).card ≤ w.cell.vertices.card := by
    simpa [hw.card_eq] using hprefixCard
  exact Finset.eq_of_subset_of_card_le hsub hprefixCard'

theorem IsFaceRespecting.section5StartNode_isGraphNode {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f) :
    IsSection5GraphNode T f (section5StartNode n) := by
  refine ⟨Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n)),
    T.section5StartCell_isFace, section5StartCell_card n, ?_, ?_⟩
  · intro v hv
    have hv' : v = section5StartVertex n := by
      simpa [section5StartCell] using hv
    simpa [hv'] using section5StartVertex_mem_coordinateFace n
  · refine ⟨prefixBarycenter n 1, hf.startCell_hits_prefixBarycenter, ?_⟩
    change prefixBarycenter n 1 ∈ segment ℝ (prefixBarycenter n 0) (prefixBarycenter n 1)
    exact right_mem_segment ℝ (prefixBarycenter n 0) (prefixBarycenter n 1)

/-- One step in the Section 5 graph: a codimension-one incidence at the next barycenter of the
chain. -/
def Section5Step {n : ℕ} (f : SelfMapOnRentSimplex n) (u v : Section5Node n) : Prop :=
  u.level + 1 = v.level ∧ u.cell.IsSubfaceOf v.cell ∧
    FacetImageContains f u.cell (prefixBarycenter n v.level)

/-- The undirected adjacency relation on the Section 5 graph. -/
def Section5Adjacent {n : ℕ} (f : SelfMapOnRentSimplex n) (u v : Section5Node n) : Prop :=
  Section5Step f u v ∨ Section5Step f v u

theorem section5Adjacent_symm {n : ℕ} {f : SelfMapOnRentSimplex n}
    {u v : Section5Node n} : Section5Adjacent f u v ↔ Section5Adjacent f v u := by
  constructor <;> intro h
  · exact h.elim Or.inr Or.inl
  · exact h.elim Or.inr Or.inl

theorem section5Adjacent_of_level_succ_eq_iff_step {n : ℕ} {f : SelfMapOnRentSimplex n}
    {u v : Section5Node n} (hlevel : u.level + 1 = v.level) :
    Section5Adjacent f u v ↔ Section5Step f u v := by
  constructor
  · intro huv
    rcases huv with huv | hvu
    · exact huv
    · exfalso
      have hvuLevel : v.level + 1 = u.level := hvu.1
      omega
  · intro huv
    exact Or.inl huv

theorem IsSection5GraphNode.lower_step_unique {n : ℕ}
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {u v w : Section5Node n} (hu : IsSection5GraphNode T f u)
    (hv : IsSection5GraphNode T f v) (hw : IsSection5GraphNode T f w)
    (hvu : Section5Step f v u) (hwu : Section5Step f w u) :
    v = w := by
  have hvuLevel : v.level + 1 = u.level := hvu.1
  have hwuLevel : w.level + 1 = u.level := hwu.1
  have hlevel : v.level = w.level := by
    omega
  have hvCell :
      v.cell.vertices = u.cell.section5PrefixVertices v.level :=
    hu.lower_cell_eq_prefixVertices_of_supercell hv hvuLevel hvu.2.1
  have hwCell :
      w.cell.vertices = u.cell.section5PrefixVertices w.level :=
    hu.lower_cell_eq_prefixVertices_of_supercell hw hwuLevel hwu.2.1
  have hverts : v.cell.vertices = w.cell.vertices := by
    have hwCell' : w.cell.vertices = u.cell.section5PrefixVertices v.level := by
      rw [hlevel]
      exact hwCell
    exact hvCell.trans hwCell'.symm
  have hcell : v.cell = w.cell := by
    cases hvCellEq : v.cell with
    | mk vverts =>
      cases hwCellEq : w.cell with
      | mk wverts =>
        simp only [SimplexFacet.mk.injEq]
        simpa [hvCellEq, hwCellEq] using hverts
  let g : Section5Node n → ℕ × SimplexFacet n := fun t => (t.level, t.cell)
  have hg : Function.Injective g := by
    rintro ⟨la, ca⟩ ⟨lb, cb⟩ hab
    simpa [g] using hab
  exact hg <| Prod.ext hlevel hcell

theorem not_section5Step_self {n : ℕ} {f : SelfMapOnRentSimplex n} {u : Section5Node n} :
    ¬ Section5Step f u u := by
  intro hu
  exact Nat.succ_ne_self u.level hu.1

theorem not_section5Adjacent_self {n : ℕ} {f : SelfMapOnRentSimplex n} {u : Section5Node n} :
    ¬ Section5Adjacent f u u := by
  intro hu
  rcases hu with hu | hu
  · exact not_section5Step_self hu
  · exact not_section5Step_self hu

/-- The finite graph on a prescribed node set, using `Section5Adjacent` as the edge relation. -/
def section5SimpleGraph {n : ℕ} (nodes : Finset (Section5Node n))
    (f : SelfMapOnRentSimplex n) : SimpleGraph nodes where
  Adj u v := Section5Adjacent f u.1 v.1
  symm := by
    intro u v huv
    exact (section5Adjacent_symm (u := u.1) (v := v.1)).mp huv
  loopless := ⟨fun u => not_section5Adjacent_self (u := u.1) (f := f)⟩

/-- The degree of one node in a finite Section 5 graph component. -/
def section5NodeDegree {n : ℕ} (nodes : Finset (Section5Node n))
    (f : SelfMapOnRentSimplex n) (v : nodes) : ℕ := by
  classical
  exact ((section5SimpleGraph nodes f).neighborFinset v).card

/-- The finite set of Section 5 node candidates contributed by one triangulation facet. -/
def section5FacetNodes {n : ℕ} (τ : SimplexFacet n) : Finset (Section5Node n) := by
  classical
  exact (τ.vertices.powerset.filter fun s => s.Nonempty).image fun s =>
    ({ level := s.card - 1, cell := ⟨s⟩ } : Section5Node n)

/-- The actual finite Section 5 node set, obtained by filtering the face candidates by the graph
conditions from Section 5. -/
def section5Nodes {n : ℕ} (T : SimplexTriangulation n)
    (f : SelfMapOnRentSimplex n) : Finset (Section5Node n) := by
  classical
  exact (T.facets.biUnion section5FacetNodes).filter fun u => IsSection5GraphNode T f u

theorem mk_section5Node_from_cell_eq {n : ℕ} (u : Section5Node n)
    (hlevel : u.level = u.cell.vertices.card - 1) :
    ({ level := u.cell.vertices.card - 1, cell := ⟨u.cell.vertices⟩ } : Section5Node n) = u := by
  cases u with
  | mk level cell =>
    cases cell with
    | mk vertices =>
      simp at hlevel ⊢
      simpa using hlevel.symm

theorem IsSection5GraphNode.mem_section5Nodes {n : ℕ} {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n} {u : Section5Node n} (hu : IsSection5GraphNode T f u) :
    u ∈ section5Nodes T f := by
  classical
  refine Finset.mem_filter.mpr ⟨?_, hu⟩
  rcases hu.isFace with ⟨τ, hτ, hsub⟩
  refine Finset.mem_biUnion.mpr ⟨τ, hτ, ?_⟩
  refine Finset.mem_image.mpr ⟨u.cell.vertices, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hu.cell_nonempty⟩
  · exact mk_section5Node_from_cell_eq u hu.level_eq_card_pred

theorem mem_section5Nodes_iff {n : ℕ} {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n} {u : Section5Node n} :
    u ∈ section5Nodes T f ↔ IsSection5GraphNode T f u := by
  classical
  constructor
  · intro hu
    exact (Finset.mem_filter.mp hu).2
  · intro hu
    exact hu.mem_section5Nodes

theorem section5StartNode_mem_section5Nodes_iff {n : ℕ} [NeZero n] {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n} :
    section5StartNode n ∈ section5Nodes T f ↔ IsSection5GraphNode T f (section5StartNode n) :=
  mem_section5Nodes_iff

/-- The Section 5 start node, packaged as a vertex of the actual finite node set. -/
def section5StartNodeInNodes {n : ℕ} [NeZero n] {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n}
    (hstart : IsSection5GraphNode T f (section5StartNode n)) : section5Nodes T f :=
  ⟨section5StartNode n, section5StartNode_mem_section5Nodes_iff.mpr hstart⟩

/-- The concrete Section 5 graph on the actual finite node set. -/
abbrev section5NodeGraph {n : ℕ} (T : SimplexTriangulation n)
    (f : SelfMapOnRentSimplex n) : SimpleGraph (section5Nodes T f) :=
  section5SimpleGraph (section5Nodes T f) f

/-- The connected component of the concrete Section 5 graph that contains the start node. -/
def section5StartComponent {n : ℕ} [NeZero n] {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n}
    (hstart : IsSection5GraphNode T f (section5StartNode n)) :
    (section5NodeGraph T f).ConnectedComponent :=
  (section5NodeGraph T f).connectedComponentMk (section5StartNodeInNodes hstart)

/-- The start node, viewed as a vertex of its connected component. -/
def section5StartVertexInComponent {n : ℕ} [NeZero n] {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n}
    (hstart : IsSection5GraphNode T f (section5StartNode n)) :
    section5StartComponent hstart := by
  exact ⟨section5StartNodeInNodes hstart,
    by
      simpa [section5StartComponent] using
        (SimpleGraph.ConnectedComponent.connectedComponentMk_mem
          (G := section5NodeGraph T f) (v := section5StartNodeInNodes hstart))⟩

/-- The graph obtained by restricting the concrete Section 5 graph to the component containing the
start node. -/
abbrev section5StartComponentGraph {n : ℕ} [NeZero n] {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n}
    (hstart : IsSection5GraphNode T f (section5StartNode n)) :
    SimpleGraph (section5StartComponent hstart) :=
  (section5StartComponent hstart).toSimpleGraph

theorem section5StartComponentGraph_preconnected {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hstart : IsSection5GraphNode T f (section5StartNode n)) :
    (section5StartComponentGraph hstart).Preconnected :=
  (section5StartComponent hstart).connected_toSimpleGraph.preconnected

theorem mem_section5StartComponent_iff_reachable {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hstart : IsSection5GraphNode T f (section5StartNode n)) {v : section5Nodes T f} :
    v ∈ (section5StartComponent hstart).supp ↔
      (section5NodeGraph T f).Reachable (section5StartNodeInNodes hstart) v := by
  constructor
  · intro hv
    have hv' :
        (section5NodeGraph T f).connectedComponentMk v = section5StartComponent hstart :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff
        (G := section5NodeGraph T f) (C := section5StartComponent hstart)
        (v := v)).mp hv
    simpa [section5StartComponent] using
      (SimpleGraph.ConnectedComponent.exact hv').symm
  · intro hv
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    unfold section5StartComponent
    simpa [SimpleGraph.reachable_comm] using SimpleGraph.ConnectedComponent.sound hv

theorem section5StartComponentGraph_adj_iff {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hstart : IsSection5GraphNode T f (section5StartNode n))
    {u v : section5StartComponent hstart} :
    (section5StartComponentGraph hstart).Adj u v ↔ Section5Adjacent f u.1.1 v.1.1 := by
  exact SimpleGraph.ConnectedComponent.toSimpleGraph_adj (C := section5StartComponent hstart)
    u.2 v.2

theorem section5StartComponentGraph_adj_level_cases {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hstart : IsSection5GraphNode T f (section5StartNode n))
    {u v : section5StartComponent hstart}
    (huv : (section5StartComponentGraph hstart).Adj u v) :
    u.1.1.level + 1 = v.1.1.level ∨ v.1.1.level + 1 = u.1.1.level := by
  rcases (section5StartComponentGraph_adj_iff hstart).mp huv with huv | hvu
  · exact Or.inl huv.1
  · exact Or.inr hvu.1

theorem section5StartComponent_eq_start_of_level_zero {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {v : section5StartComponent hstart} (hv0 : v.1.1.level = 0) :
    v = section5StartVertexInComponent hstart := by
  have hvNode : IsSection5GraphNode T f v.1.1 := mem_section5Nodes_iff.mp v.1.2
  have hcard : v.1.1.cell.vertices.card = 1 := by
    simpa [hv0] using hvNode.card_eq
  rcases Finset.card_eq_one.mp hcard with ⟨w, hw⟩
  have hwMem : w ∈ v.1.1.cell.vertices := by
    rw [hw]
    simp
  have hwFace : w ∈ coordinateFace (prefixRooms n 1) := by
    simpa [hv0] using hvNode.prefix_vertices hwMem
  have hwEq : w = section5StartVertex n :=
    eq_section5StartVertex_of_mem_coordinateFace_one hwFace
  have hcell : v.1.1.cell = section5StartCell n := by
    cases hvCell : v.1.1.cell with
    | mk verts =>
      simpa [hvCell, section5StartCell, hwEq] using hw
  have hnode : v.1.1 = section5StartNode n :=
    Section5Node.eq_of_level_eq_of_cell_eq
      (by simpa [section5StartNode_level] using hv0) hcell
  have hnode' : v.1 = section5StartNodeInNodes hstart := Subtype.ext hnode
  exact Subtype.ext hnode'

theorem section5StartComponent_level_pos_of_ne_start {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {v : section5StartComponent hstart}
    (hv : v ≠ section5StartVertexInComponent hstart) :
    0 < v.1.1.level := by
  have hv0 : v.1.1.level ≠ 0 := by
    intro hv0
    exact hv (section5StartComponent_eq_start_of_level_zero hv0)
  exact Nat.pos_of_ne_zero hv0

theorem section5StartComponentGraph_lower_neighbor_unique {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {u a b : section5StartComponent hstart}
    (haAdj : (section5StartComponentGraph hstart).Adj a u)
    (haLevel : a.1.1.level + 1 = u.1.1.level)
    (hbAdj : (section5StartComponentGraph hstart).Adj b u)
    (hbLevel : b.1.1.level + 1 = u.1.1.level) :
    a = b := by
  have huNode : IsSection5GraphNode T f u.1.1 := mem_section5Nodes_iff.mp u.1.2
  have haNode : IsSection5GraphNode T f a.1.1 := mem_section5Nodes_iff.mp a.1.2
  have hbNode : IsSection5GraphNode T f b.1.1 := mem_section5Nodes_iff.mp b.1.2
  have haStep : Section5Step f a.1.1 u.1.1 := by
    exact (section5Adjacent_of_level_succ_eq_iff_step (f := f) haLevel).mp <|
      (section5StartComponentGraph_adj_iff hstart).mp haAdj
  have hbStep : Section5Step f b.1.1 u.1.1 := by
    exact (section5Adjacent_of_level_succ_eq_iff_step (f := f) hbLevel).mp <|
      (section5StartComponentGraph_adj_iff hstart).mp hbAdj
  have habNode : a.1.1 = b.1.1 :=
    huNode.lower_step_unique haNode hbNode haStep hbStep
  have habNode' : a.1 = b.1 := Subtype.ext habNode
  exact Subtype.ext habNode'

theorem section5StartComponentGraph_penultimate_level_succ_of_shortest_path {n : ℕ}
    [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {v : section5StartComponent hstart}
    (hv : v ≠ section5StartVertexInComponent hstart)
    {p : (section5StartComponentGraph hstart).Walk (section5StartVertexInComponent hstart) v}
    (hpPath : p.IsPath)
    (hpLen :
      p.length =
        (section5StartComponentGraph hstart).dist (section5StartVertexInComponent hstart) v) :
    p.penultimate.1.1.level + 1 = v.1.1.level := by
  have hvPos : 0 < v.1.1.level := section5StartComponent_level_pos_of_ne_start hv
  have hpPos : 0 < p.length := by
    rw [hpLen]
    exact p.reachable.pos_dist_of_ne hv.symm
  have hLastAdj :
      (section5StartComponentGraph hstart).Adj p.penultimate v := by
    have hLastAdjRaw := p.adj_getVert_succ (i := p.length - 1) (by omega)
    have hArith : p.length - 1 + 1 = p.length := by
      omega
    simpa [SimpleGraph.Walk.penultimate, hArith] using hLastAdjRaw
  rcases section5StartComponentGraph_adj_level_cases hstart hLastAdj with hUp | hDown
  · exact hUp
  · exfalso
    let k : ℕ := v.1.1.level
    let P : ℕ → Prop := fun i =>
      i ≤ p.length - 1 ∧
        ∀ j, i ≤ j → j ≤ p.length →
          (p.getVert j).1.1.level = k + (p.length - j)
    have hPExists : ∃ i, P i := by
      refine ⟨p.length - 1, ?_⟩
      refine ⟨le_rfl, ?_⟩
      intro j hj hj'
      have hCases : j = p.length - 1 ∨ j = p.length := by
        omega
      rcases hCases with rfl | rfl
      · have hPen : p.penultimate.1.1.level = k + 1 := by
          simpa [k] using hDown.symm
        have hArith : p.length - (p.length - 1) = 1 := by
          omega
        simp [k, hPen, hArith]
      · simp [k]
    let i : ℕ := Nat.find hPExists
    have hiSpec : P i := Nat.find_spec hPExists
    have hiLe : i ≤ p.length - 1 := hiSpec.1
    have hiLevel : (p.getVert i).1.1.level = k + (p.length - i) :=
      hiSpec.2 i le_rfl (by omega)
    have hiPos : 0 < i := by
      by_contra hiZero
      have hStartLevel :
          (section5StartVertexInComponent hstart).1.1.level = k + p.length := by
        simpa [i, hiZero, k] using hiSpec.2 0 (by omega) (by omega)
      have : 0 = k + p.length := by
        simpa [k] using hStartLevel
      have hkPos : 0 < k := by
        simpa [k] using hvPos
      omega
    have hiLt : i < p.length := by
      omega
    have hPrevAdj :
        (section5StartComponentGraph hstart).Adj (p.getVert (i - 1)) (p.getVert i) := by
      have hPrevAdjRaw := p.adj_getVert_succ (i := i - 1) (by omega)
      have hArith : i - 1 + 1 = i := by
        omega
      simpa [hArith] using hPrevAdjRaw
    have hNextAdj :
        (section5StartComponentGraph hstart).Adj (p.getVert i) (p.getVert (i + 1)) := by
      exact p.adj_getVert_succ (i := i) hiLt
    have hiNextLevel : (p.getVert (i + 1)).1.1.level = k + (p.length - (i + 1)) :=
      hiSpec.2 (i + 1) (by omega) (by omega)
    have hNextLower : (p.getVert (i + 1)).1.1.level + 1 = (p.getVert i).1.1.level := by
      omega
    have hPrevLower : (p.getVert (i - 1)).1.1.level + 1 = (p.getVert i).1.1.level := by
      rcases section5StartComponentGraph_adj_level_cases hstart hPrevAdj with hPrev | hPrev
      · exact hPrev
      · exfalso
        have hPrevSpec : P (i - 1) := by
          refine ⟨by omega, ?_⟩
          intro j hj hj'
          by_cases hEq : j = i - 1
          · subst hEq
            omega
          · exact hiSpec.2 j (by omega) hj'
        have : i ≤ i - 1 := Nat.find_min' hPExists hPrevSpec
        omega
    have hRepeat :
        p.getVert (i - 1) = p.getVert (i + 1) :=
      section5StartComponentGraph_lower_neighbor_unique
        (hstart := hstart) (u := p.getVert i)
        (a := p.getVert (i - 1)) (b := p.getVert (i + 1))
        hPrevAdj hPrevLower hNextAdj.symm hNextLower
    have hIdxEq : i - 1 = i + 1 := hpPath.getVert_injOn
      (by simp [show i - 1 ≤ p.length by omega])
      (by simp [show i + 1 ≤ p.length by omega])
      hRepeat
    omega

theorem section5StartComponent_exists_lower_neighbor_of_ne_start {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {v : section5StartComponent hstart}
    (hv : v ≠ section5StartVertexInComponent hstart) :
    ∃ u : section5StartComponent hstart,
      (section5StartComponentGraph hstart).Adj u v ∧ u.1.1.level + 1 = v.1.1.level := by
  have hReach :
      (section5StartComponentGraph hstart).Reachable (section5StartVertexInComponent hstart) v :=
    (section5StartComponentGraph_preconnected hstart) _ _
  rcases hReach.exists_path_of_dist with ⟨p, hpPath, hpLen⟩
  have hpPos : 0 < p.length := by
    rw [hpLen]
    exact hReach.pos_dist_of_ne hv.symm
  refine ⟨p.penultimate, ?_, ?_⟩
  · simpa [SimpleGraph.Walk.penultimate] using
      (show (section5StartComponentGraph hstart).Adj
          (p.getVert (p.length - 1)) (p.getVert p.length) from
          by
            have hAdj := p.adj_getVert_succ (i := p.length - 1) (by omega)
            have hArith : p.length - 1 + 1 = p.length := by
              omega
            simpa [hArith] using hAdj)
  · exact section5StartComponentGraph_penultimate_level_succ_of_shortest_path hv hpPath hpLen

theorem not_section5Step_to_startNode {n : ℕ} [NeZero n] {f : SelfMapOnRentSimplex n}
    {u : Section5Node n} : ¬ Section5Step f u (section5StartNode n) := by
  intro hu
  have : u.level + 1 = 0 := by simpa [section5StartNode_level] using hu.1
  omega

theorem section5Step_from_startNode_iff {n : ℕ} [NeZero n] {f : SelfMapOnRentSimplex n}
    {u : Section5Node n} :
    Section5Step f (section5StartNode n) u ↔
      u.level = 1 ∧
        (section5StartCell n).IsSubfaceOf u.cell ∧
        FacetImageContains f (section5StartCell n) (prefixBarycenter n 1) := by
  constructor
  · intro hu
    have hlevel : u.level = 1 := by
      have hstep : (section5StartNode n).level + 1 = u.level := hu.1
      simpa [section5StartNode_level] using hstep.symm
    refine ⟨hlevel, hu.2.1, ?_⟩
    simpa [section5StartNode_cell, hlevel] using hu.2.2
  · rintro ⟨hlevel, hsub, hhit⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [section5StartNode_level, hlevel]
    · simpa [section5StartNode_cell] using hsub
    · rw [section5StartNode_cell, hlevel]
      exact hhit

theorem section5Adjacent_startNode_iff {n : ℕ} [NeZero n] {f : SelfMapOnRentSimplex n}
    {u : Section5Node n} :
    Section5Adjacent f (section5StartNode n) u ↔
      u.level = 1 ∧
        (section5StartCell n).IsSubfaceOf u.cell ∧
        FacetImageContains f (section5StartCell n) (prefixBarycenter n 1) := by
  constructor
  · intro hu
    rcases hu with hsu | hus
    · exact section5Step_from_startNode_iff.mp hsu
    · exact False.elim <| not_section5Step_to_startNode hus
  · intro hu
    exact Or.inl <| section5Step_from_startNode_iff.mpr hu

theorem section5StartComponentGraph_adj_start_iff {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hstart : IsSection5GraphNode T f (section5StartNode n))
    {v : section5StartComponent hstart} :
    (section5StartComponentGraph hstart).Adj (section5StartVertexInComponent hstart) v ↔
      v.1.1.level = 1 ∧
        (section5StartCell n).IsSubfaceOf v.1.1.cell ∧
        FacetImageContains f (section5StartCell n) (prefixBarycenter n 1) := by
  rw [section5StartComponentGraph_adj_iff hstart]
  exact section5Adjacent_startNode_iff

/-- A path in the Section 5 graph. -/
def Section5Path {n : ℕ} (f : SelfMapOnRentSimplex n) (p : List (Section5Node n)) : Prop :=
  List.IsChain (Section5Adjacent f) p

def IsSection5Endpoint {n : ℕ} [NeZero n] (T : SimplexTriangulation n)
    (f : SelfMapOnRentSimplex n) (u : Section5Node n) : Prop :=
  IsSection5GraphNode (T := T) (f := f) u ∧
    FacetImageContains f u.cell ((rentBarycenter n : RentSimplex n) : RentCoordinates n)

theorem IsSection5GraphNode.level_eq_last_of_hitsBarycenter {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hf : IsFaceRespecting f)
    (hbar : FacetImageContains f u.cell ((rentBarycenter n : RentSimplex n) : RentCoordinates n)) :
    u.level + 1 = n := by
  have hprefix :
      prefixRooms n (u.level + 1) = Finset.univ := by
    exact IsFaceRespecting.facetImageContains_interiorPoint_of_vertices hf hu.prefix_vertices
      (rentBarycenter_isInteriorSimplexPoint n) hbar
  exact (prefixRooms_eq_univ_iff hu.level_le).mp hprefix

theorem IsSection5Endpoint.cell_mem_facets {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hf : IsFaceRespecting f) (hu : IsSection5Endpoint T f u) : u.cell ∈ T.facets := by
  have hlast : u.level + 1 = n :=
    hu.1.level_eq_last_of_hitsBarycenter hf hu.2
  exact SimplexTriangulation.mem_facets_of_isFace_of_card (T := T) hu.1.isFace <| by
    simpa [hlast] using hu.1.card_eq

theorem IsSection5Endpoint.exists_targetFacet {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hf : IsFaceRespecting f) (hu : IsSection5Endpoint T f u) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact ⟨u.cell, hu.cell_mem_facets hf, hu.2⟩

theorem SimpleGraph.exists_other_degreeOne {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {start : α} (hstart : (G.neighborFinset start).card = 1)
    (hdeg : ∀ v : α, (G.neighborFinset v).card ≤ 2) :
    ∃ finish : α, finish ≠ start ∧ (G.neighborFinset finish).card = 1 := by
  classical
  have hstartOdd : Odd ((G.neighborFinset start).card) := by
    rw [hstart]
    decide
  let S : Finset α := Finset.univ.filter fun w => w ≠ start ∧ Odd ((G.neighborFinset w).card)
  have hodd' :
      Odd ((Finset.univ.filter fun w => w ≠ start ∧ Odd (G.degree w)).card) :=
    G.odd_card_odd_degree_vertices_ne start <| by
      simpa only [← G.card_neighborFinset_eq_degree] using hstartOdd
  have hodd : Odd S.card := by
    simpa only [S, ← G.card_neighborFinset_eq_degree] using hodd'
  obtain ⟨finish, hfinish⟩ := Finset.card_pos.mp hodd.pos
  have hfinish_ne : finish ≠ start := by
    exact (Finset.mem_filter.mp hfinish).2.1
  have hfinishOdd : Odd ((G.neighborFinset finish).card) := by
    exact (Finset.mem_filter.mp hfinish).2.2
  have hfinish_deg : (G.neighborFinset finish).card = 1 := by
    have hfinish_le : (G.neighborFinset finish).card ≤ 2 := hdeg finish
    have hcases :
        (G.neighborFinset finish).card = 0 ∨
          (G.neighborFinset finish).card = 1 ∨
            (G.neighborFinset finish).card = 2 := by
      omega
    rcases hcases with h0 | h1 | h2
    · exfalso
      exact (by decide : ¬ Odd 0) (h0 ▸ hfinishOdd)
    · exact h1
    · exfalso
      exact (by decide : ¬ Odd 2) (h2 ▸ hfinishOdd)
  exact ⟨finish, hfinish_ne, hfinish_deg⟩

theorem SimpleGraph.exists_other_endpoint {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] {start : α}
    (hstart : (G.neighborFinset start).card = 1)
    (hdeg : ∀ v : α, (G.neighborFinset v).card ≤ 2) (hconn : G.Preconnected) :
    ∃ finish : α,
      finish ≠ start ∧ (G.neighborFinset finish).card = 1 ∧ G.Reachable start finish := by
  rcases SimpleGraph.exists_other_degreeOne G hstart hdeg with ⟨finish, hfinish_ne, hfinish_deg⟩
  exact ⟨finish, hfinish_ne, hfinish_deg, hconn start finish⟩

theorem section5SimpleGraph.exists_other_degreeOne {n : ℕ}
    (nodes : Finset (Section5Node n)) (f : SelfMapOnRentSimplex n) {start : nodes}
    (hstart : section5NodeDegree nodes f start = 1)
    (hdeg : ∀ v : nodes, section5NodeDegree nodes f v ≤ 2) :
    ∃ finish : nodes,
      finish ≠ start ∧ section5NodeDegree nodes f finish = 1 := by
  classical
  let G : SimpleGraph nodes := section5SimpleGraph nodes f
  letI : DecidableRel G.Adj := Classical.decRel _
  rcases SimpleGraph.exists_other_degreeOne G
      (by simpa [section5NodeDegree, G] using hstart)
      (by
        intro v
        simpa [section5NodeDegree, G] using hdeg v) with
    ⟨finish, hfinish_ne, hfinish_deg⟩
  exact ⟨finish, hfinish_ne, by
    simpa [section5NodeDegree, G] using hfinish_deg⟩

theorem section5SimpleGraph.exists_other_endpoint {n : ℕ}
    (nodes : Finset (Section5Node n)) (f : SelfMapOnRentSimplex n) {start : nodes}
    (hstart : section5NodeDegree nodes f start = 1)
    (hdeg : ∀ v : nodes, section5NodeDegree nodes f v ≤ 2)
    (hconn : (section5SimpleGraph nodes f).Preconnected) :
    ∃ finish : nodes,
      finish ≠ start ∧
      section5NodeDegree nodes f finish = 1 ∧
      (section5SimpleGraph nodes f).Reachable start finish := by
  classical
  let G : SimpleGraph nodes := section5SimpleGraph nodes f
  letI : DecidableRel G.Adj := Classical.decRel _
  rcases SimpleGraph.exists_other_endpoint G
      (by simpa [section5NodeDegree, G] using hstart)
      (by
        intro v
        simpa [section5NodeDegree, G] using hdeg v)
      hconn with
    ⟨finish, hfinish_ne, hfinish_deg, hreach⟩
  exact ⟨finish, hfinish_ne, by
    simpa [section5NodeDegree, G] using hfinish_deg, hreach⟩

theorem section5SimpleGraph.exists_targetFacet_of_endpoint_rule {n : ℕ} [NeZero n]
    (nodes : Finset (Section5Node n)) (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n)
    (hf : IsFaceRespecting f) {start : nodes}
    (hstart : section5NodeDegree nodes f start = 1)
    (hdeg : ∀ v : nodes, section5NodeDegree nodes f v ≤ 2)
    (hconn : (section5SimpleGraph nodes f).Preconnected)
    (hendpoint :
      ∀ v : nodes, section5NodeDegree nodes f v = 1 →
        v = start ∨ IsSection5Endpoint T f v.1) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  rcases section5SimpleGraph.exists_other_endpoint nodes f hstart hdeg hconn with
    ⟨finish, hfinish_ne, hfinish_deg, _hreach⟩
  rcases hendpoint finish hfinish_deg with rfl | hfinish_endpoint
  · exact False.elim (hfinish_ne rfl)
  · exact hfinish_endpoint.exists_targetFacet hf

theorem section5Nodes.exists_targetFacet_of_endpoint_rule {n : ℕ} [NeZero n]
    (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n) (hf : IsFaceRespecting f)
    (hstart : IsSection5GraphNode T f (section5StartNode n))
    (hstartdeg :
      section5NodeDegree (section5Nodes T f) f (section5StartNodeInNodes hstart) = 1)
    (hdeg : ∀ v : section5Nodes T f, section5NodeDegree (section5Nodes T f) f v ≤ 2)
    (hconn : (section5SimpleGraph (section5Nodes T f) f).Preconnected)
    (hendpoint :
      ∀ v : section5Nodes T f,
        section5NodeDegree (section5Nodes T f) f v = 1 →
          v = section5StartNodeInNodes hstart ∨ IsSection5Endpoint T f v.1) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact section5SimpleGraph.exists_targetFacet_of_endpoint_rule
    (nodes := section5Nodes T f) (T := T) (f := f) hf
    (start := section5StartNodeInNodes hstart) hstartdeg hdeg hconn hendpoint

/-- The degree of one node in the explicit Section 5 start component. -/
abbrev section5StartComponentNodeDegree {n : ℕ} [NeZero n] {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (v : section5StartComponent hstart) : ℕ := by
  classical
  exact (Finset.univ.filter fun w : section5StartComponent hstart =>
    (section5StartComponentGraph hstart).Adj v w).card

theorem section5StartComponentGraph_degree_le_two_of_upper_neighbor_unique {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hupper :
      ∀ {u a b : section5StartComponent hstart},
        (section5StartComponentGraph hstart).Adj u a →
        u.1.1.level + 1 = a.1.1.level →
        (section5StartComponentGraph hstart).Adj u b →
        u.1.1.level + 1 = b.1.1.level →
        a = b) :
    ∀ u : section5StartComponent hstart, section5StartComponentNodeDegree u ≤ 2 := by
  classical
  intro u
  rw [section5StartComponentNodeDegree]
  by_contra hdeg
  have hthree :
      2 <
        (Finset.univ.filter fun w : section5StartComponent hstart =>
          (section5StartComponentGraph hstart).Adj u w).card := by
    omega
  rcases Finset.two_lt_card.mp hthree with
    ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  have haAdj : (section5StartComponentGraph hstart).Adj u a :=
    (Finset.mem_filter.mp ha).2
  have hbAdj : (section5StartComponentGraph hstart).Adj u b :=
    (Finset.mem_filter.mp hb).2
  have hcAdj : (section5StartComponentGraph hstart).Adj u c :=
    (Finset.mem_filter.mp hc).2
  rcases section5StartComponentGraph_adj_level_cases hstart haAdj with haDir | haDir
  · rcases section5StartComponentGraph_adj_level_cases hstart hbAdj with hbDir | hbDir
    · exact hab <| hupper haAdj haDir hbAdj hbDir
    · rcases section5StartComponentGraph_adj_level_cases hstart hcAdj with hcDir | hcDir
      · exact hac <| hupper haAdj haDir hcAdj hcDir
      · exact hbc <| section5StartComponentGraph_lower_neighbor_unique
          (hstart := hstart) (u := u) (a := b) (b := c) hbAdj.symm hbDir hcAdj.symm hcDir
  · rcases section5StartComponentGraph_adj_level_cases hstart hbAdj with hbDir | hbDir
    · rcases section5StartComponentGraph_adj_level_cases hstart hcAdj with hcDir | hcDir
      · exact hbc <| hupper hbAdj hbDir hcAdj hcDir
      · exact hac <| section5StartComponentGraph_lower_neighbor_unique
          (hstart := hstart) (u := u) (a := a) (b := c) haAdj.symm haDir hcAdj.symm hcDir
    · exact hab <| section5StartComponentGraph_lower_neighbor_unique
        (hstart := hstart) (u := u) (a := a) (b := b) haAdj.symm haDir hbAdj.symm hbDir

theorem section5StartComponent_nonstart_degree_one_is_endpoint_of_no_upper_neighbor_endpoint
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hendpoint :
      ∀ v : section5StartComponent hstart,
        (¬ ∃ w : section5StartComponent hstart,
            (section5StartComponentGraph hstart).Adj v w ∧
              v.1.1.level + 1 = w.1.1.level) →
          IsSection5Endpoint T f v.1.1) :
    ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v = 1 →
      v ≠ section5StartVertexInComponent hstart →
        IsSection5Endpoint T f v.1.1 := by
  classical
  intro v hvdeg hvstart
  by_cases hupper :
      ∃ w : section5StartComponent hstart,
        (section5StartComponentGraph hstart).Adj v w ∧
          v.1.1.level + 1 = w.1.1.level
  · rcases section5StartComponent_exists_lower_neighbor_of_ne_start hvstart with ⟨u, huAdj, huLevel⟩
    rcases hupper with ⟨w, hwAdj, hwLevel⟩
    have huwNe : u ≠ w := by
      intro huw
      subst w
      omega
    have hCard :
        1 <
          (Finset.univ.filter fun z : section5StartComponent hstart =>
            (section5StartComponentGraph hstart).Adj v z).card := by
      apply Finset.one_lt_card.mpr
      refine ⟨u, ?_, w, ?_, huwNe⟩
      · simp [huAdj.symm]
      · simp [hwAdj]
    rw [section5StartComponentNodeDegree] at hvdeg
    omega
  · exact hendpoint v hupper

/-- The graph-theoretic form of the paper's generic segment-intersection claims on the connected
component of the Section 5 graph that starts at `e₁`. -/
structure Section5StartComponentGenericity {n : ℕ} [NeZero n]
    (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n)
    (hstart : IsSection5GraphNode T f (section5StartNode n)) : Prop where
  start_unique_neighbor :
    ∃! v : section5StartComponent hstart,
      (section5StartComponentGraph hstart).Adj (section5StartVertexInComponent hstart) v
  degree_le_two :
    ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v ≤ 2
  degree_one_or_endpoint :
    ∀ v : section5StartComponent hstart,
      section5StartComponentNodeDegree v = 1 →
        v = section5StartVertexInComponent hstart ∨ IsSection5Endpoint T f v.1.1

theorem Section5StartComponentGenericity.start_degree_one {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgen : Section5StartComponentGenericity T f hstart) :
    section5StartComponentNodeDegree (section5StartVertexInComponent hstart) = 1 := by
  classical
  rw [section5StartComponentNodeDegree, Finset.card_eq_one]
  rcases hgen.start_unique_neighbor with ⟨v, hv, huniq⟩
  refine ⟨v, ?_⟩
  ext w
  constructor
  · intro hw
    have hw' :
        (section5StartComponentGraph hstart).Adj
          (section5StartVertexInComponent hstart) w := by
      simpa [section5StartComponentGraph_adj_iff] using hw
    simpa [Finset.mem_singleton] using huniq _ hw'
  · intro hw
    have hw' : w = v := by simpa using hw
    subst hw'
    simpa [section5StartComponentGraph_adj_iff] using hv

/-- Endpoint extraction on the explicit Section 5 start component, formulated directly with the
neighbor-cardinality hypotheses needed by the graph argument. -/
theorem section5StartComponentGraph.exists_targetFacet_of_endpoint_rule {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hstartdeg : section5StartComponentNodeDegree (section5StartVertexInComponent hstart) = 1)
    (hdeg : ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v ≤ 2)
    (hendpoint :
      ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v = 1 →
          v = section5StartVertexInComponent hstart ∨ IsSection5Endpoint T f v.1.1) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  classical
  letI : DecidableRel (section5StartComponentGraph hstart).Adj := Classical.decRel _
  have hstartdeg' :
      ((section5StartComponentGraph hstart).neighborFinset
        (section5StartVertexInComponent hstart)).card = 1 := by
    simpa [section5StartComponentNodeDegree, SimpleGraph.neighborFinset_eq_filter] using hstartdeg
  have hdeg' :
      ∀ v : section5StartComponent hstart,
        ((section5StartComponentGraph hstart).neighborFinset v).card ≤ 2 := by
    intro v
    simpa [section5StartComponentNodeDegree, SimpleGraph.neighborFinset_eq_filter] using hdeg v
  rcases SimpleGraph.exists_other_endpoint (section5StartComponentGraph hstart) hstartdeg'
      hdeg'
      (section5StartComponentGraph_preconnected hstart) with
    ⟨finish, hfinish_ne, hfinish_deg, _⟩
  rcases hendpoint finish (by
      simpa [section5StartComponentNodeDegree, SimpleGraph.neighborFinset_eq_filter] using
        hfinish_deg) with rfl | hfinish
  · exact False.elim (hfinish_ne rfl)
  · exact hfinish.exists_targetFacet hf

theorem section5StartComponentGraph.exists_targetFacet_of_upper_neighbor_and_no_upper_endpoint_rule
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hstartdeg : section5StartComponentNodeDegree (section5StartVertexInComponent hstart) = 1)
    (hupper :
      ∀ {u a b : section5StartComponent hstart},
        (section5StartComponentGraph hstart).Adj u a →
        u.1.1.level + 1 = a.1.1.level →
        (section5StartComponentGraph hstart).Adj u b →
        u.1.1.level + 1 = b.1.1.level →
        a = b)
    (hendpoint :
      ∀ v : section5StartComponent hstart,
        (¬ ∃ w : section5StartComponent hstart,
            (section5StartComponentGraph hstart).Adj v w ∧
              v.1.1.level + 1 = w.1.1.level) →
          IsSection5Endpoint T f v.1.1) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  refine section5StartComponentGraph.exists_targetFacet_of_endpoint_rule
    (T := T) (f := f) hf hstartdeg
    (section5StartComponentGraph_degree_le_two_of_upper_neighbor_unique
      (hstart := hstart) hupper) ?_
  intro v hvdeg
  by_cases hvstart : v = section5StartVertexInComponent hstart
  · exact Or.inl hvstart
  · exact Or.inr <|
      section5StartComponent_nonstart_degree_one_is_endpoint_of_no_upper_neighbor_endpoint
        (T := T) (f := f) (hstart := hstart) hendpoint v hvdeg hvstart

theorem Section5StartComponentGenericity.exists_targetFacet {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgen : Section5StartComponentGenericity T f hstart) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact section5StartComponentGraph.exists_targetFacet_of_endpoint_rule
    (T := T) (f := f) hf hgen.start_degree_one hgen.degree_le_two hgen.degree_one_or_endpoint

/-- The paper's Section 5 genericity input, separated from the graph-theoretic packaging.
It says that the barycenter-chain preimage looks locally like a 1-dimensional walk:
the start node has one boundary-chain successor, every node has at most two neighbors, and any
non-start degree-one node is already terminal at the barycenter. -/
structure Section5SegmentGeometry {n : ℕ} [NeZero n]
    (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n)
    (hstart : IsSection5GraphNode T f (section5StartNode n)) : Prop where
  start_unique_boundary_successor :
    ∃! v : section5StartComponent hstart,
      (section5StartComponentGraph hstart).Adj (section5StartVertexInComponent hstart) v
  degree_le_two :
    ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v ≤ 2
  nonstart_degree_one_is_endpoint :
    ∀ v : section5StartComponent hstart,
      section5StartComponentNodeDegree v = 1 →
        v ≠ section5StartVertexInComponent hstart →
          IsSection5Endpoint T f v.1.1

theorem Section5SegmentGeometry.toStartComponentGenericity {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgeom : Section5SegmentGeometry T f hstart) :
    Section5StartComponentGenericity T f hstart := by
  refine ⟨hgeom.start_unique_boundary_successor, hgeom.degree_le_two, ?_⟩
  intro v hv
  by_cases hEq : v = section5StartVertexInComponent hstart
  · exact Or.inl hEq
  · exact Or.inr (hgeom.nonstart_degree_one_is_endpoint v hv hEq)

theorem Section5SegmentGeometry.exists_targetFacet {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgeom : Section5SegmentGeometry T f hstart) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact (hgeom.toStartComponentGenericity).exists_targetFacet hf

theorem section5StartComponent_existsLevelOneSuccessor_of_faceRespecting {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)} :
    ∃ v : section5StartComponent hstart,
      v.1.1.level = 1 ∧ (section5StartCell n).IsSubfaceOf v.1.1.cell := by
  rcases T.exists_min_nonstart_section5BoundaryVertex hn with
    ⟨v, hvT, hvFace, hvNe, hmin⟩
  let m : RentSimplex n := section5StartSegmentMidpoint v
  have hmFace : m ∈ coordinateFace (prefixRooms n 2) := by
    simpa [m] using section5StartSegmentMidpoint_mem_coordinateFace_two hvFace
  have hmNe : m ≠ section5StartVertex n := by
    simpa [m] using section5StartSegmentMidpoint_ne_start hn hvFace hvNe
  rcases T.covers_simplex m with ⟨τ, hτ, hmτ⟩
  have hmBoundary :
      ((m : RentSimplex n) : RentCoordinates n) ∈ τ.section5BoundaryFace.realization := by
    exact τ.mem_section5BoundaryFace_realization_of_mem_realization_of_mem_coordinateFace_two
      hmFace hmτ
  have hstartMem : section5StartVertex n ∈ τ.section5BoundaryFace.vertices := by
    exact T.section5StartVertex_mem_boundaryFace_of_midpoint_realization
      hn hτ hvFace hvNe hmin (by simpa [m] using hmBoundary)
  rcases exists_nonstart_boundary_vertex_of_mem_convexHull hn hmFace hmNe
      (by simpa [SimplexFacet.realization, SimplexFacet.pointSet, m] using hmBoundary) with
    ⟨a, haMem, _, haNe⟩
  have hcard_le : τ.section5BoundaryFace.vertices.card ≤ 2 := by
    simpa [SimplexFacet.section5BoundaryFace_vertices] using T.boundaryVertices_card_le_two hn hτ
  have hcard : τ.section5BoundaryFace.vertices.card = 2 := by
    have hcard_gt : 1 < τ.section5BoundaryFace.vertices.card := by
      have hstartNeA : section5StartVertex n ≠ a := by
        intro hEq
        exact haNe hEq.symm
      exact Finset.one_lt_card.mpr ⟨section5StartVertex n, hstartMem, a, haMem, hstartNeA⟩
    have hcard_ge : 2 ≤ τ.section5BoundaryFace.vertices.card := by
      omega
    omega
  have hstartSub : (section5StartCell n).IsSubfaceOf τ.section5BoundaryFace := by
    intro w hw
    have hwEq : w = section5StartVertex n := by
      simpa [section5StartCell] using hw
    subst hwEq
    exact hstartMem
  let u : Section5Node n := { level := 1, cell := τ.section5BoundaryFace }
  have huGraph : IsSection5GraphNode T f u := by
    refine ⟨by simpa [u] using hn, T.section5BoundaryFace_isFace hτ, by simpa [u] using hcard,
      ?_, ?_⟩
    · intro w hw
      have hw' : w ∈ τ.section5BoundaryVertices := by
        simpa [u, SimplexFacet.section5BoundaryFace_vertices] using hw
      exact (τ.mem_section5BoundaryVertices_iff.mp hw').2
    · refine ⟨prefixBarycenter n 1, ?_, ?_⟩
      · rw [FacetImageHull, ← hf.map_section5StartVertex_eq_prefixBarycenter]
        exact subset_convexHull ℝ _ <|
          Set.mem_image_of_mem (fun x : RentSimplex n => f x) hstartMem
      · change prefixBarycenter n 1 ∈ segment ℝ (prefixBarycenter n 1) (prefixBarycenter n 2)
        exact left_mem_segment ℝ (prefixBarycenter n 1) (prefixBarycenter n 2)
  let uNode : section5Nodes T f := ⟨u, mem_section5Nodes_iff.mpr huGraph⟩
  have huAdj :
      (section5NodeGraph T f).Adj (section5StartNodeInNodes hstart) uNode := by
    have huAdjRaw : Section5Adjacent f (section5StartNode n) u := by
      exact section5Adjacent_startNode_iff.mpr ⟨by simp [u], by simpa [u] using hstartSub,
        hf.startCell_hits_prefixBarycenter⟩
    simpa [section5NodeGraph, section5SimpleGraph, uNode, section5StartNodeInNodes] using huAdjRaw
  have huReach :
      (section5NodeGraph T f).Reachable (section5StartNodeInNodes hstart) uNode :=
    SimpleGraph.Adj.reachable huAdj
  have huSupp : uNode ∈ (section5StartComponent hstart).supp :=
    (mem_section5StartComponent_iff_reachable hstart).2 huReach
  refine ⟨⟨uNode, huSupp⟩, ?_, ?_⟩
  · change u.level = 1
    simp [u]
  · change (section5StartCell n).IsSubfaceOf u.cell
    simpa [u] using hstartSub

theorem section5StartComponent_existsUnique_levelOneSuccessor_of_exists {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hex :
      ∃ v : section5StartComponent hstart,
        v.1.1.level = 1 ∧ (section5StartCell n).IsSubfaceOf v.1.1.cell) :
    ∃! v : section5StartComponent hstart,
      v.1.1.level = 1 ∧ (section5StartCell n).IsSubfaceOf v.1.1.cell := by
  rcases hex with ⟨v, hv⟩
  refine ⟨v, hv, ?_⟩
  intro w hw
  have hvNode : IsSection5GraphNode T f v.1.1 := mem_section5Nodes_iff.mp v.1.2
  have hwNode : IsSection5GraphNode T f w.1.1 := mem_section5Nodes_iff.mp w.1.2
  have hcell : v.1.1.cell = w.1.1.cell :=
    hvNode.levelOne_cell_eq_of_start_subface hv.1 hv.2 hwNode hw.1 hw.2
  have hnode : v.1.1 = w.1.1 :=
    Section5Node.eq_of_level_eq_one_of_cell_eq hv.1 hw.1 hcell
  have hnode' : v.1 = w.1 := by
    exact Subtype.ext hnode
  exact Subtype.ext hnode'.symm

theorem section5StartComponent_existsUnique_levelOneSuccessor_of_faceRespecting {n : ℕ}
    [NeZero n] (hn : 2 ≤ n) {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)} :
    ∃! v : section5StartComponent hstart,
      v.1.1.level = 1 ∧ (section5StartCell n).IsSubfaceOf v.1.1.cell := by
  exact section5StartComponent_existsUnique_levelOneSuccessor_of_exists <|
    section5StartComponent_existsLevelOneSuccessor_of_faceRespecting
      (T := T) (f := f) (hstart := hstart) hn hf

/-- The start-vertex portion of the Section 5 geometry: the singleton vertex `e₁` hits `b₁`,
and among nodes in the start component there is a unique level-1 cell containing that vertex. -/
structure Section5StartBoundaryGeometry {n : ℕ} [NeZero n]
    (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n)
    (hstart : IsSection5GraphNode T f (section5StartNode n)) : Prop where
  start_hits_barycenter :
    FacetImageContains f (section5StartCell n) (prefixBarycenter n 1)
  unique_levelOne_successor :
    ∃! v : section5StartComponent hstart,
      v.1.1.level = 1 ∧ (section5StartCell n).IsSubfaceOf v.1.1.cell

theorem section5StartBoundaryGeometry_of_pointAndSuccessorData {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hpoint : f (section5StartVertex n) = prefixBarycenter n 1)
    (hsucc :
      ∃! v : section5StartComponent hstart,
        v.1.1.level = 1 ∧ (section5StartCell n).IsSubfaceOf v.1.1.cell) :
    Section5StartBoundaryGeometry T f hstart := by
  refine ⟨?_, hsucc⟩
  rw [facetImageContains_section5StartCell_iff]
  exact hpoint.symm

theorem section5StartBoundaryGeometry_of_faceRespectingAndSuccessorData {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hf : IsFaceRespecting f)
    (hsucc :
      ∃! v : section5StartComponent hstart,
        v.1.1.level = 1 ∧ (section5StartCell n).IsSubfaceOf v.1.1.cell) :
    Section5StartBoundaryGeometry T f hstart := by
  refine ⟨hf.startCell_hits_prefixBarycenter, hsucc⟩

theorem section5StartBoundaryGeometry_of_faceRespectingAndExistsLevelOneSuccessor
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hf : IsFaceRespecting f)
    (hex :
      ∃ v : section5StartComponent hstart,
        v.1.1.level = 1 ∧ (section5StartCell n).IsSubfaceOf v.1.1.cell) :
    Section5StartBoundaryGeometry T f hstart := by
  exact section5StartBoundaryGeometry_of_faceRespectingAndSuccessorData
    (T := T) (f := f) (hstart := hstart) hf
    (section5StartComponent_existsUnique_levelOneSuccessor_of_exists hex)

theorem section5StartBoundaryGeometry_of_faceRespecting {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hf : IsFaceRespecting f) :
    Section5StartBoundaryGeometry T f hstart := by
  exact section5StartBoundaryGeometry_of_faceRespectingAndExistsLevelOneSuccessor
    (T := T) (f := f) (hstart := hstart) hf <|
      section5StartComponent_existsLevelOneSuccessor_of_faceRespecting
        (T := T) (f := f) (hstart := hstart) hn hf

theorem Section5StartBoundaryGeometry.start_unique_neighbor {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgeom : Section5StartBoundaryGeometry T f hstart) :
    ∃! v : section5StartComponent hstart,
      (section5StartComponentGraph hstart).Adj (section5StartVertexInComponent hstart) v := by
  rcases hgeom.unique_levelOne_successor with ⟨v, hv, huniq⟩
  refine ⟨v, ?_, ?_⟩
  · exact (section5StartComponentGraph_adj_start_iff hstart).mpr
      ⟨hv.1, hv.2, hgeom.start_hits_barycenter⟩
  · intro w hw
    apply huniq w
    rcases (section5StartComponentGraph_adj_start_iff hstart).mp hw with ⟨hlevel, hsub, _⟩
    exact ⟨hlevel, hsub⟩

theorem Section5StartBoundaryGeometry.start_degree_one {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgeom : Section5StartBoundaryGeometry T f hstart) :
    section5StartComponentNodeDegree (section5StartVertexInComponent hstart) = 1 := by
  classical
  rw [section5StartComponentNodeDegree, Finset.card_eq_one]
  rcases hgeom.start_unique_neighbor with ⟨v, hv, huniq⟩
  refine ⟨v, ?_⟩
  ext w
  constructor
  · intro hw
    have hw' :
        (section5StartComponentGraph hstart).Adj
          (section5StartVertexInComponent hstart) w := by
      simpa [section5StartComponentNodeDegree] using hw
    simpa [Finset.mem_singleton] using huniq _ hw'
  · intro hw
    have hw' : w = v := by simpa using hw
    subst hw'
    simpa [section5StartComponentNodeDegree] using hv

theorem section5StartComponent_startDegreeOne_of_faceRespectingAndExistsLevelOneSuccessor
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hf : IsFaceRespecting f)
    (hex :
      ∃ v : section5StartComponent hstart,
        v.1.1.level = 1 ∧ (section5StartCell n).IsSubfaceOf v.1.1.cell) :
    section5StartComponentNodeDegree (section5StartVertexInComponent hstart) = 1 := by
  exact Section5StartBoundaryGeometry.start_degree_one <|
    section5StartBoundaryGeometry_of_faceRespectingAndExistsLevelOneSuccessor
      (T := T) (f := f) (hstart := hstart) hf hex

theorem section5StartComponent_startDegreeOne_of_faceRespecting {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hf : IsFaceRespecting f) :
    section5StartComponentNodeDegree (section5StartVertexInComponent hstart) = 1 := by
  exact section5StartComponent_startDegreeOne_of_faceRespectingAndExistsLevelOneSuccessor
    (T := T) (f := f) (hstart := hstart) hf <|
      section5StartComponent_existsLevelOneSuccessor_of_faceRespecting
        (T := T) (f := f) (hstart := hstart) hn hf

theorem section5SegmentGeometry_of_startBoundaryGeometry {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hstartGeom : Section5StartBoundaryGeometry T f hstart)
    (hdeg : ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v ≤ 2)
    (hendpoint :
      ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v = 1 →
        v ≠ section5StartVertexInComponent hstart →
          IsSection5Endpoint T f v.1.1) :
    Section5SegmentGeometry T f hstart := by
  refine ⟨hstartGeom.start_unique_neighbor, hdeg, ?_⟩
  intro v hv hne
  exact hendpoint v hv hne

theorem section5SegmentGeometry_of_faceRespectingAndLocalDegreeData {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hdeg : ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v ≤ 2)
    (hendpoint :
      ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v = 1 →
        v ≠ section5StartVertexInComponent hstart →
          IsSection5Endpoint T f v.1.1) :
    Section5SegmentGeometry T f hstart := by
  exact section5SegmentGeometry_of_startBoundaryGeometry
    (T := T) (f := f) (hstart := hstart)
    (section5StartBoundaryGeometry_of_faceRespecting
      (T := T) (f := f) (hstart := hstart) hn hf) hdeg hendpoint

theorem Section5StartBoundaryGeometry.exists_targetFacet_of_localDegreeData {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hstartGeom : Section5StartBoundaryGeometry T f hstart)
    (hdeg : ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v ≤ 2)
    (hendpoint :
      ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v = 1 →
        v ≠ section5StartVertexInComponent hstart →
          IsSection5Endpoint T f v.1.1) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact (section5SegmentGeometry_of_startBoundaryGeometry
    (T := T) (f := f) (hstart := hstart) hstartGeom hdeg hendpoint).exists_targetFacet hf

theorem exists_targetFacet_of_faceRespectingAndSuccessorLocalDegreeData {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hsucc :
      ∃! v : section5StartComponent hstart,
        v.1.1.level = 1 ∧ (section5StartCell n).IsSubfaceOf v.1.1.cell)
    (hdeg : ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v ≤ 2)
    (hendpoint :
      ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v = 1 →
        v ≠ section5StartVertexInComponent hstart →
          IsSection5Endpoint T f v.1.1) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact (section5StartBoundaryGeometry_of_faceRespectingAndSuccessorData
    (T := T) (f := f) (hstart := hstart) hf hsucc).exists_targetFacet_of_localDegreeData
      hf hdeg hendpoint

theorem exists_targetFacet_of_faceRespectingAndLocalDegreeData {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hdeg : ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v ≤ 2)
    (hendpoint :
      ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v = 1 →
        v ≠ section5StartVertexInComponent hstart →
          IsSection5Endpoint T f v.1.1) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact (section5SegmentGeometry_of_faceRespectingAndLocalDegreeData
    (T := T) (f := f) (hstart := hstart) hn hf hdeg hendpoint).exists_targetFacet hf

/-- The remaining Section 5 genericity input, stated directly with actual pointwise witnesses on
prefix-face realizations produced by the piecewise-affine structure. -/
structure Section5PointwiseGenericity {n : ℕ} [NeZero n]
    (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n)
    (hstart : IsSection5GraphNode T f (section5StartNode n)) where
  piecewiseAffine : IsPiecewiseAffineOn T f
  upper_continuation_unique :
    ∀ {u a b : section5StartComponent hstart},
      (section5StartComponentGraph hstart).Adj u a →
      u.1.1.level + 1 = a.1.1.level →
      (section5StartComponentGraph hstart).Adj u b →
      u.1.1.level + 1 = b.1.1.level →
      FaceHitWitness T f u.1.1.cell (prefixBarycenter n (u.1.1.level + 1)) →
      a = b
  no_upper_neighbor_hits_barycenter :
    ∀ v : section5StartComponent hstart,
      (¬ ∃ w : section5StartComponent hstart,
          (section5StartComponentGraph hstart).Adj v w ∧
            v.1.1.level + 1 = w.1.1.level) →
        FaceHitWitness T f v.1.1.cell
          ((rentBarycenter n : RentSimplex n) : RentCoordinates n)

theorem Section5PointwiseGenericity.upper_neighbor_unique {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgeom : Section5PointwiseGenericity T f hstart) :
    ∀ {u a b : section5StartComponent hstart},
      (section5StartComponentGraph hstart).Adj u a →
      u.1.1.level + 1 = a.1.1.level →
      (section5StartComponentGraph hstart).Adj u b →
      u.1.1.level + 1 = b.1.1.level →
      a = b := by
  intro u a b haAdj haLevel hbAdj hbLevel
  have huNode : IsSection5GraphNode T f u.1.1 := mem_section5Nodes_iff.mp u.1.2
  have haAdjRaw : Section5Adjacent f u.1.1 a.1.1 :=
    (section5StartComponentGraph_adj_iff hstart).mp haAdj
  have haStep : Section5Step f u.1.1 a.1.1 :=
    (section5Adjacent_of_level_succ_eq_iff_step (f := f) haLevel).mp haAdjRaw
  have huHit :
      FacetImageContains f u.1.1.cell (prefixBarycenter n (u.1.1.level + 1)) := by
    simpa [haLevel] using haStep.2.2
  let hw : FaceHitWitness T f u.1.1.cell (prefixBarycenter n (u.1.1.level + 1)) :=
    T.faceHitWitnessOfFacetImageContains huNode.isFace hgeom.piecewiseAffine huHit
  exact hgeom.upper_continuation_unique haAdj haLevel hbAdj hbLevel hw

theorem Section5PointwiseGenericity.no_upper_neighbor_is_endpoint {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgeom : Section5PointwiseGenericity T f hstart) :
    ∀ v : section5StartComponent hstart,
      (¬ ∃ w : section5StartComponent hstart,
          (section5StartComponentGraph hstart).Adj v w ∧
            v.1.1.level + 1 = w.1.1.level) →
        IsSection5Endpoint T f v.1.1 := by
  intro v hv
  exact ⟨mem_section5Nodes_iff.mp v.1.2,
    (hgeom.no_upper_neighbor_hits_barycenter v hv).facetImageContains⟩

theorem Section5PointwiseGenericity.toSegmentGeometry {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgeom : Section5PointwiseGenericity T f hstart) :
    Section5SegmentGeometry T f hstart := by
  refine ⟨?_, ?_, ?_⟩
  · exact (section5StartBoundaryGeometry_of_faceRespecting
      (T := T) (f := f) (hstart := hstart) hn hf).start_unique_neighbor
  · exact section5StartComponentGraph_degree_le_two_of_upper_neighbor_unique
      (hstart := hstart) hgeom.upper_neighbor_unique
  · intro v hv hne
    exact section5StartComponent_nonstart_degree_one_is_endpoint_of_no_upper_neighbor_endpoint
      (T := T) (f := f) (hstart := hstart) hgeom.no_upper_neighbor_is_endpoint v hv hne

theorem Section5PointwiseGenericity.exists_targetFacet {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgeom : Section5PointwiseGenericity T f hstart) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact (hgeom.toSegmentGeometry hn hf).exists_targetFacet hf

/-- Minimal local support theorem matching the manuscript's perturbation-to-a-local-1-complex
claim: at each start-component node the upper-neighbor fiber is locally a singleton, and when it
is empty the face already hits the barycenter. -/
structure Section5LocalOneComplexGeometry {n : ℕ} [NeZero n]
    (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n)
    (hstart : IsSection5GraphNode T f (section5StartNode n)) where
  piecewiseAffine : IsPiecewiseAffineOn T f
  upper_neighbors_subsingleton :
    ∀ v : section5StartComponent hstart,
      Subsingleton {w : section5StartComponent hstart //
        (section5StartComponentGraph hstart).Adj v w ∧
          v.1.1.level + 1 = w.1.1.level}
  no_upper_neighbor_hits_barycenter :
    ∀ v : section5StartComponent hstart,
      IsEmpty {w : section5StartComponent hstart //
        (section5StartComponentGraph hstart).Adj v w ∧
          v.1.1.level + 1 = w.1.1.level} →
        FaceHitWitness T f v.1.1.cell
          ((rentBarycenter n : RentSimplex n) : RentCoordinates n)

noncomputable def section5LocalOneComplexGeometry_of_uniqueUpperOrEndpoint {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hpa : IsPiecewiseAffineOn T f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hlocal :
      ∀ v : section5StartComponent hstart,
        IsSection5Endpoint T f v.1.1 ∨
          ∃! w : section5StartComponent hstart,
            (section5StartComponentGraph hstart).Adj v w ∧
              v.1.1.level + 1 = w.1.1.level) :
    Section5LocalOneComplexGeometry T f hstart := by
  classical
  refine ⟨hpa, ?_, ?_⟩
  · intro v
    by_cases hvEndpoint : IsSection5Endpoint T f v.1.1
    · let α := {w : section5StartComponent hstart //
          (section5StartComponentGraph hstart).Adj v w ∧
            v.1.1.level + 1 = w.1.1.level}
      have hEmpty : IsEmpty α := by
        refine ⟨?_⟩
        intro a
        have hvLast : v.1.1.level + 1 = n :=
          hvEndpoint.1.level_eq_last_of_hitsBarycenter hf hvEndpoint.2
        have haNode : IsSection5GraphNode T f a.1.1.1 := mem_section5Nodes_iff.mp a.1.1.2
        have haLevel : v.1.1.level + 1 = a.1.1.1.level := a.2.2
        have : a.1.1.1.level + 1 ≤ n := haNode.level_le
        omega
      letI : IsEmpty α := hEmpty
      infer_instance
    · have hUnique :
          ∃! w : section5StartComponent hstart,
            (section5StartComponentGraph hstart).Adj v w ∧
              v.1.1.level + 1 = w.1.1.level := by
        rcases hlocal v with hEnd | hUnique
        · exact False.elim (hvEndpoint hEnd)
        · exact hUnique
      rcases hUnique with ⟨w, hw, huniq⟩
      refine ⟨?_⟩
      intro a b
      apply Subtype.ext
      exact (huniq a.1 a.2).trans (huniq b.1 b.2).symm
  · intro v hEmpty
    by_cases hvEndpoint : IsSection5Endpoint T f v.1.1
    · exact T.faceHitWitnessOfFacetImageContains hvEndpoint.1.isFace hpa hvEndpoint.2
    · have hUnique :
          ∃! w : section5StartComponent hstart,
            (section5StartComponentGraph hstart).Adj v w ∧
              v.1.1.level + 1 = w.1.1.level := by
        rcases hlocal v with hEnd | hUnique
        · exact False.elim (hvEndpoint hEnd)
        · exact hUnique
      let hex : ∃ w : section5StartComponent hstart,
          (section5StartComponentGraph hstart).Adj v w ∧
            v.1.1.level + 1 = w.1.1.level := ExistsUnique.exists hUnique
      exact False.elim <|
        hEmpty.false ⟨Classical.choose hex, Classical.choose_spec hex⟩

def Section5LocalOneComplexGeometry.toPointwiseGenericity {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgeom : Section5LocalOneComplexGeometry T f hstart) :
    Section5PointwiseGenericity T f hstart := by
  refine ⟨hgeom.piecewiseAffine, ?_, ?_⟩
  · intro u a b haAdj haLevel hbAdj hbLevel _hw
    let a' : {w : section5StartComponent hstart //
        (section5StartComponentGraph hstart).Adj u w ∧
          u.1.1.level + 1 = w.1.1.level} := ⟨a, haAdj, haLevel⟩
    let b' : {w : section5StartComponent hstart //
        (section5StartComponentGraph hstart).Adj u w ∧
          u.1.1.level + 1 = w.1.1.level} := ⟨b, hbAdj, hbLevel⟩
    have hs : Subsingleton {w : section5StartComponent hstart //
        (section5StartComponentGraph hstart).Adj u w ∧
          u.1.1.level + 1 = w.1.1.level} := hgeom.upper_neighbors_subsingleton u
    have hab : a' = b' := hs.elim a' b'
    exact congrArg Subtype.val hab
  · intro v hv
    let hEmpty :
        IsEmpty {w : section5StartComponent hstart //
          (section5StartComponentGraph hstart).Adj v w ∧
            v.1.1.level + 1 = w.1.1.level} := by
      refine ⟨?_⟩
      intro w
      exact hv ⟨w.1, w.2.1, w.2.2⟩
    exact hgeom.no_upper_neighbor_hits_barycenter v hEmpty

theorem Section5LocalOneComplexGeometry.exists_targetFacet {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgeom : Section5LocalOneComplexGeometry T f hstart) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact hgeom.toPointwiseGenericity.exists_targetFacet hn hf

end Arxiv170207325
