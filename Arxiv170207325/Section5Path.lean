import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Arxiv170207325.InteriorTarget
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

theorem prefixBarycenterSegment_subset_ambientCoordinateFace {n k : ℕ} [NeZero k]
    (hk : k + 1 ≤ n) :
    prefixBarycenterSegment n k ⊆ ambientCoordinateFace (prefixRooms n (k + 1)) := by
  have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
  haveI : NeZero (k + 1) := ⟨Nat.succ_ne_zero k⟩
  refine (convex_ambientCoordinateFace _).segment_subset ?_ ?_
  · exact ambientCoordinateFace_mono (prefixRooms_mono (Nat.le_succ k))
      (prefixBarycenter_mem_ambientCoordinateFace hk')
  · exact prefixBarycenter_mem_ambientCoordinateFace hk

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

/-- The triangulation vertices of one facet that lie on the boundary edge `[e₁,e₂]`. -/
def SimplexFacet.section5BoundaryVertices {n : ℕ}
    (τ : SimplexFacet n) : Finset (RentSimplex n) := by
  classical
  exact τ.vertices.filter fun v => v ∈ coordinateFace (prefixRooms n 2)

@[simp]
theorem SimplexFacet.mem_section5BoundaryVertices_iff {n : ℕ} {τ : SimplexFacet n}
    {v : RentSimplex n} :
    v ∈ τ.section5BoundaryVertices ↔ v ∈ τ.vertices ∧ v ∈ coordinateFace (prefixRooms n 2) := by
  classical
  simp [SimplexFacet.section5BoundaryVertices]

theorem SimplexTriangulation.boundaryVertices_card_le_two {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (T : SimplexTriangulation n) {τ : SimplexFacet n} (hτ : τ ∈ T.facets) :
    τ.section5BoundaryVertices.card ≤ 2 := by
  classical
  by_contra hcard
  have hcard' : 2 < τ.section5BoundaryVertices.card := by
    omega
  rcases Finset.two_lt_card.mp hcard' with
    ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  have haτ : a ∈ τ.vertices := (τ.mem_section5BoundaryVertices_iff.mp ha).1
  have hbτ : b ∈ τ.vertices := (τ.mem_section5BoundaryVertices_iff.mp hb).1
  have hcτ : c ∈ τ.vertices := (τ.mem_section5BoundaryVertices_iff.mp hc).1
  have haFace : a ∈ coordinateFace (prefixRooms n 2) :=
    (τ.mem_section5BoundaryVertices_iff.mp ha).2
  have hbFace : b ∈ coordinateFace (prefixRooms n 2) :=
    (τ.mem_section5BoundaryVertices_iff.mp hb).2
  have hcFace : c ∈ coordinateFace (prefixRooms n 2) :=
    (τ.mem_section5BoundaryVertices_iff.mp hc).2
  let emb : Fin 3 ↪ τ.vertices := {
    toFun := ![⟨a, haτ⟩, ⟨b, hbτ⟩, ⟨c, hcτ⟩]
    inj' := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exfalso
        exact hab (by simpa using congrArg Subtype.val hij)
      · exfalso
        exact hac (by simpa using congrArg Subtype.val hij)
      · exfalso
        exact hab.symm (by simpa using congrArg Subtype.val hij)
      · rfl
      · exfalso
        exact hbc (by simpa using congrArg Subtype.val hij)
      · exfalso
        exact hac.symm (by simpa using congrArg Subtype.val hij)
      · exfalso
        exact hbc.symm (by simpa using congrArg Subtype.val hij)
      · rfl }
  let p : Fin 3 → RentCoordinates n := fun i =>
    ((((emb i : τ.vertices) : RentSimplex n) : RentCoordinates n))
  have hind : AffineIndependent ℝ p := by
    exact (T.facet_affineIndependent τ hτ).comp_embedding emb
  have hnotcol :
      ¬ Collinear ℝ
        ({((a : RentSimplex n) : RentCoordinates n),
          ((b : RentSimplex n) : RentCoordinates n),
          ((c : RentSimplex n) : RentCoordinates n)} : Set (RentCoordinates n)) :=
    by
      have hnotcol' :
          ¬ Collinear ℝ ({p 0, p 1, p 2} : Set (RentCoordinates n)) :=
        (affineIndependent_iff_not_collinear_of_ne
          (k := ℝ) (p := p) (by decide) (by decide) (by decide)).mp hind
      simpa [p, emb]
  exact hnotcol (collinear_boundary_vertices hn haFace hbFace hcFace)

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

end Arxiv170207325
