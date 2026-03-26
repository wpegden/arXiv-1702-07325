import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Powerset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Analysis.Normed.Module.FiniteDimension
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

/-- Sum of coordinates outside a prescribed face. This is the linear functional suggested by the
stuck-recovery route for detecting when a point has left the lower prefix face. -/
def outsideMass {n : ℕ} (I : Finset (RoomIndex n)) (y : RentCoordinates n) : ℝ :=
  Finset.sum (Finset.univ.filter fun i : RoomIndex n => i ∉ I) fun i => y i

theorem outsideMass_nonneg {n : ℕ} {I : Finset (RoomIndex n)} {x : RentSimplex n} :
    0 ≤ outsideMass I (x : RentCoordinates n) := by
  unfold outsideMass
  exact Finset.sum_nonneg (by intro i _; exact x.2.1 i)

@[simp]
theorem outsideMass_eq_zero_iff_mem_coordinateFace {n : ℕ} {I : Finset (RoomIndex n)}
    {x : RentSimplex n} :
    outsideMass I (x : RentCoordinates n) = 0 ↔ x ∈ coordinateFace I := by
  constructor
  · intro hmass
    rw [mem_coordinateFace_iff]
    intro i hi
    have hterms :
        ∀ j ∈ Finset.univ.filter (fun j : RoomIndex n => j ∉ I),
          ((x : RentCoordinates n) j) = 0 := by
      simpa [outsideMass] using
        (Finset.sum_eq_zero_iff_of_nonneg (by intro j _; exact x.2.1 j)).mp hmass
    have hi' : i ∈ Finset.univ.filter (fun j : RoomIndex n => j ∉ I) := by
      simp [hi]
    exact hterms i hi'
  · intro hx
    unfold outsideMass
    apply Finset.sum_eq_zero
    intro i hi
    exact (mem_coordinateFace_iff.mp hx) i (Finset.mem_filter.mp hi).2

theorem outsideMass_pos_of_not_mem_coordinateFace {n : ℕ} {I : Finset (RoomIndex n)}
    {x : RentSimplex n} (hx : x ∉ coordinateFace I) :
    0 < outsideMass I (x : RentCoordinates n) := by
  have hnonneg : 0 ≤ outsideMass I (x : RentCoordinates n) :=
    outsideMass_nonneg (I := I) (x := x)
  by_contra hnot
  have hzero : outsideMass I (x : RentCoordinates n) = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  exact hx ((outsideMass_eq_zero_iff_mem_coordinateFace (I := I) (x := x)).mp hzero)

theorem outsideMass_lineMap {n : ℕ} {I : Finset (RoomIndex n)}
    (x y : RentCoordinates n) (t : ℝ) :
    outsideMass I (AffineMap.lineMap x y t) =
      (1 - t) * outsideMass I x + t * outsideMass I y := by
  unfold outsideMass
  rw [AffineMap.lineMap_apply_module]
  simp_rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

theorem continuous_outsideMass {n : ℕ} {I : Finset (RoomIndex n)} :
    Continuous (outsideMass I) := by
  unfold outsideMass
  exact continuous_finset_sum _ (by
    intro i hi
    exact continuous_apply i)

/-- The standard simplex vertices spanning the prefix face `conv{e_1, ..., e_k}`. -/
def prefixVertexPoints (n k : ℕ) : Finset (RentCoordinates n) :=
  (prefixRooms n k).image fun i : RoomIndex n =>
    ((stdSimplex.vertex (S := ℝ) i : RentSimplex n) : RentCoordinates n)

theorem prefixVertexPoints_card {n k : ℕ} (hk : k ≤ n) :
    (prefixVertexPoints n k).card = k := by
  classical
  unfold prefixVertexPoints
  rw [Finset.card_image_of_injective]
  · simpa using prefixRooms_card (n := n) (k := k) hk
  · intro i j hij
    exact stdSimplex.vertex_injective (Subtype.ext hij)

theorem mem_convexHull_prefixVertexPoints_of_mem_coordinateFace {n k : ℕ}
    {x : RentSimplex n} (hx : x ∈ coordinateFace (prefixRooms n k)) :
    ((x : RentSimplex n) : RentCoordinates n) ∈
      convexHull ℝ ((prefixVertexPoints n k : Finset (RentCoordinates n)) :
        Set (RentCoordinates n)) := by
  classical
  rw [mem_coordinateFace_iff] at hx
  have hsum_prefix : ∑ i ∈ prefixRooms n k, x i = 1 := by
    rw [prefixRooms, Finset.sum_filter]
    calc
      (∑ i : RoomIndex n, if i.1 < k then x i else 0) = ∑ i : RoomIndex n, x i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hi' : i.1 < k
        · simp [hi']
        · have hxi0 : x i = 0 := hx i (by simpa [mem_prefixRooms_iff] using hi')
          simp [hi', hxi0]
      _ = 1 := stdSimplex.sum_eq_one x
  have hx_eq_center :
      (prefixRooms n k).centerMass (fun i : RoomIndex n => x i)
        (fun i : RoomIndex n =>
          ((stdSimplex.vertex (S := ℝ) i : RentSimplex n) : RentCoordinates n)) =
        ((x : RentSimplex n) : RentCoordinates n) := by
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsum_prefix]
    ext j
    rw [Finset.sum_apply]
    by_cases hj : j ∈ prefixRooms n k
    · rw [Finset.sum_eq_single j]
      · simp
      · intro i hi hij
        change x i * (((stdSimplex.vertex (S := ℝ) i : RentSimplex n) : RentCoordinates n) j) = 0
        have hji : j ≠ i := by simpa using hij.symm
        simp [stdSimplex_vertex_apply, hji]
      · simp [hj]
    · have hxj0 : x j = 0 := hx j hj
      rw [hxj0]
      refine Finset.sum_eq_zero ?_
      intro i hi
      change x i * (((stdSimplex.vertex (S := ℝ) i : RentSimplex n) : RentCoordinates n) j) = 0
      have hji : j ≠ i := by
        intro hji
        apply hj
        simpa [hji] using hi
      simp [stdSimplex_vertex_apply, hji]
  refine hx_eq_center ▸ Finset.centerMass_mem_convexHull (t := prefixRooms n k)
    (s := ((prefixVertexPoints n k : Finset (RentCoordinates n)) :
      Set (RentCoordinates n))) ?_ ?_ ?_
  · intro i hi
    exact x.2.1 i
  · rw [hsum_prefix]
    norm_num
  · intro i hi
    unfold prefixVertexPoints
    change (((stdSimplex.vertex (S := ℝ) i : RentSimplex n) : RentCoordinates n)) ∈
      Finset.image (fun i : RoomIndex n =>
        ((stdSimplex.vertex (S := ℝ) i : RentSimplex n) : RentCoordinates n))
        (prefixRooms n k)
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

theorem mem_affineSpan_prefixVertexPoints_of_mem_coordinateFace {n k : ℕ}
    {x : RentSimplex n} (hx : x ∈ coordinateFace (prefixRooms n k)) :
    ((x : RentSimplex n) : RentCoordinates n) ∈
      affineSpan ℝ ((prefixVertexPoints n k : Finset (RentCoordinates n)) :
        Set (RentCoordinates n)) :=
  convexHull_subset_affineSpan
    ((prefixVertexPoints n k : Finset (RentCoordinates n)) : Set (RentCoordinates n))
    (mem_convexHull_prefixVertexPoints_of_mem_coordinateFace hx)

def simplexCoordEmbedding (n : ℕ) : RentSimplex n ↪ RentCoordinates n :=
  ⟨fun v => ((v : RentSimplex n) : RentCoordinates n), fun _ _ h => Subtype.ext h⟩

theorem SimplexTriangulation.card_le_prefixVertexPoints_of_subset_coordinateFace {n k : ℕ}
    {T : SimplexTriangulation n} {τ : SimplexFacet n} (hτ : τ ∈ T.facets)
    {S : Finset (RentSimplex n)} (hS : S ⊆ τ.vertices)
    (hface : ∀ ⦃v : RentSimplex n⦄, v ∈ S → v ∈ coordinateFace (prefixRooms n k)) :
    S.card ≤ (prefixVertexPoints n k).card := by
  classical
  let e := simplexCoordEmbedding n
  let pτ : τ.vertices → RentCoordinates n := fun v => ((v : RentSimplex n) : RentCoordinates n)
  let pS : S.map e → RentCoordinates n := fun v => (v : RentCoordinates n)
  have hτ_aff_range : AffineIndependent ℝ (fun x : Set.range pτ => (x : RentCoordinates n)) := by
    exact AffineIndependent.range (T.facet_affineIndependent τ hτ)
  have hS_range_subset : Set.range pS ⊆ Set.range pτ := by
    rintro y ⟨v, rfl⟩
    rcases Finset.mem_map.mp v.2 with ⟨w, hw, hw_eq⟩
    refine ⟨⟨w, hS hw⟩, ?_⟩
    simpa [pτ, pS, e] using hw_eq
  have hS_aff_range : AffineIndependent ℝ (fun x : Set.range pS => (x : RentCoordinates n)) := by
    exact hτ_aff_range.mono hS_range_subset
  have hS_aff : AffineIndependent ℝ ((↑) : (S.map e) → RentCoordinates n) := by
    exact AffineIndependent.of_set_of_injective hS_aff_range Subtype.val_injective
  have hsubset_span :
      ((S.map e : Finset (RentCoordinates n)) : Set (RentCoordinates n)) ⊆
        affineSpan ℝ ((prefixVertexPoints n k : Finset (RentCoordinates n)) :
          Set (RentCoordinates n)) := by
    intro y hy
    rcases Finset.mem_map.mp hy with ⟨v, hv, rfl⟩
    exact mem_affineSpan_prefixVertexPoints_of_mem_coordinateFace (hface hv)
  have hcard := AffineIndependent.card_le_card_of_subset_affineSpan (k := ℝ)
    (s := S.map e) (t := prefixVertexPoints n k) hS_aff hsubset_span
  simpa [e] using hcard

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

theorem prefixBarycenter_mem_ambientCoordinateFace_iff {n k : ℕ} [NeZero k] (hk : k ≤ n)
    {I : Finset (RoomIndex n)} :
    prefixBarycenter n k ∈ ambientCoordinateFace I ↔ prefixRooms n k ⊆ I := by
  constructor
  · intro hy
    simpa [coordSupport_prefixBarycenter] using hy.2
  · intro hI
    exact ambientCoordinateFace_mono hI
      (prefixBarycenter_mem_ambientCoordinateFace (n := n) (k := k) hk)

theorem prefixBarycenter_not_mem_ambientCoordinateFace_erase {n k : ℕ} [NeZero k] (hk : k ≤ n)
    {i : RoomIndex n} (hi : i ∈ prefixRooms n k) :
    prefixBarycenter n k ∉ ambientCoordinateFace (Finset.univ.erase i) := by
  intro hy
  have hsub :
      prefixRooms n k ⊆ Finset.univ.erase i :=
    (prefixBarycenter_mem_ambientCoordinateFace_iff (n := n) (k := k) hk).mp hy
  exact (by simpa using hsub hi : False)

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

theorem isCompact_prefixBarycenterSegment {n k : ℕ} :
    IsCompact (prefixBarycenterSegment n k) := by
  rw [prefixBarycenterSegment, segment_eq_image_lineMap]
  let g : ℝ →ᵃ[ℝ] RentCoordinates n :=
    AffineMap.lineMap (prefixBarycenter n k) (prefixBarycenter n (k + 1))
  have hg : Continuous g := g.continuous_of_finiteDimensional
  simpa [g] using isCompact_Icc.image hg

theorem prefixBarycenterSegment_subset_ambientCoordinateFace {n k : ℕ} [NeZero k]
    (hk : k + 1 ≤ n) :
    prefixBarycenterSegment n k ⊆ ambientCoordinateFace (prefixRooms n (k + 1)) := by
  have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
  haveI : NeZero (k + 1) := ⟨Nat.succ_ne_zero k⟩
  refine (convex_ambientCoordinateFace _).segment_subset ?_ ?_
  · exact ambientCoordinateFace_mono (prefixRooms_mono (Nat.le_succ k))
      (prefixBarycenter_mem_ambientCoordinateFace hk')
  · exact prefixBarycenter_mem_ambientCoordinateFace hk

theorem mem_prefixBarycenterSegment_levelCoord_le {n k : ℕ} [NeZero k]
    (hk : k + 1 ≤ n) {y : RentCoordinates n}
    (hySeg : y ∈ prefixBarycenterSegment n k) :
    let ik : RoomIndex n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
    y ik ≤ ((k + 1 : ℝ)⁻¹) := by
  let ik : RoomIndex n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
  rw [prefixBarycenterSegment, segment_eq_image_lineMap ℝ
    (prefixBarycenter n k) (prefixBarycenter n (k + 1))] at hySeg
  rcases hySeg with ⟨θ, hθ, rfl⟩
  have hk1_nonneg : 0 ≤ ((k + 1 : ℝ)⁻¹) := by positivity
  have hθ_le : θ * ((k + 1 : ℝ)⁻¹) ≤ ((k + 1 : ℝ)⁻¹) := by
    nlinarith [hθ.1, hθ.2, hk1_nonneg]
  simpa [ik, AffineMap.lineMap_apply_module, prefixBarycenter]
    using hθ_le

theorem mem_prefixBarycenterSegment_apply_of_lt {n k : ℕ} [NeZero k]
    (hk : k + 1 ≤ n) {y : RentCoordinates n}
    (hySeg : y ∈ prefixBarycenterSegment n k) {i : RoomIndex n} (hi : i.1 < k) :
    let ik : RoomIndex n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
    y i = (k : ℝ)⁻¹ - y ik / k := by
  let ik : RoomIndex n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
  rw [prefixBarycenterSegment, segment_eq_image_lineMap ℝ
    (prefixBarycenter n k) (prefixBarycenter n (k + 1))] at hySeg
  rcases hySeg with ⟨θ, _hθ0, _hθ1, rfl⟩
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
  have hk1R : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hyi :
      AffineMap.lineMap (prefixBarycenter n k) (prefixBarycenter n (k + 1)) θ i =
        (1 - θ) * (k : ℝ)⁻¹ + θ * ((k + 1 : ℝ)⁻¹) := by
    simp [AffineMap.lineMap_apply_module, prefixBarycenter, hi,
      show i.1 < k + 1 by omega]
  have hyk :
      AffineMap.lineMap (prefixBarycenter n k) (prefixBarycenter n (k + 1)) θ ik =
        θ * ((k + 1 : ℝ)⁻¹) := by
    simp [AffineMap.lineMap_apply_module, prefixBarycenter, ik]
  rw [hyi]
  change
    (1 - θ) * (k : ℝ)⁻¹ + θ * ((k + 1 : ℝ)⁻¹) =
      (k : ℝ)⁻¹ -
        (AffineMap.lineMap (prefixBarycenter n k) (prefixBarycenter n (k + 1)) θ ik) / k
  rw [hyk]
  field_simp [hkR, hk1R]
  ring

theorem mem_prefixBarycenterSegment_iff_mem_ambientCoordinateFace_and_eq_levelCoord
    {n k : ℕ} [NeZero k] (hk : k + 1 ≤ n) {y : RentCoordinates n} :
    y ∈ prefixBarycenterSegment n k ↔
      y ∈ ambientCoordinateFace (prefixRooms n (k + 1)) ∧
        let ik : RoomIndex n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
        y ik ≤ ((k + 1 : ℝ)⁻¹) ∧
          ∀ {i : RoomIndex n}, i.1 < k → y i = (k : ℝ)⁻¹ - y ik / k := by
  constructor
  · intro hySeg
    refine ⟨prefixBarycenterSegment_subset_ambientCoordinateFace hk hySeg, ?_⟩
    exact ⟨mem_prefixBarycenterSegment_levelCoord_le hk hySeg, fun hi =>
      mem_prefixBarycenterSegment_apply_of_lt hk hySeg hi⟩
  · intro hy
    let ik : RoomIndex n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
    rcases hy with ⟨hyFace, hyk_le, hprefix⟩
    let θ : ℝ := (k + 1 : ℝ) * y ik
    have hθ_nonneg : 0 ≤ θ := by
      dsimp [θ]
      have hyk_nonneg : 0 ≤ y ik := hyFace.1.1 ik
      positivity
    have hk1R : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hθ_le : θ ≤ 1 := by
      calc
        θ = (k + 1 : ℝ) * y ik := by rfl
        _ ≤ (k + 1 : ℝ) * ((k + 1 : ℝ)⁻¹) := by
          gcongr
        _ = 1 := by field_simp [hk1R]
    rw [prefixBarycenterSegment, segment_eq_image_lineMap ℝ
      (prefixBarycenter n k) (prefixBarycenter n (k + 1))]
    refine ⟨θ, ⟨hθ_nonneg, hθ_le⟩, ?_⟩
    ext i
    by_cases hi : i.1 < k
    · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
      have hk1R : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hyi : y i = (k : ℝ)⁻¹ - y ik / k := hprefix hi
      rw [hyi]
      simp [AffineMap.lineMap_apply_module, prefixBarycenter, hi,
        show i.1 < k + 1 by omega, θ]
      field_simp [hkR, hk1R]
      ring
    · by_cases hik : i = ik
      · subst hik
        simp [AffineMap.lineMap_apply_module, prefixBarycenter, ik, θ]
        field_simp [hk1R]
      · have hik_notin : i ∉ prefixRooms n (k + 1) := by
          rw [mem_prefixRooms_iff]
          by_contra hik_mem
          have : i.1 = k := by omega
          exact hik (Fin.ext this)
        have hyi_zero : y i = 0 := (coordSupport_subset_iff.mp hyFace.2) i hik_notin
        rw [hyi_zero]
        simp [AffineMap.lineMap_apply_module, prefixBarycenter, hi,
          show ¬ i.1 < k + 1 by simpa [mem_prefixRooms_iff] using hik_notin]

theorem eq_prefixBarycenter_of_mem_prefixBarycenterSegment_of_mem_ambientCoordinateFace
    {n k : ℕ} [NeZero k] (hk : k + 1 ≤ n) {y : RentCoordinates n}
    (hySeg : y ∈ prefixBarycenterSegment n k)
    (hyFace : y ∈ ambientCoordinateFace (prefixRooms n k)) :
    y = prefixBarycenter n k := by
  let ik : RoomIndex n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
  have hySeg' : y ∈ segment ℝ (prefixBarycenter n k) (prefixBarycenter n (k + 1)) := by
    simpa [prefixBarycenterSegment] using hySeg
  rw [segment_eq_image_lineMap ℝ (prefixBarycenter n k) (prefixBarycenter n (k + 1))] at hySeg'
  rcases hySeg' with ⟨θ, _hθ, rfl⟩
  have hik_notin : ik ∉ prefixRooms n k := by
    simp [ik, prefixRooms]
  have hcoord_zero :
      AffineMap.lineMap (prefixBarycenter n k) (prefixBarycenter n (k + 1)) θ ik = 0 := by
    exact (coordSupport_subset_iff.mp hyFace.2) ik hik_notin
  have hcoord_eq :
      AffineMap.lineMap (prefixBarycenter n k) (prefixBarycenter n (k + 1)) θ ik =
        θ * ((k + 1 : ℝ)⁻¹) := by
    simp [AffineMap.lineMap_apply_module, prefixBarycenter, ik]
  have htheta_zero' : θ * ((k + 1 : ℝ)⁻¹) = 0 := by
    rw [← hcoord_eq]
    exact hcoord_zero
  have htheta_zero : θ = 0 := by
    rcases mul_eq_zero.mp htheta_zero' with hθ | hinv
    · exact hθ
    · exfalso
      have hk1 : (↑k + 1 : ℝ) ≠ 0 := by
        positivity
      exact hk1 (inv_eq_zero.mp hinv)
  simp [htheta_zero]

theorem IsFaceRespecting.eq_prefixBarycenter_of_mem_coordinateFace_of_map_mem_prefixBarycenterSegment
    {n k : ℕ} [NeZero k] {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f)
    (hk : k + 1 ≤ n) {x : RentSimplex n}
    (hxFace : x ∈ coordinateFace (prefixRooms n k))
    (hfxSeg : f x ∈ prefixBarycenterSegment n k) :
    f x = prefixBarycenter n k := by
  apply eq_prefixBarycenter_of_mem_prefixBarycenterSegment_of_mem_ambientCoordinateFace hk hfxSeg
  exact hf.mapsTo_ambientCoordinateFace (prefixRooms n k) hxFace

/-- The first barycenter `b_1`, viewed as a simplex vertex, is the Section 5 start point. -/
def section5StartVertex (n : ℕ) [NeZero n] : RentSimplex n :=
  ⟨prefixBarycenter n 1, by
    simpa [RentSimplex, scaledSimplex] using
      (prefixBarycenter_mem_scaledSimplex (n := n) (k := 1) <|
        Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n)))⟩

/-- The singleton cell at the Section 5 starting vertex. -/
def section5StartCell (n : ℕ) [NeZero n] : SimplexFacet n where
  vertices := {section5StartVertex n}

theorem section5StartVertex_mem_coordinateFace (n : ℕ) [NeZero n] :
    section5StartVertex n ∈ coordinateFace (prefixRooms n 1) := by
  rw [mem_coordinateFace_iff]
  intro i hi
  have hi' : ¬ i.1 < 1 := by
    simpa [mem_prefixRooms_iff] using hi
  simp [section5StartVertex, prefixBarycenter, hi']

@[simp]
theorem section5StartCell_card (n : ℕ) [NeZero n] :
    (section5StartCell n).vertices.card = 1 := by
  simp [section5StartCell]

theorem section5StartVertex_eq_stdSimplex_vertex (n : ℕ) [NeZero n] :
    section5StartVertex n = stdSimplex.vertex (S := ℝ) (0 : RoomIndex n) := by
  apply eq_stdSimplex_vertex_of_apply_eq_one
  change prefixBarycenter n 1 (0 : RoomIndex n) = 1
  simp [prefixBarycenter]

theorem section5StartCell_isFace {n : ℕ} [NeZero n] (T : SimplexTriangulation n) :
    T.IsFace (section5StartCell n) := by
  obtain ⟨τ, hτ, hmem⟩ := T.covers_simplex (section5StartVertex n)
  refine ⟨τ, hτ, ?_⟩
  intro v hv
  have hv' : v = section5StartVertex n := by
    simpa [section5StartCell] using hv
  subst hv'
  have hmem' :
      ((stdSimplex.vertex (S := ℝ) (0 : RoomIndex n) : RentSimplex n) : RentCoordinates n) ∈
        τ.realization := by
    simpa [section5StartVertex_eq_stdSimplex_vertex (n := n)] using hmem
  have hvertex :
      stdSimplex.vertex (S := ℝ) (0 : RoomIndex n) ∈ τ.vertices := by
    exact τ.stdSimplexVertex_mem_vertices_of_mem_realization (i := (0 : RoomIndex n)) hmem'
  simpa [section5StartVertex_eq_stdSimplex_vertex (n := n)] using hvertex

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

theorem eq_section5StartVertex_of_mem_coordinateFace_prefixRooms_one {n : ℕ} [NeZero n]
    {v : RentSimplex n} (hv : v ∈ coordinateFace (prefixRooms n 1)) :
    v = section5StartVertex n := by
  apply Subtype.ext
  exact eq_prefixBarycenter_one_of_mem_ambientCoordinateFace
    (mem_ambientCoordinateFace_of_mem_coordinateFace hv)

theorem ambientCoordinateFace_prefixRooms_two_apply_eq_one_sub_apply_zero {n : ℕ} [NeZero n]
    {y : RentCoordinates n} (hy : y ∈ ambientCoordinateFace (prefixRooms n 2))
    {i : RoomIndex n} (hi : i.1 < 2) (h0 : i ≠ (0 : RoomIndex n)) :
    y i = 1 - y (0 : RoomIndex n) := by
  have hsum_split :
      (∑ k : RoomIndex n, y k) =
        y (0 : RoomIndex n) +
          Finset.sum (Finset.univ.erase (0 : RoomIndex n)) (fun k => y k) := by
    simpa using Finset.sum_eq_add_sum_diff_singleton
      (s := (Finset.univ : Finset (RoomIndex n))) (f := fun k => y k) (i := (0 : RoomIndex n))
      (Finset.mem_univ _)
  have hrest :
      Finset.sum (Finset.univ.erase (0 : RoomIndex n)) (fun k => y k) = y i := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro k hk hki
      have hk0 : k ≠ (0 : RoomIndex n) := (Finset.mem_erase.mp hk).1
      have hkge : 2 ≤ k.1 := by
        by_contra hkge
        have hklt : k.1 < 2 := Nat.lt_of_not_ge hkge
        have hi0' : i.1 ≠ 0 := by
          intro hi0'
          apply h0
          exact Fin.ext hi0'
        have hk0' : k.1 ≠ 0 := by
          intro hk0'
          apply hk0
          exact Fin.ext hk0'
        have hi1 : i.1 = 1 := by omega
        have hk1 : k.1 = 1 := by omega
        have : k = i := by
          apply Fin.ext
          omega
        exact hki this
      exact (coordSupport_subset_iff.mp hy.2) k (by simpa [mem_prefixRooms_iff] using hkge)
    · intro hi_not_mem
      exact False.elim <| hi_not_mem (by simp [h0])
  have hsum :
      y (0 : RoomIndex n) +
        Finset.sum (Finset.univ.erase (0 : RoomIndex n)) (fun k => y k) = 1 := by
    rw [← hsum_split, hy.1.2]
    norm_num
  rw [hrest] at hsum
  linarith

theorem eq_of_mem_ambientCoordinateFace_prefixRooms_two_of_apply_zero_eq {n : ℕ} [NeZero n]
    {x y : RentCoordinates n}
    (hx : x ∈ ambientCoordinateFace (prefixRooms n 2))
    (hy : y ∈ ambientCoordinateFace (prefixRooms n 2))
    (h0 : x (0 : RoomIndex n) = y (0 : RoomIndex n)) :
    x = y := by
  ext i
  by_cases hi0 : i = (0 : RoomIndex n)
  · simpa [hi0] using h0
  · by_cases hi : i.1 < 2
    · rw [ambientCoordinateFace_prefixRooms_two_apply_eq_one_sub_apply_zero hx hi hi0,
        ambientCoordinateFace_prefixRooms_two_apply_eq_one_sub_apply_zero hy hi hi0, h0]
    · have hxi : x i = 0 :=
        (coordSupport_subset_iff.mp hx.2) i (by simpa [mem_prefixRooms_iff] using hi)
      have hyi : y i = 0 :=
        (coordSupport_subset_iff.mp hy.2) i (by simpa [mem_prefixRooms_iff] using hi)
      rw [hxi, hyi]

theorem ambientCoordinateFace_prefixRooms_two_apply_zero_le_one {n : ℕ} [NeZero n]
    {y : RentCoordinates n} (hy : y ∈ ambientCoordinateFace (prefixRooms n 2)) :
    y (0 : RoomIndex n) ≤ 1 := by
  have hsum_split :
      (∑ k : RoomIndex n, y k) =
        y (0 : RoomIndex n) +
          Finset.sum (Finset.univ.erase (0 : RoomIndex n)) (fun k => y k) := by
    simpa using Finset.sum_eq_add_sum_diff_singleton
      (s := (Finset.univ : Finset (RoomIndex n))) (f := fun k => y k) (i := (0 : RoomIndex n))
      (Finset.mem_univ _)
  have hrest_nonneg :
      0 ≤ Finset.sum (Finset.univ.erase (0 : RoomIndex n)) (fun k => y k) := by
    exact Finset.sum_nonneg fun k _ => hy.1.1 k
  have hsum :
      y (0 : RoomIndex n) +
        Finset.sum (Finset.univ.erase (0 : RoomIndex n)) (fun k => y k) = 1 := by
    rw [← hsum_split, hy.1.2]
    norm_num
  linarith

theorem prefixBarycenter_one_mem_ambientCoordinateFace_two {n : ℕ} [NeZero n] :
    prefixBarycenter n 1 ∈ ambientCoordinateFace (prefixRooms n 2) := by
  have h1n : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
  exact ambientCoordinateFace_mono (prefixRooms_mono (by omega))
    (prefixBarycenter_mem_ambientCoordinateFace (n := n) (k := 1) h1n)

theorem ambientCoordinateFace_prefixRooms_two_apply_zero_lt_one_of_ne_start {n : ℕ} [NeZero n]
    {y : RentCoordinates n} (hy : y ∈ ambientCoordinateFace (prefixRooms n 2))
    (hne : y ≠ prefixBarycenter n 1) :
    y (0 : RoomIndex n) < 1 := by
  have hle : y (0 : RoomIndex n) ≤ 1 := ambientCoordinateFace_prefixRooms_two_apply_zero_le_one hy
  by_contra hlt
  have hy0 : y (0 : RoomIndex n) = 1 := by linarith
  apply hne
  exact eq_of_mem_ambientCoordinateFace_prefixRooms_two_of_apply_zero_eq hy
    prefixBarycenter_one_mem_ambientCoordinateFace_two (by simpa [prefixBarycenter] using hy0)

theorem mem_segment_prefixBarycenter_one_of_boundary_zero_order {n : ℕ} [NeZero n]
    {x y : RentCoordinates n} (hx : x ∈ ambientCoordinateFace (prefixRooms n 2))
    (hy : y ∈ ambientCoordinateFace (prefixRooms n 2)) (hy_ne : y ≠ prefixBarycenter n 1)
    (hxy : y (0 : RoomIndex n) ≤ x (0 : RoomIndex n)) :
    x ∈ segment ℝ (prefixBarycenter n 1) y := by
  let t : ℝ := (1 - x (0 : RoomIndex n)) / (1 - y (0 : RoomIndex n))
  have hy_lt_one :
      y (0 : RoomIndex n) < 1 :=
    ambientCoordinateFace_prefixRooms_two_apply_zero_lt_one_of_ne_start hy hy_ne
  have hy_den_pos : 0 < 1 - y (0 : RoomIndex n) := by linarith
  have ht_nonneg : 0 ≤ t := by
    have hx_le_one : x (0 : RoomIndex n) ≤ 1 :=
      ambientCoordinateFace_prefixRooms_two_apply_zero_le_one hx
    dsimp [t]
    exact div_nonneg (by linarith) (le_of_lt hy_den_pos)
  have ht_le_one : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one hy_den_pos).2 (by linarith)
  have hz_mem :
      AffineMap.lineMap (prefixBarycenter n 1) y t ∈ segment ℝ (prefixBarycenter n 1) y := by
    refine ⟨1 - t, t, sub_nonneg.mpr ht_le_one, ht_nonneg, by linarith, ?_⟩
    simp [AffineMap.lineMap_apply_module]
  have hz_face :
      AffineMap.lineMap (prefixBarycenter n 1) y t ∈ ambientCoordinateFace (prefixRooms n 2) := by
    exact (convex_ambientCoordinateFace (prefixRooms n 2)).segment_subset
      prefixBarycenter_one_mem_ambientCoordinateFace_two hy hz_mem
  have hz0 :
      AffineMap.lineMap (prefixBarycenter n 1) y t (0 : RoomIndex n) = x (0 : RoomIndex n) := by
    dsimp [t]
    simp [AffineMap.lineMap_apply_module, prefixBarycenter]
    field_simp [hy_den_pos.ne']
    ring
  have hxz :
      x = AffineMap.lineMap (prefixBarycenter n 1) y t := by
    exact eq_of_mem_ambientCoordinateFace_prefixRooms_two_of_apply_zero_eq hx hz_face hz0.symm
  rw [hxz]
  exact hz_mem

theorem mem_ambientCoordinateFace_prefixRooms_two_of_scaledSimplex_zero_off {n : ℕ} [NeZero n]
    {y : RentCoordinates n} (hy : y ∈ scaledSimplex 1 n)
    (hzero : ∀ i, i ∉ prefixRooms n 2 → y i = 0) :
    y ∈ ambientCoordinateFace (prefixRooms n 2) := by
  refine ⟨hy, ?_⟩
  rw [coordSupport_subset_iff]
  exact hzero

theorem mem_coordinateFace_of_mem_ambientCoordinateFace {n : ℕ} {I : Finset (RoomIndex n)}
    {v : RentSimplex n}
    (hv : ((v : RentSimplex n) : RentCoordinates n) ∈ ambientCoordinateFace I) :
    v ∈ coordinateFace I := by
  rw [mem_coordinateFace_iff]
  exact coordSupport_subset_iff.mp hv.2

theorem SimplexFacet.realization_subset_ambientCoordinateFace_of_vertices_mem_coordinateFace
    {n : ℕ} {τ : SimplexFacet n} {I : Finset (RoomIndex n)}
    (hverts : ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices → v ∈ coordinateFace I) :
    τ.realization ⊆ ambientCoordinateFace I := by
  rw [SimplexFacet.realization]
  refine convexHull_min ?_ (convex_ambientCoordinateFace I)
  rintro y ⟨v, hv, rfl⟩
  exact mem_ambientCoordinateFace_of_mem_coordinateFace (hverts hv)

theorem SimplexFacet.mem_coordinateFace_of_mem_realization_of_vertices_mem_coordinateFace
    {n : ℕ} {τ : SimplexFacet n} {I : Finset (RoomIndex n)} {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization)
    (hverts : ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices → v ∈ coordinateFace I) :
    x ∈ coordinateFace I := by
  exact mem_coordinateFace_of_mem_ambientCoordinateFace <|
    τ.realization_subset_ambientCoordinateFace_of_vertices_mem_coordinateFace hverts hxτ

theorem mem_coordinateFace_prefixRooms_two_of_mem_ambientCoordinateFace {n : ℕ} [NeZero n]
    {v : RentSimplex n}
    (hv : ((v : RentSimplex n) : RentCoordinates n) ∈ ambientCoordinateFace (prefixRooms n 2)) :
    v ∈ coordinateFace (prefixRooms n 2) := by
  exact mem_coordinateFace_of_mem_ambientCoordinateFace hv

theorem point_mem_ambientCoordinateFace_of_nonzero_weight {n : ℕ} {I : Finset (RoomIndex n)}
    {τ : SimplexFacet n} {x : RentCoordinates n}
    (_hxτ : x ∈ τ.realization) (hxFace : x ∈ ambientCoordinateFace I)
    {w : RentCoordinates n → ℝ}
    (hw_nonneg :
      ∀ y ∈ τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n),
        0 ≤ w y)
    (hw_sum :
      ∑ y ∈ τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n),
        w y = 1)
    (hw_center :
      (τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n)).centerMass
        w id = x)
    {y : RentCoordinates n}
    (hy : y ∈ τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n))
    (hwy : w y ≠ 0) :
    y ∈ ambientCoordinateFace I := by
  rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
  rw [mem_ambientCoordinateFace_iff]
  constructor
  · simpa [RentSimplex, scaledSimplex] using v.2
  · rw [coordSupport_subset_iff]
    intro i hi
    have hx_zero : x i = 0 := (coordSupport_subset_iff.mp hxFace.2) i hi
    have hsum_i :
        ∑ y ∈ τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n),
          w y * y i = x i := by
      calc
        ∑ y ∈ τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n),
            w y * y i
          = (∑ y ∈ τ.vertices.image fun v : RentSimplex n =>
                ((v : RentSimplex n) : RentCoordinates n), w y • y) i := by
              simp [Pi.smul_apply]
        _ = ((τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n)).centerMass
              w id) i := by
              rw [Finset.centerMass_eq_of_sum_1
                (τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) :
                  RentCoordinates n)) id hw_sum]
              rfl
        _ = x i := by
              exact congrArg (fun z : RentCoordinates n => z i) hw_center
    have hsum_zero :
        ∑ y ∈ τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n),
          w y * y i = 0 := by
      simpa [hx_zero] using hsum_i
    have hterms_zero :
        ∀ z ∈ τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n),
          w z * z i = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hsum_zero
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨u, hu, rfl⟩
      exact mul_nonneg (hw_nonneg _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)) (u.2.1 i)
    have hwi_zero :
        w (((v : RentSimplex n) : RentCoordinates n)) *
          ((v : RentSimplex n) : RentCoordinates n) i = 0 :=
      hterms_zero _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    exact (mul_eq_zero.mp hwi_zero).resolve_left hwy

/-- If a point of a facet lies on the boundary edge `conv(e₁,e₂)`, then any vertex with nonzero
weight in a convex-hull presentation of that point also lies on the same boundary edge. -/
theorem point_mem_ambientCoordinateFace_prefixRooms_two_of_nonzero_weight {n : ℕ} [NeZero n]
    {τ : SimplexFacet n} {x : RentCoordinates n}
    (hxτ : x ∈ τ.realization) (hxFace : x ∈ ambientCoordinateFace (prefixRooms n 2))
    {w : RentCoordinates n → ℝ}
    (hw_nonneg :
      ∀ y ∈ τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n),
        0 ≤ w y)
    (hw_sum :
      ∑ y ∈ τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n),
        w y = 1)
    (hw_center :
      (τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n)).centerMass
        w id = x)
    {y : RentCoordinates n}
    (hy : y ∈ τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n))
    (hwy : w y ≠ 0) :
    y ∈ ambientCoordinateFace (prefixRooms n 2) := by
  exact point_mem_ambientCoordinateFace_of_nonzero_weight hxτ hxFace hw_nonneg hw_sum hw_center
    hy hwy

theorem mem_erase_realization_of_mem_realization_of_mem_coordinateFace_of_not_mem_coordinateFace
    {n : ℕ} {I : Finset (RoomIndex n)} {τ : SimplexFacet n}
    {x : RentSimplex n} {v : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization)
    (hxFace : x ∈ coordinateFace I)
    (hv : v ∈ τ.vertices)
    (hvFace : v ∉ coordinateFace I) :
    ((x : RentSimplex n) : RentCoordinates n) ∈
      (⟨τ.vertices.erase v⟩ : SimplexFacet n).realization := by
  classical
  let s : Finset (RentCoordinates n) :=
    τ.vertices.image fun u : RentSimplex n => ((u : RentSimplex n) : RentCoordinates n)
  have hxconv :
      ((x : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ (s : Set (RentCoordinates n)) := by
    simpa [s, SimplexFacet.realization, SimplexFacet.pointSet] using hxτ
  obtain ⟨w, hw_nonneg, hw_sum, hw_center⟩ := (Finset.mem_convexHull).mp hxconv
  let supp : Finset (RentCoordinates n) := s.filter fun y => w y ≠ 0
  have hxFace' :
      ((x : RentSimplex n) : RentCoordinates n) ∈ ambientCoordinateFace I :=
    mem_ambientCoordinateFace_of_mem_coordinateFace hxFace
  have hvw_zero : w (((v : RentSimplex n) : RentCoordinates n)) = 0 := by
    by_contra hvw_ne
    have hvFace' :
        ((v : RentSimplex n) : RentCoordinates n) ∈ ambientCoordinateFace I :=
      point_mem_ambientCoordinateFace_of_nonzero_weight hxτ hxFace' hw_nonneg hw_sum hw_center
        (Finset.mem_image.mpr ⟨v, hv, rfl⟩) hvw_ne
    exact hvFace (mem_coordinateFace_of_mem_ambientCoordinateFace hvFace')
  have hsupp_sum : ∑ y ∈ supp, w y = 1 := by
    calc
      ∑ y ∈ supp, w y = ∑ y ∈ s, w y := by
        simpa [supp] using (Finset.sum_filter_ne_zero (s := s) (f := w))
      _ = 1 := hw_sum
  have hsupp_center :
      supp.centerMass w id = ((x : RentSimplex n) : RentCoordinates n) := by
    calc
      supp.centerMass w id = s.centerMass w id := by
        simpa [supp] using (Finset.centerMass_filter_ne_zero (t := s) (w := w) (z := id))
      _ = ((x : RentSimplex n) : RentCoordinates n) := hw_center
  have hsupp_conv :
      ((x : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ (supp : Set (RentCoordinates n)) := by
    rw [← hsupp_center]
    refine Finset.centerMass_id_mem_convexHull supp ?_ ?_
    · intro y hy
      exact hw_nonneg _ (Finset.mem_filter.mp hy).1
    · rw [hsupp_sum]
      norm_num
  have hsupp_subset :
      (supp : Set (RentCoordinates n)) ⊆ (⟨τ.vertices.erase v⟩ : SimplexFacet n).pointSet := by
    intro y hy
    rcases Finset.mem_image.mp (Finset.mem_filter.mp hy).1 with ⟨u, hu, rfl⟩
    have hwu_ne_zero :
        w (((u : RentSimplex n) : RentCoordinates n)) ≠ 0 := (Finset.mem_filter.mp hy).2
    have huv_ne : u ≠ v := by
      intro huv
      subst huv
      exact hwu_ne_zero hvw_zero
    exact Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n)
      (Finset.mem_erase.mpr ⟨huv_ne, hu⟩)
  rw [SimplexFacet.realization]
  exact convexHull_mono hsupp_subset hsupp_conv

theorem exists_boundaryEdgeVertex_ne_start {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (T : SimplexTriangulation n) :
    ∃ v ∈ T.vertices, v ∈ coordinateFace (prefixRooms n 2) ∧ v ≠ section5StartVertex n := by
  classical
  let x : RentSimplex n := ⟨prefixBarycenter n 2, by
    simpa [RentSimplex, scaledSimplex] using
      prefixBarycenter_mem_scaledSimplex (n := n) (k := 2) hn⟩
  obtain ⟨τ, hτ, hxτ⟩ := T.covers_simplex x
  let s : Finset (RentCoordinates n) :=
    τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n)
  have hxconv : ((x : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ (s : Set (RentCoordinates n)) := by
    simpa [s, SimplexFacet.realization, SimplexFacet.pointSet] using hxτ
  obtain ⟨w, hw_nonneg, hw_sum, hw_center⟩ := (Finset.mem_convexHull).mp hxconv
  let supp : Finset (RentCoordinates n) := s.filter fun y => w y ≠ 0
  have hsupp_sum : ∑ y ∈ supp, w y = 1 := by
    calc
      ∑ y ∈ supp, w y = ∑ y ∈ s, w y := by
        simpa [supp] using (Finset.sum_filter_ne_zero (s := s) (f := w))
      _ = 1 := hw_sum
  have hsupp_nonempty : supp.Nonempty := by
    by_contra hsupp
    have : (∑ y ∈ supp, w y) = 0 := by
      simp [Finset.not_nonempty_iff_eq_empty.mp hsupp]
    linarith
  have hsupp_center :
      supp.centerMass w id = ((x : RentSimplex n) : RentCoordinates n) := by
    calc
      supp.centerMass w id = s.centerMass w id := by
        simpa [supp] using (Finset.centerMass_filter_ne_zero (t := s) (w := w) (z := id))
      _ = ((x : RentSimplex n) : RentCoordinates n) := hw_center
  have hsupp_conv :
      ((x : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ (supp : Set (RentCoordinates n)) := by
    rw [← hsupp_center]
    refine Finset.centerMass_id_mem_convexHull supp ?_ ?_
    · intro y hy
      exact hw_nonneg _ (Finset.mem_filter.mp hy).1
    · rw [hsupp_sum]
      norm_num
  have hsupp_boundary :
      ∀ y ∈ supp, y ∈ ambientCoordinateFace (prefixRooms n 2) := by
    intro y hy
    exact point_mem_ambientCoordinateFace_prefixRooms_two_of_nonzero_weight hxτ
      (prefixBarycenter_mem_ambientCoordinateFace (n := n) (k := 2) hn)
      hw_nonneg hw_sum hw_center (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2
  have hex_nonstart :
      ∃ y ∈ supp, y ≠ prefixBarycenter n 1 := by
    by_contra hno
    have hsupp_subset :
        (supp : Set (RentCoordinates n)) ⊆ {prefixBarycenter n 1} := by
      intro y hy
      simp
      by_contra hy_ne
      exact hno ⟨y, hy, hy_ne⟩
    have hx_eq_start : ((x : RentSimplex n) : RentCoordinates n) = prefixBarycenter n 1 := by
      have hx_singleton :
          ((x : RentSimplex n) : RentCoordinates n) ∈
            convexHull ℝ ({prefixBarycenter n 1} : Set (RentCoordinates n)) :=
        convexHull_mono hsupp_subset hsupp_conv
      simpa [convexHull_singleton] using hx_singleton
    have : prefixBarycenter n 2 = prefixBarycenter n 1 := by simpa using hx_eq_start
    have hcoord := congrArg (fun z : RentCoordinates n => z (0 : RoomIndex n)) this
    simp [prefixBarycenter] at hcoord
  rcases hex_nonstart with ⟨y, hy_supp, hy_ne⟩
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hy_supp).1 with ⟨v, hvτ, rfl⟩
  refine ⟨v, ?_, ?_, ?_⟩
  · simpa [SimplexTriangulation.vertices] using Finset.mem_biUnion.mpr ⟨τ, hτ, hvτ⟩
  · exact mem_coordinateFace_prefixRooms_two_of_mem_ambientCoordinateFace
      (hsupp_boundary _ hy_supp)
  · intro hv_eq
    apply hy_ne
    rw [hv_eq]
    rfl

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

theorem IsFaceRespecting.exists_targetFacet_of_eq_one
    {T : SimplexTriangulation 1} {f : SelfMapOnRentSimplex 1} (hf : IsFaceRespecting f)
    {y : RentCoordinates 1} (hy : IsInteriorSimplexPoint y) :
    ∃ τ ∈ T.facets, FacetImageContains f τ y := by
  have hfacet : section5StartCell 1 ∈ T.facets := by
    refine SimplexTriangulation.mem_facets_of_isFace_of_card (T := T) (section5StartCell_isFace T) ?_
    simpa using section5StartCell_card 1
  have hy_face : y ∈ ambientCoordinateFace (prefixRooms 1 1) := by
    simpa [prefixRooms_self] using (interiorPoint_mem_ambientCoordinateFace_iff hy).2 rfl
  have hy_eq : y = prefixBarycenter 1 1 :=
    eq_prefixBarycenter_one_of_mem_ambientCoordinateFace hy_face
  refine ⟨section5StartCell 1, hfacet, ?_⟩
  simpa [hy_eq] using (hf.startCell_hits_prefixBarycenter (n := 1))

theorem IsFaceRespecting.exists_barycenter_targetFacet_of_eq_one
    {T : SimplexTriangulation 1} {f : SelfMapOnRentSimplex 1} (hf : IsFaceRespecting f) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter 1 : RentSimplex 1) : RentCoordinates 1) := by
  simpa [prefixBarycenter_self_eq_rentBarycenter] using
    (hf.exists_targetFacet_of_eq_one (y := ((rentBarycenter 1 : RentSimplex 1) : RentCoordinates 1))
      (rentBarycenter_isInteriorSimplexPoint 1))

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

theorem IsPiecewiseAffineOn.exists_point_in_cell_realization_of_graphNode {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u) :
    ∃ x : RentSimplex n, ((x : RentSimplex n) : RentCoordinates n) ∈ u.cell.realization ∧
      f x ∈ prefixBarycenterSegment n u.level := by
  rcases hu.meets_chain with ⟨y, hyHull, hySeg⟩
  rcases hfpl.exists_point_in_realization_of_facetImageContains hu.isFace hyHull with
    ⟨x, hx, hfx⟩
  refine ⟨x, hx, ?_⟩
  simpa [hfx] using hySeg

/-- The actual preimage slice of the current barycenter segment inside one Section 5 cell. -/
def section5CellSlice {n : ℕ} (u : Section5Node n) (f : SelfMapOnRentSimplex n) :
    Set (RentSimplex n) :=
  {x | ((x : RentSimplex n) : RentCoordinates n) ∈ u.cell.realization ∧
    f x ∈ prefixBarycenterSegment n u.level}

@[simp]
theorem mem_section5CellSlice_iff {n : ℕ} {u : Section5Node n} {f : SelfMapOnRentSimplex n}
    {x : RentSimplex n} :
    x ∈ section5CellSlice u f ↔
      ((x : RentSimplex n) : RentCoordinates n) ∈ u.cell.realization ∧
        f x ∈ prefixBarycenterSegment n u.level :=
  Iff.rfl

theorem IsPiecewiseAffineOn.exists_mem_section5CellSlice_of_graphNode {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u) :
    ∃ x : RentSimplex n, x ∈ section5CellSlice u f := by
  rcases hfpl.exists_point_in_cell_realization_of_graphNode hu with ⟨x, hx, hfx⟩
  exact ⟨x, hx, hfx⟩

theorem IsFaceRespecting.section5StartNode_isGraphNode {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f) :
    IsSection5GraphNode T f (section5StartNode n) := by
  refine ⟨Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n)), section5StartCell_isFace T,
    section5StartCell_card n, ?_, ?_⟩
  · intro v hv
    have hv' : v = section5StartVertex n := by
      simpa [section5StartCell] using hv
    subst hv'
    exact section5StartVertex_mem_coordinateFace n
  · refine ⟨prefixBarycenter n 1, hf.startCell_hits_prefixBarycenter, ?_⟩
    simpa [prefixBarycenterSegment] using
      right_mem_segment ℝ (prefixBarycenter n 0) (prefixBarycenter n 1)

theorem IsSection5GraphNode.level_eq_card_pred {n : ℕ} {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n} {u : Section5Node n} (hu : IsSection5GraphNode T f u) :
    u.level = u.cell.vertices.card - 1 := by
  rw [hu.card_eq]
  omega

/-- The nonempty subfaces of one Section 5 cell whose image still meets the current barycenter
segment. -/
def section5SegmentSubfaces {n : ℕ} (u : Section5Node n) (f : SelfMapOnRentSimplex n) :
    Finset (SimplexFacet n) := by
  classical
  exact ((u.cell.vertices.powerset.filter fun s =>
      s.Nonempty ∧ (FacetImageHull f (⟨s⟩ : SimplexFacet n) ∩ prefixBarycenterSegment n u.level).Nonempty)
    ).image fun s => (⟨s⟩ : SimplexFacet n)

theorem mem_section5SegmentSubfaces_iff {n : ℕ} {u : Section5Node n} {f : SelfMapOnRentSimplex n}
    {τ : SimplexFacet n} :
    τ ∈ section5SegmentSubfaces u f ↔
      τ.IsSubfaceOf u.cell ∧ τ.vertices.Nonempty ∧
        (FacetImageHull f τ ∩ prefixBarycenterSegment n u.level).Nonempty := by
  classical
  constructor
  · intro hτ
    rcases Finset.mem_image.mp hτ with ⟨s, hs, hs_eq⟩
    have hs_vertices : s = τ.vertices := by
      simpa using congrArg SimplexFacet.vertices hs_eq
    subst hs_vertices
    refine ⟨(Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1), ?_, ?_⟩
    · exact (Finset.mem_filter.mp hs).2.1
    · exact (Finset.mem_filter.mp hs).2.2
  · rintro ⟨hτsub, hτne, hτhit⟩
    refine Finset.mem_image.mpr ⟨τ.vertices, ?_, by rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hτsub, hτne, hτhit⟩

theorem section5SegmentSubfaces_nonempty {n : ℕ} {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n} {u : Section5Node n} (hu : IsSection5GraphNode T f u) :
    (section5SegmentSubfaces u f).Nonempty := by
  classical
  refine ⟨u.cell, ?_⟩
  exact (mem_section5SegmentSubfaces_iff (u := u) (f := f) (τ := u.cell)).mpr
    ⟨Finset.Subset.refl _, hu.cell_nonempty, hu.meets_chain⟩

theorem exists_minimal_section5SegmentSubface {n : ℕ} {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n} {u : Section5Node n} (hu : IsSection5GraphNode T f u) :
    ∃ τ ∈ section5SegmentSubfaces u f,
      ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card := by
  classical
  exact Finset.exists_min_image (section5SegmentSubfaces u f) (fun τ => τ.vertices.card)
    (section5SegmentSubfaces_nonempty hu)

/-- Local lower-boundary data for one Section 5 cell: a minimal segment-hitting subface whose
vertices already lie in the lower prefix face and whose cardinality is exactly codimension one. -/
structure Section5MinimalSliceFaceData {n : ℕ} (u : Section5Node n)
    (f : SelfMapOnRentSimplex n) where
  face : SimplexFacet n
  mem_segmentSubfaces : face ∈ section5SegmentSubfaces u f
  minimal :
    ∀ σ ∈ section5SegmentSubfaces u f, face.vertices.card ≤ σ.vertices.card
  card_eq : face.vertices.card = u.level
  lower_prefix_vertices :
    ∀ ⦃w : RentSimplex n⦄, w ∈ face.vertices → w ∈ coordinateFace (prefixRooms n u.level)

theorem Section5MinimalSliceFaceData.face_isSubface {n : ℕ} {u : Section5Node n}
    {f : SelfMapOnRentSimplex n} (hdata : Section5MinimalSliceFaceData u f) :
    hdata.face.IsSubfaceOf u.cell :=
  (mem_section5SegmentSubfaces_iff
    (u := u) (f := f) (τ := hdata.face)).mp hdata.mem_segmentSubfaces |>.1

theorem IsPiecewiseAffineOn.exists_point_in_realization_of_mem_section5SegmentSubfaces
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    {τ : SimplexFacet n} (hτ : τ ∈ section5SegmentSubfaces u f) :
    ∃ x : RentSimplex n, ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization ∧
      f x ∈ prefixBarycenterSegment n u.level := by
  rcases (mem_section5SegmentSubfaces_iff (u := u) (f := f) (τ := τ)).mp hτ with
    ⟨hτsub, _hτne, hτhit⟩
  have hτface : T.IsFace τ := by
    rcases hu.isFace with ⟨σ, hσ, hσsub⟩
    exact ⟨σ, hσ, hτsub.trans hσsub⟩
  rcases hτhit with ⟨y, hyHull, hySeg⟩
  rcases hfpl.exists_point_in_realization_of_facetImageContains hτface hyHull with
    ⟨x, hx, hfx⟩
  refine ⟨x, hx, ?_⟩
  simpa [hfx] using hySeg

/-- The slice of one subface against the Section 5 barycenter segment, expressed in one affine
chart on that subface. -/
def section5SubfaceSliceSet {n : ℕ} (u : Section5Node n) (τ : SimplexFacet n)
    (g : RentCoordinates n →ᵃ[ℝ] RentCoordinates n) : Set (RentCoordinates n) :=
  τ.realization ∩ g ⁻¹' prefixBarycenterSegment n u.level

theorem isCompact_section5SubfaceSliceSet {n : ℕ} (u : Section5Node n) (τ : SimplexFacet n)
    (g : RentCoordinates n →ᵃ[ℝ] RentCoordinates n) :
    IsCompact (section5SubfaceSliceSet u τ g) := by
  unfold section5SubfaceSliceSet
  refine τ.isCompact_realization.inter_right ?_
  have hg : Continuous g := g.continuous_of_finiteDimensional
  exact (isCompact_prefixBarycenterSegment (n := n) (k := u.level)).isClosed.preimage hg

theorem IsPiecewiseAffineOn.section5SubfaceSliceSet_nonempty
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    {τ : SimplexFacet n} (hτ : τ ∈ section5SegmentSubfaces u f)
    {g : RentCoordinates n →ᵃ[ℝ] RentCoordinates n}
    (hg : ∀ x : RentSimplex n,
      ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization → g x = f x) :
    (section5SubfaceSliceSet u τ g).Nonempty := by
  rcases hfpl.exists_point_in_realization_of_mem_section5SegmentSubfaces hu hτ with
    ⟨x, hxτ, hfxSeg⟩
  refine ⟨(x : RentCoordinates n), hxτ, ?_⟩
  simpa [hg x hxτ] using hfxSeg

theorem exists_isMinOn_outsideMass_section5SubfaceSliceSet {n : ℕ} (u : Section5Node n)
    (τ : SimplexFacet n) (g : RentCoordinates n →ᵃ[ℝ] RentCoordinates n)
    (hne : (section5SubfaceSliceSet u τ g).Nonempty) :
    ∃ y ∈ section5SubfaceSliceSet u τ g,
      IsMinOn (outsideMass (prefixRooms n u.level)) (section5SubfaceSliceSet u τ g) y := by
  exact (isCompact_section5SubfaceSliceSet u τ g).exists_isMinOn
    hne continuous_outsideMass.continuousOn

theorem IsPiecewiseAffineOn.exists_outsideMass_minimizer_on_section5SegmentSubface
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    {τ : SimplexFacet n} (hτ : τ ∈ section5SegmentSubfaces u f) :
    ∃ g : RentCoordinates n →ᵃ[ℝ] RentCoordinates n,
      (∀ x : RentSimplex n,
        ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization → g x = f x) ∧
      ∃ y ∈ section5SubfaceSliceSet u τ g,
        IsMinOn (outsideMass (prefixRooms n u.level)) (section5SubfaceSliceSet u τ g) y := by
  have hτface : T.IsFace τ := by
    rcases (mem_section5SegmentSubfaces_iff (u := u) (f := f) (τ := τ)).mp hτ with
      ⟨hτsub, _, _⟩
    rcases hu.isFace with ⟨σ, hσ, hσsub⟩
    exact ⟨σ, hσ, hτsub.trans hσsub⟩
  rcases hfpl.exists_affineMap_on_face hτface with ⟨g, hg⟩
  refine ⟨g, hg, ?_⟩
  exact exists_isMinOn_outsideMass_section5SubfaceSliceSet u τ g
    (hfpl.section5SubfaceSliceSet_nonempty hu hτ hg)

theorem Section5MinimalSliceFaceData.exists_point_mem_slice {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hdata : Section5MinimalSliceFaceData u f) :
    ∃ x : RentSimplex n,
      x ∈ section5CellSlice u f ∧
        ((x : RentSimplex n) : RentCoordinates n) ∈ hdata.face.realization := by
  rcases IsPiecewiseAffineOn.exists_point_in_realization_of_mem_section5SegmentSubfaces
      hfpl hu hdata.mem_segmentSubfaces with ⟨x, hxface, hfxSeg⟩
  have hxcell :
      ((x : RentSimplex n) : RentCoordinates n) ∈ u.cell.realization :=
    SimplexFacet.realization_mono_of_isSubface hdata.face_isSubface hxface
  exact ⟨x, ⟨hxcell, hfxSeg⟩, hxface⟩

theorem Section5MinimalSliceFaceData.exists_point_mem_slice_and_mem_coordinateFace {n : ℕ}
    [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hdata : Section5MinimalSliceFaceData u f) :
    ∃ x : RentSimplex n,
      x ∈ section5CellSlice u f ∧ x ∈ coordinateFace (prefixRooms n u.level) := by
  rcases hdata.exists_point_mem_slice hfpl hu with ⟨x, hxSlice, hxface⟩
  refine ⟨x, hxSlice, ?_⟩
  exact hdata.face.mem_coordinateFace_of_mem_realization_of_vertices_mem_coordinateFace
    hxface hdata.lower_prefix_vertices

theorem mem_section5SegmentSubfaces_of_mem_realization_map_segment {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    {τ : SimplexFacet n} (hτsub : τ.IsSubfaceOf u.cell) (hτne : τ.vertices.Nonempty)
    {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization)
    (hfxSeg : f x ∈ prefixBarycenterSegment n u.level) :
    τ ∈ section5SegmentSubfaces u f := by
  have hτface : T.IsFace τ := by
    rcases hu.isFace with ⟨σ, hσ, hσsub⟩
    exact ⟨σ, hσ, hτsub.trans hσsub⟩
  have hτhit : (FacetImageHull f τ ∩ prefixBarycenterSegment n u.level).Nonempty := by
    refine ⟨f x, hfpl.facetImageContains_of_mem_realization hτface hxτ, hfxSeg⟩
  exact (mem_section5SegmentSubfaces_iff (u := u) (f := f) (τ := τ)).mpr
    ⟨hτsub, hτne, hτhit⟩

/-- Exact local theorem still missing from the manuscript's quoted genericity sentence: every
minimal segment-hitting face meets the barycenter segment through a codimension-one lower face
lying in the lower prefix face. -/
def Section5MinimalSubfaceLowerBoundaryGenericity {n : ℕ} (u : Section5Node n)
    (f : SelfMapOnRentSimplex n) : Prop :=
  ∀ {τ : SimplexFacet n},
    τ ∈ section5SegmentSubfaces u f →
    (∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card) →
      ∃ (ρ : SimplexFacet n) (x : RentSimplex n),
        ρ.IsSubfaceOf τ ∧
          ρ.vertices.card = u.level ∧
          (∀ ⦃w : RentSimplex n⦄,
            w ∈ ρ.vertices → w ∈ coordinateFace (prefixRooms n u.level)) ∧
          ((x : RentSimplex n) : RentCoordinates n) ∈ ρ.realization ∧
          f x ∈ prefixBarycenterSegment n u.level

/-- Exact local support-layer data for the paper's remaining genericity sentence on one cell:
a minimal segment-hitting face `τ` has a codimension-one lower face carrying a point whose image
still lies on the barycenter segment. The existing Section 5 support API can already upgrade this
package to genuine slice geometry. -/
structure Section5MinimalSliceLowerBoundaryFaceData {n : ℕ} (u : Section5Node n)
    (f : SelfMapOnRentSimplex n) where
  minimal_face : SimplexFacet n
  mem_segmentSubfaces : minimal_face ∈ section5SegmentSubfaces u f
  minimal :
    ∀ σ ∈ section5SegmentSubfaces u f, minimal_face.vertices.card ≤ σ.vertices.card
  lower_boundary_face : SimplexFacet n
  lower_boundary_isSubface : lower_boundary_face.IsSubfaceOf minimal_face
  lower_boundary_card_eq : lower_boundary_face.vertices.card = u.level
  lower_boundary_prefix_vertices :
    ∀ ⦃w : RentSimplex n⦄,
      w ∈ lower_boundary_face.vertices → w ∈ coordinateFace (prefixRooms n u.level)
  lower_boundary_point : RentSimplex n
  lower_boundary_point_mem_realization :
    ((lower_boundary_point : RentSimplex n) : RentCoordinates n) ∈ lower_boundary_face.realization
  lower_boundary_point_map_mem_segment :
    f lower_boundary_point ∈ prefixBarycenterSegment n u.level

def Section5MinimalSubfaceLowerBoundaryGenericity.toLowerBoundaryFaceData
    {n : ℕ} {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hu : IsSection5GraphNode T f u)
    (hgeneric : Section5MinimalSubfaceLowerBoundaryGenericity u f) :
    Section5MinimalSliceLowerBoundaryFaceData u f := by
  classical
  let hminExists := exists_minimal_section5SegmentSubface hu
  let τ : SimplexFacet n := Classical.choose hminExists
  have hτ : τ ∈ section5SegmentSubfaces u f := (Classical.choose_spec hminExists).1
  have hmin : ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card :=
    (Classical.choose_spec hminExists).2
  let hboundary := hgeneric hτ hmin
  let ρ : SimplexFacet n := Classical.choose hboundary
  let hxExists := Classical.choose_spec hboundary
  let x : RentSimplex n := Classical.choose hxExists
  have hxSpec := Classical.choose_spec hxExists
  have hρsub : ρ.IsSubfaceOf τ := hxSpec.1
  have hρrest := hxSpec.2
  have hρcard : ρ.vertices.card = u.level := hρrest.1
  have hρrest' := hρrest.2
  have hρface :
      ∀ ⦃w : RentSimplex n⦄,
        w ∈ ρ.vertices → w ∈ coordinateFace (prefixRooms n u.level) :=
    hρrest'.1
  have hxρ : ((x : RentSimplex n) : RentCoordinates n) ∈ ρ.realization := hρrest'.2.1
  have hfxSeg : f x ∈ prefixBarycenterSegment n u.level := hρrest'.2.2
  exact ⟨τ, hτ, hmin, ρ, hρsub, hρcard, hρface, x, hxρ, hfxSeg⟩

/-- A first local boundary-geometry package for one minimal segment-hitting face `τ`: a lower
codimension-one boundary face carries an actual point of the slice. Minimality then forces `τ`
itself to be that lower face. -/
structure Section5MinimalSliceLowerBoundaryGeometry {n : ℕ} (u : Section5Node n)
    (f : SelfMapOnRentSimplex n) where
  minimal_face : SimplexFacet n
  mem_segmentSubfaces : minimal_face ∈ section5SegmentSubfaces u f
  minimal :
    ∀ σ ∈ section5SegmentSubfaces u f, minimal_face.vertices.card ≤ σ.vertices.card
  lower_boundary_face : SimplexFacet n
  lower_boundary_isSubface : lower_boundary_face.IsSubfaceOf minimal_face
  lower_boundary_card_eq : lower_boundary_face.vertices.card = u.level
  lower_boundary_prefix_vertices :
    ∀ ⦃w : RentSimplex n⦄,
      w ∈ lower_boundary_face.vertices → w ∈ coordinateFace (prefixRooms n u.level)
  lower_boundary_point : RentSimplex n
  lower_boundary_point_mem_slice : lower_boundary_point ∈ section5CellSlice u f
  lower_boundary_point_mem_realization :
    ((lower_boundary_point : RentSimplex n) : RentCoordinates n) ∈ lower_boundary_face.realization

def Section5MinimalSliceLowerBoundaryGeometry.toMinimalSliceFaceData
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    (hulevel : 0 < u.level) (hgeom : Section5MinimalSliceLowerBoundaryGeometry u f) :
    Section5MinimalSliceFaceData u f := by
  have hρcard_pos : 0 < hgeom.lower_boundary_face.vertices.card := by
    rw [hgeom.lower_boundary_card_eq]
    exact hulevel
  have hρne : hgeom.lower_boundary_face.vertices.Nonempty := Finset.card_pos.mp hρcard_pos
  have hτsubu : hgeom.minimal_face.IsSubfaceOf u.cell :=
    (mem_section5SegmentSubfaces_iff
      (u := u) (f := f) (τ := hgeom.minimal_face)).mp hgeom.mem_segmentSubfaces |>.1
  have hρsubu : hgeom.lower_boundary_face.IsSubfaceOf u.cell :=
    hgeom.lower_boundary_isSubface.trans hτsubu
  have hρmem : hgeom.lower_boundary_face ∈ section5SegmentSubfaces u f :=
    mem_section5SegmentSubfaces_of_mem_realization_map_segment
      hfpl hu hρsubu hρne
      hgeom.lower_boundary_point_mem_realization
      hgeom.lower_boundary_point_mem_slice.2
  have hτcard_le : hgeom.minimal_face.vertices.card ≤ hgeom.lower_boundary_face.vertices.card :=
    hgeom.minimal _ hρmem
  have hρcard_le : hgeom.lower_boundary_face.vertices.card ≤ hgeom.minimal_face.vertices.card :=
    Finset.card_le_card hgeom.lower_boundary_isSubface
  have hcard_eq : hgeom.minimal_face.vertices.card = u.level := by
    have hfaces_card_eq :
        hgeom.minimal_face.vertices.card = hgeom.lower_boundary_face.vertices.card :=
      le_antisymm hτcard_le hρcard_le
    rw [hfaces_card_eq, hgeom.lower_boundary_card_eq]
  have hverts_eq :
      hgeom.lower_boundary_face.vertices = hgeom.minimal_face.vertices := by
    refine Finset.eq_of_subset_of_card_le hgeom.lower_boundary_isSubface ?_
    exact hτcard_le
  refine ⟨hgeom.minimal_face, hgeom.mem_segmentSubfaces, hgeom.minimal, hcard_eq, ?_⟩
  intro w hw
  have hwρ : w ∈ hgeom.lower_boundary_face.vertices := by
    simpa [hverts_eq] using hw
  exact hgeom.lower_boundary_prefix_vertices hwρ

theorem IsPiecewiseAffineOn.exists_point_with_nonzero_weights_of_minimal_section5SegmentSubface
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    {τ : SimplexFacet n} (hτ : τ ∈ section5SegmentSubfaces u f)
    (hmin : ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card) :
    ∃ x : RentSimplex n, ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization ∧
      f x ∈ prefixBarycenterSegment n u.level ∧
      ∃ w : RentCoordinates n → ℝ,
        (∀ y ∈ τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n),
          0 ≤ w y) ∧
        (∑ y ∈ τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n),
          w y = 1) ∧
        ((τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n)).centerMass
          w id = ((x : RentSimplex n) : RentCoordinates n)) ∧
        (∀ y ∈ τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n),
          w y ≠ 0) := by
  classical
  rcases hfpl.exists_point_in_realization_of_mem_section5SegmentSubfaces hu hτ with
    ⟨x, hxτ, hfxSeg⟩
  let s : Finset (RentCoordinates n) :=
    τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n)
  have hxconv : ((x : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ (s : Set (RentCoordinates n)) := by
    simpa [s, SimplexFacet.realization, SimplexFacet.pointSet] using hxτ
  obtain ⟨w, hw_nonneg, hw_sum, hw_center⟩ := (Finset.mem_convexHull).mp hxconv
  let σ : SimplexFacet n := ⟨τ.vertices.filter fun v => w ((v : RentSimplex n) : RentCoordinates n) ≠ 0⟩
  have hσsubτ : σ.IsSubfaceOf τ := by
    intro v hv
    exact (Finset.mem_filter.mp hv).1
  have hσreal :
      ((x : RentSimplex n) : RentCoordinates n) ∈ σ.realization := by
    let supp : Finset (RentCoordinates n) := s.filter fun y => w y ≠ 0
    have hsupp_sum : ∑ y ∈ supp, w y = 1 := by
      calc
        ∑ y ∈ supp, w y = ∑ y ∈ s, w y := by
          simpa [supp] using (Finset.sum_filter_ne_zero (s := s) (f := w))
        _ = 1 := hw_sum
    have hsupp_center :
        supp.centerMass w id = ((x : RentSimplex n) : RentCoordinates n) := by
      calc
        supp.centerMass w id = s.centerMass w id := by
          simpa [supp] using (Finset.centerMass_filter_ne_zero (t := s) (w := w) (z := id))
        _ = ((x : RentSimplex n) : RentCoordinates n) := hw_center
    have hsupp_conv :
        ((x : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ (supp : Set (RentCoordinates n)) := by
      rw [← hsupp_center]
      refine Finset.centerMass_id_mem_convexHull supp ?_ ?_
      · intro y hy
        exact hw_nonneg _ (Finset.mem_filter.mp hy).1
      · rw [hsupp_sum]
        norm_num
    have hsupp_subset : (supp : Set (RentCoordinates n)) ⊆ σ.pointSet := by
      intro y hy
      rcases Finset.mem_image.mp (Finset.mem_filter.mp hy).1 with ⟨v, hv, rfl⟩
      exact Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n)
        (Finset.mem_filter.mpr ⟨hv, (Finset.mem_filter.mp hy).2⟩)
    exact convexHull_mono hsupp_subset hsupp_conv
  have hτsubu : τ.IsSubfaceOf u.cell :=
    (mem_section5SegmentSubfaces_iff (u := u) (f := f) (τ := τ)).mp hτ |>.1
  have hσsubu : σ.IsSubfaceOf u.cell := hσsubτ.trans hτsubu
  have hσface : T.IsFace σ := by
    rcases hu.isFace with ⟨ρ, hρ, hρsub⟩
    exact ⟨ρ, hρ, hσsubu.trans hρsub⟩
  have hσhit :
      (FacetImageHull f σ ∩ prefixBarycenterSegment n u.level).Nonempty := by
    refine ⟨f x, hfpl.facetImageContains_of_mem_realization hσface hσreal, hfxSeg⟩
  have hσmem : σ ∈ section5SegmentSubfaces u f := by
    exact (mem_section5SegmentSubfaces_iff (u := u) (f := f) (τ := σ)).mpr
      ⟨hσsubu, by
        have : 0 < ∑ y ∈ s, w y := by simpa [hw_sum]
        have hnonempty : (σ.vertices).Nonempty := by
          by_contra hσempty
          have hsupp_empty : (s.filter fun y => w y ≠ 0) = ∅ := by
            ext y
            constructor
            · intro hy
              rcases Finset.mem_image.mp (Finset.mem_filter.mp hy).1 with ⟨v, hv, rfl⟩
              have hvσ : v ∈ σ.vertices := Finset.mem_filter.mpr ⟨hv, (Finset.mem_filter.mp hy).2⟩
              exact False.elim (hσempty ⟨v, hvσ⟩)
            · intro hy
              exact False.elim (by simpa using hy)
          have : ∑ y ∈ s, w y = 0 := by
            rw [← Finset.sum_filter_ne_zero (s := s) (f := w), hsupp_empty]
            simp
          linarith
        exact hnonempty, hσhit⟩
  have hcard_min : τ.vertices.card ≤ σ.vertices.card := hmin σ hσmem
  have hcard_le : σ.vertices.card ≤ τ.vertices.card := Finset.card_le_card hσsubτ
  have hcard_eq : σ.vertices.card = τ.vertices.card := le_antisymm hcard_le hcard_min
  refine ⟨x, hxτ, hfxSeg, w, hw_nonneg, hw_sum, hw_center, ?_⟩
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
  by_contra hzero
  have hv_notinσ : v ∉ σ.vertices := by
    intro hvσ
    exact (Finset.mem_filter.mp hvσ).2 hzero
  have hproper : σ.vertices ⊂ τ.vertices := by
    refine ⟨hσsubτ, ?_⟩
    intro hτσ
    exact hv_notinσ (hτσ hv)
  have : σ.vertices.card < τ.vertices.card := Finset.card_lt_card hproper
  omega

theorem Finset.centerMass_eq_lineMap_centerMass_erase_of_mem
    {ι : Type*} [DecidableEq ι] {n : ℕ} {t : Finset ι} {w : ι → ℝ}
    {z : ι → RentCoordinates n} {i : ι}
    (hi : i ∈ t) (hw_sum : ∑ j ∈ t, w j = 1) (hwi : w i ≠ 1) :
    t.centerMass w z =
      AffineMap.lineMap ((t.erase i).centerMass (fun j => w j / (1 - w i)) z) (z i) (w i) := by
  have hden : 1 - w i ≠ 0 := sub_ne_zero.mpr hwi.symm
  have hsum_erase : ∑ j ∈ t.erase i, w j = 1 - w i := by
    have hsum_erase_add := Finset.sum_erase_add (s := t) (f := w) hi
    linarith
  have hnorm_sum : ∑ j ∈ t.erase i, w j / (1 - w i) = 1 := by
    calc
      ∑ j ∈ t.erase i, w j / (1 - w i)
          = (∑ j ∈ t.erase i, w j) / (1 - w i) := by
              simp_rw [div_eq_mul_inv]
              rw [Finset.sum_mul]
      _ = 1 := by
          rw [hsum_erase]
          field_simp [hden]
  have hsplit : ∑ j ∈ t, w j • z j = ∑ j ∈ t.erase i, w j • z j + w i • z i := by
    simpa [add_comm] using
      (Finset.sum_erase_add (s := t) (f := fun j => w j • z j) hi).symm
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw_sum, Finset.centerMass_eq_of_sum_1 _ _ hnorm_sum,
    AffineMap.lineMap_apply_module]
  calc
    ∑ j ∈ t, w j • z j = ∑ j ∈ t.erase i, w j • z j + w i • z i := hsplit
    _ = (1 - w i) • ∑ j ∈ t.erase i, (w j / (1 - w i)) • z j + w i • z i := by
            rw [Finset.smul_sum]
            congr 1
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hcoef : (1 - w i) * (w j / (1 - w i)) = w j := by
              field_simp [hden]
            rw [smul_smul, hcoef]

theorem IsPiecewiseAffineOn.exists_erased_face_point_of_minimal_section5SegmentSubface
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    {τ : SimplexFacet n} (hτ : τ ∈ section5SegmentSubfaces u f)
    (hmin : ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card)
    {v : RentSimplex n} (hv : v ∈ τ.vertices) (hcard : 1 < τ.vertices.card) :
    ∃ x x' : RentSimplex n, ∃ c : ℝ,
      ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization ∧
      f x ∈ prefixBarycenterSegment n u.level ∧
      ((x' : RentSimplex n) : RentCoordinates n) ∈ (⟨τ.vertices.erase v⟩ : SimplexFacet n).realization ∧
      0 < c ∧ c < 1 ∧
      ((x : RentSimplex n) : RentCoordinates n) =
        AffineMap.lineMap (((x' : RentSimplex n) : RentCoordinates n))
          (((v : RentSimplex n) : RentCoordinates n)) c ∧
      f x = AffineMap.lineMap (f x') (f v) c := by
  classical
  obtain ⟨x, hxτ, hfxSeg, w, hw_nonneg, hw_sum, hw_center, hw_nz⟩ :=
    hfpl.exists_point_with_nonzero_weights_of_minimal_section5SegmentSubface hu hτ hmin
  let s : Finset (RentCoordinates n) :=
    τ.vertices.image fun u : RentSimplex n => ((u : RentSimplex n) : RentCoordinates n)
  let yv : RentCoordinates n := ((v : RentSimplex n) : RentCoordinates n)
  have hyv_mem : yv ∈ s := by
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  have hyv_ne_zero : w yv ≠ 0 := hw_nz _ hyv_mem
  have hyv_pos : 0 < w yv := by
    exact lt_of_le_of_ne (hw_nonneg _ hyv_mem) (by simpa using hyv_ne_zero.symm)
  have hs_card : s.card = τ.vertices.card := by
    dsimp [s]
    simpa using
      Finset.card_image_of_injective τ.vertices
        (fun a b hab => Subtype.ext hab)
  have hyv_ne_one : w yv ≠ 1 := by
    intro hyv_one
    have hsum_erase_zero : ∑ y ∈ s.erase yv, w y = 0 := by
      have hsum_erase_add := Finset.sum_erase_add (s := s) (f := w) hyv_mem
      linarith
    have hzero_erase : ∀ y ∈ s.erase yv, w y = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (by
          intro y hy
          exact hw_nonneg _ (Finset.mem_of_mem_erase hy))).mp hsum_erase_zero
    have herase_card : 0 < (s.erase yv).card := by
      rw [Finset.card_erase_of_mem hyv_mem]
      omega
    rcases Finset.card_pos.mp herase_card with ⟨y, hy⟩
    exact (hw_nz _ (Finset.mem_of_mem_erase hy)) (hzero_erase _ hy)
  have hyv_le_one : w yv ≤ 1 := by
    have hsum_erase_nonneg : 0 ≤ ∑ y ∈ s.erase yv, w y := by
      exact Finset.sum_nonneg (by
        intro y hy
        exact hw_nonneg _ (Finset.mem_of_mem_erase hy))
    have hsum_erase_add := Finset.sum_erase_add (s := s) (f := w) hyv_mem
    linarith
  have hyv_lt_one : w yv < 1 := by
    exact lt_of_le_of_ne hyv_le_one hyv_ne_one
  have hden_pos : 0 < 1 - w yv := sub_pos.mpr hyv_lt_one
  let x'coord : RentCoordinates n :=
    (s.erase yv).centerMass (fun y => w y / (1 - w yv)) id
  have hnorm_sum : ∑ y ∈ s.erase yv, w y / (1 - w yv) = 1 := by
    have hsum_erase : ∑ y ∈ s.erase yv, w y = 1 - w yv := by
      have hsum_erase_add := Finset.sum_erase_add (s := s) (f := w) hyv_mem
      linarith
    calc
      ∑ y ∈ s.erase yv, w y / (1 - w yv)
          = (∑ y ∈ s.erase yv, w y) / (1 - w yv) := by
              simp_rw [div_eq_mul_inv]
              rw [Finset.sum_mul]
      _ = 1 := by
          rw [hsum_erase]
          field_simp [ne_of_gt hden_pos]
  have hx'conv :
      x'coord ∈ convexHull ℝ ((s.erase yv : Finset (RentCoordinates n)) : Set (RentCoordinates n)) := by
    have hnorm_pos : 0 < ∑ y ∈ s.erase yv, w y / (1 - w yv) := by
      rw [hnorm_sum]
      norm_num
    exact Finset.centerMass_id_mem_convexHull
      (t := s.erase yv)
      (w := fun y => w y / (1 - w yv))
      (by
        intro y hy
        exact div_nonneg (hw_nonneg _ (Finset.mem_of_mem_erase hy)) (le_of_lt hden_pos))
      hnorm_pos
  have hs_erase :
      (τ.vertices.erase v).image
          (fun u : RentSimplex n => ((u : RentSimplex n) : RentCoordinates n)) =
        s.erase yv := by
    simpa [s, yv] using
      (Finset.image_erase
        (s := τ.vertices) (a := v)
        (f := fun u : RentSimplex n => ((u : RentSimplex n) : RentCoordinates n))
        (fun a b hab => Subtype.ext hab))
  have hs_erase_set :
      (((↑) : RentSimplex n → RentCoordinates n) '' ((τ.vertices.erase v : Finset (RentSimplex n)) :
        Set (RentSimplex n))) = ((s.erase yv : Finset (RentCoordinates n)) : Set (RentCoordinates n)) := by
    simpa [Finset.coe_image] using
      congrArg (fun t : Finset (RentCoordinates n) => (t : Set (RentCoordinates n))) hs_erase
  have hx'erase :
      x'coord ∈ (⟨τ.vertices.erase v⟩ : SimplexFacet n).realization := by
    rw [SimplexFacet.realization, SimplexFacet.pointSet, hs_erase_set]
    exact hx'conv
  let x' : RentSimplex n := ⟨x'coord, by
    simpa [RentSimplex, scaledSimplex] using
      (⟨τ.vertices.erase v⟩ : SimplexFacet n).realization_subset_scaledSimplex hx'erase⟩
  have hx'_real : ((x' : RentSimplex n) : RentCoordinates n) ∈
      (⟨τ.vertices.erase v⟩ : SimplexFacet n).realization := hx'erase
  have hx_line :
      ((x : RentSimplex n) : RentCoordinates n) =
        AffineMap.lineMap (((x' : RentSimplex n) : RentCoordinates n))
          (((v : RentSimplex n) : RentCoordinates n)) (w yv) := by
    calc
      ((x : RentSimplex n) : RentCoordinates n) = s.centerMass w id := by
        symm
        exact hw_center
      _ = AffineMap.lineMap ((s.erase yv).centerMass (fun y => w y / (1 - w yv)) id) yv (w yv) := by
        exact Finset.centerMass_eq_lineMap_centerMass_erase_of_mem hyv_mem hw_sum hyv_ne_one
      _ = AffineMap.lineMap (((x' : RentSimplex n) : RentCoordinates n))
            (((v : RentSimplex n) : RentCoordinates n)) (w yv) := by
        rfl
  have hτsubu : τ.IsSubfaceOf u.cell :=
    (mem_section5SegmentSubfaces_iff (u := u) (f := f) (τ := τ)).mp hτ |>.1
  have herase_subτ : (⟨τ.vertices.erase v⟩ : SimplexFacet n).IsSubfaceOf τ := by
    intro w hw
    exact Finset.mem_of_mem_erase hw
  have hxcell : ((x : RentSimplex n) : RentCoordinates n) ∈ u.cell.realization :=
    SimplexFacet.realization_mono_of_isSubface hτsubu hxτ
  have hx'cell : ((x' : RentSimplex n) : RentCoordinates n) ∈ u.cell.realization :=
    SimplexFacet.realization_mono_of_isSubface (herase_subτ.trans hτsubu) hx'_real
  have hvτreal : ((v : RentSimplex n) : RentCoordinates n) ∈ τ.realization := by
    rw [SimplexFacet.realization]
    exact subset_convexHull ℝ _ <|
      Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n) hv
  have hvcell : ((v : RentSimplex n) : RentCoordinates n) ∈ u.cell.realization :=
    SimplexFacet.realization_mono_of_isSubface hτsubu hvτreal
  rcases hu.isFace with ⟨ρ, hρ, hu_subρ⟩
  rcases hfpl ρ hρ with ⟨g, hg⟩
  have hxρ : ((x : RentSimplex n) : RentCoordinates n) ∈ ρ.realization :=
    SimplexFacet.realization_mono_of_isSubface hu_subρ hxcell
  have hx'ρ : ((x' : RentSimplex n) : RentCoordinates n) ∈ ρ.realization :=
    SimplexFacet.realization_mono_of_isSubface hu_subρ hx'cell
  have hvρ : ((v : RentSimplex n) : RentCoordinates n) ∈ ρ.realization :=
    SimplexFacet.realization_mono_of_isSubface hu_subρ hvcell
  have hfx : f x = g x := (hg x hxρ).symm
  have hfx' : f x' = g x' := (hg x' hx'ρ).symm
  have hfv : f v = g v := (hg v hvρ).symm
  refine ⟨x, x', w yv, hxτ, hfxSeg, hx'_real, hyv_pos, hyv_lt_one, hx_line, ?_⟩
  calc
    f x = g x := hfx
    _ = g (AffineMap.lineMap (((x' : RentSimplex n) : RentCoordinates n))
          (((v : RentSimplex n) : RentCoordinates n)) (w yv)) := by
            simpa [hx_line]
    _ = AffineMap.lineMap (g x') (g v) (w yv) := by
          rw [AffineMap.apply_lineMap]
    _ = AffineMap.lineMap (f x') (f v) (w yv) := by
          simp [hfx', hfv]

theorem minimal_section5SegmentSubface_erase_not_mem
    {n : ℕ} {f : SelfMapOnRentSimplex n} {u : Section5Node n} {τ : SimplexFacet n}
    (hmin : ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card)
    {v : RentSimplex n} (hv : v ∈ τ.vertices) :
    (⟨τ.vertices.erase v⟩ : SimplexFacet n) ∉ section5SegmentSubfaces u f := by
  intro hσ
  have hcard_min : τ.vertices.card ≤ (⟨τ.vertices.erase v⟩ : SimplexFacet n).vertices.card :=
    hmin _ hσ
  have hcard_lt : (⟨τ.vertices.erase v⟩ : SimplexFacet n).vertices.card < τ.vertices.card := by
    simpa using Finset.card_erase_lt_of_mem hv
  omega

theorem minimal_section5SegmentSubface_vertices_mem_coordinateFace_of_erase_mem
    {n : ℕ} {f : SelfMapOnRentSimplex n} {u : Section5Node n} {τ : SimplexFacet n}
    (hmin : ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card)
    (herase :
      ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices →
        v ∉ coordinateFace (prefixRooms n u.level) →
          (⟨τ.vertices.erase v⟩ : SimplexFacet n) ∈ section5SegmentSubfaces u f) :
    ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices → v ∈ coordinateFace (prefixRooms n u.level) := by
  intro v hv
  by_contra hvFace
  exact minimal_section5SegmentSubface_erase_not_mem hmin hv (herase hv hvFace)

theorem minimal_section5SegmentSubface_vertices_mem_coordinateFace_of_erase_realization_map_segment
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    {τ : SimplexFacet n} (hτ : τ ∈ section5SegmentSubfaces u f)
    (hmin : ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card)
    (herase :
      ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices →
        v ∉ coordinateFace (prefixRooms n u.level) →
          ∃ x : RentSimplex n,
            ((x : RentSimplex n) : RentCoordinates n) ∈
              (⟨τ.vertices.erase v⟩ : SimplexFacet n).realization ∧
            f x ∈ prefixBarycenterSegment n u.level) :
    ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices → v ∈ coordinateFace (prefixRooms n u.level) := by
  apply minimal_section5SegmentSubface_vertices_mem_coordinateFace_of_erase_mem hmin
  intro v hv hvFace
  rcases herase hv hvFace with ⟨x, hxerase, hfxSeg⟩
  have hτsubu : τ.IsSubfaceOf u.cell :=
    (mem_section5SegmentSubfaces_iff (u := u) (f := f) (τ := τ)).mp hτ |>.1
  have herase_subτ : (⟨τ.vertices.erase v⟩ : SimplexFacet n).IsSubfaceOf τ := by
    intro w hw
    exact Finset.mem_of_mem_erase hw
  have herase_ne : (⟨τ.vertices.erase v⟩ : SimplexFacet n).vertices.Nonempty := by
    by_contra herase_empty
    have hverts_empty :
        (⟨τ.vertices.erase v⟩ : SimplexFacet n).vertices = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp herase_empty
    have hset_empty : ((τ.vertices : Set (RentSimplex n)) \ {v}) = ∅ := by
      simpa [Finset.coe_erase] using
        congrArg (fun s : Finset (RentSimplex n) => (s : Set (RentSimplex n))) hverts_empty
    have himage_empty :
        DFunLike.coe '' (((τ.vertices : Set (RentSimplex n)) \ {v}) : Set (RentSimplex n)) =
          (∅ : Set (RentCoordinates n)) := by
      rw [hset_empty, Set.image_empty]
    have : False := by
      simpa [SimplexFacet.realization, SimplexFacet.pointSet, himage_empty, convexHull_empty]
        using hxerase
    exact this
  exact mem_section5SegmentSubfaces_of_mem_realization_map_segment
    hfpl hu (herase_subτ.trans hτsubu) herase_ne hxerase hfxSeg

theorem minimal_section5SegmentSubface_vertices_mem_coordinateFace_of_erase_same_image
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    {τ : SimplexFacet n} (hτ : τ ∈ section5SegmentSubfaces u f)
    (hmin : ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card)
    {x : RentSimplex n}
    (hfxSeg : f x ∈ prefixBarycenterSegment n u.level)
    (herase :
      ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices →
        v ∉ coordinateFace (prefixRooms n u.level) →
          ∃ x' : RentSimplex n,
            ((x' : RentSimplex n) : RentCoordinates n) ∈
              (⟨τ.vertices.erase v⟩ : SimplexFacet n).realization ∧
            f x' = f x) :
    ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices → v ∈ coordinateFace (prefixRooms n u.level) := by
  apply minimal_section5SegmentSubface_vertices_mem_coordinateFace_of_erase_realization_map_segment
    hfpl hu hτ hmin
  intro v hv hvFace
  rcases herase hv hvFace with ⟨x', hx'erase, hx'eq⟩
  refine ⟨x', hx'erase, ?_⟩
  simpa [hx'eq] using hfxSeg

theorem minimal_section5SegmentSubface_mem_coordinateFace_of_erase_same_image
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    {τ : SimplexFacet n} (hτ : τ ∈ section5SegmentSubfaces u f)
    (hmin : ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card)
    {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization)
    (hfxSeg : f x ∈ prefixBarycenterSegment n u.level)
    (herase :
      ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices →
        v ∉ coordinateFace (prefixRooms n u.level) →
          ∃ x' : RentSimplex n,
            ((x' : RentSimplex n) : RentCoordinates n) ∈
              (⟨τ.vertices.erase v⟩ : SimplexFacet n).realization ∧
            f x' = f x) :
    x ∈ coordinateFace (prefixRooms n u.level) := by
  exact τ.mem_coordinateFace_of_mem_realization_of_vertices_mem_coordinateFace hxτ
    (minimal_section5SegmentSubface_vertices_mem_coordinateFace_of_erase_same_image
      hfpl hu hτ hmin hfxSeg herase)

theorem IsPiecewiseAffineOn.minimal_section5SegmentSubface_mem_coordinateFace_of_erase_same_chartImage
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    {τ : SimplexFacet n} (hτ : τ ∈ section5SegmentSubfaces u f)
    (hmin : ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card)
    {g : RentCoordinates n →ᵃ[ℝ] RentCoordinates n}
    (hg : ∀ x : RentSimplex n,
      ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization → g x = f x)
    {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization)
    (hgxSeg : g x ∈ prefixBarycenterSegment n u.level)
    (herase :
      ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices →
        v ∉ coordinateFace (prefixRooms n u.level) →
          ∃ x' : RentSimplex n,
            ((x' : RentSimplex n) : RentCoordinates n) ∈
              (⟨τ.vertices.erase v⟩ : SimplexFacet n).realization ∧
            g x' = g x) :
    x ∈ coordinateFace (prefixRooms n u.level) := by
  apply minimal_section5SegmentSubface_mem_coordinateFace_of_erase_same_image
    hfpl hu hτ hmin hxτ
  · simpa [hg x hxτ] using hgxSeg
  · intro v hv hvFace
    rcases herase hv hvFace with ⟨x', hx'erase, hx'eq⟩
    refine ⟨x', hx'erase, ?_⟩
    have hx'τ : ((x' : RentSimplex n) : RentCoordinates n) ∈ τ.realization :=
      SimplexFacet.realization_mono_of_isSubface
        (by intro w hw; exact Finset.mem_of_mem_erase hw) hx'erase
    rw [← hg x' hx'τ, ← hg x hxτ]
    exact hx'eq

theorem minimal_section5SegmentSubface_erase_realization_map_segment_of_mem_coordinateFace_point
    {n : ℕ} {f : SelfMapOnRentSimplex n} {u : Section5Node n} {τ : SimplexFacet n}
    {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization)
    (hxFace : x ∈ coordinateFace (prefixRooms n u.level))
    (hfxSeg : f x ∈ prefixBarycenterSegment n u.level) :
    ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices →
      v ∉ coordinateFace (prefixRooms n u.level) →
        ∃ x' : RentSimplex n,
          ((x' : RentSimplex n) : RentCoordinates n) ∈
            (⟨τ.vertices.erase v⟩ : SimplexFacet n).realization ∧
          f x' ∈ prefixBarycenterSegment n u.level := by
  intro v hv hvFace
  refine ⟨x, ?_, hfxSeg⟩
  exact mem_erase_realization_of_mem_realization_of_mem_coordinateFace_of_not_mem_coordinateFace
    hxτ hxFace hv hvFace

theorem minimal_section5SegmentSubface_vertices_mem_coordinateFace_of_mem_coordinateFace_point
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    {τ : SimplexFacet n} (hτ : τ ∈ section5SegmentSubfaces u f)
    (hmin : ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card)
    {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization)
    (hxFace : x ∈ coordinateFace (prefixRooms n u.level))
    (hfxSeg : f x ∈ prefixBarycenterSegment n u.level) :
    ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices → v ∈ coordinateFace (prefixRooms n u.level) := by
  exact minimal_section5SegmentSubface_vertices_mem_coordinateFace_of_erase_realization_map_segment
    hfpl hu hτ hmin
    (minimal_section5SegmentSubface_erase_realization_map_segment_of_mem_coordinateFace_point
      hxτ hxFace hfxSeg)

theorem minimal_section5SegmentSubface_exists_mem_coordinateFace_point_of_vertices_mem_coordinateFace
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    {τ : SimplexFacet n} (hτ : τ ∈ section5SegmentSubfaces u f)
    (hτface :
      ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices → v ∈ coordinateFace (prefixRooms n u.level)) :
    ∃ x : RentSimplex n,
      ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization ∧
      x ∈ coordinateFace (prefixRooms n u.level) ∧
      f x ∈ prefixBarycenterSegment n u.level := by
  rcases hfpl.exists_point_in_realization_of_mem_section5SegmentSubfaces hu hτ with
    ⟨x, hxτ, hfxSeg⟩
  refine ⟨x, hxτ, ?_, hfxSeg⟩
  exact τ.mem_coordinateFace_of_mem_realization_of_vertices_mem_coordinateFace hxτ hτface

def minimal_section5SegmentSubface_lowerBoundaryGeometry_of_card_eq_of_erase_realization_map_segment
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    {τ : SimplexFacet n} (hτ : τ ∈ section5SegmentSubfaces u f)
    (hmin : ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card)
    (hτcard : τ.vertices.card = u.level)
    (herase :
      ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices →
        v ∉ coordinateFace (prefixRooms n u.level) →
          ∃ x : RentSimplex n,
            ((x : RentSimplex n) : RentCoordinates n) ∈
              (⟨τ.vertices.erase v⟩ : SimplexFacet n).realization ∧
            f x ∈ prefixBarycenterSegment n u.level) :
    Section5MinimalSliceLowerBoundaryGeometry u f := by
  classical
  let hx :=
    hfpl.exists_point_in_realization_of_mem_section5SegmentSubfaces hu hτ
  let x : RentSimplex n := Classical.choose hx
  have hxspec := Classical.choose_spec hx
  have hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization := hxspec.1
  have hfxSeg : f x ∈ prefixBarycenterSegment n u.level := hxspec.2
  have hτsubu : τ.IsSubfaceOf u.cell :=
    (mem_section5SegmentSubfaces_iff (u := u) (f := f) (τ := τ)).mp hτ |>.1
  have hτface :
      ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices → v ∈ coordinateFace (prefixRooms n u.level) :=
    minimal_section5SegmentSubface_vertices_mem_coordinateFace_of_erase_realization_map_segment
      hfpl hu hτ hmin herase
  refine
    ⟨τ, hτ, hmin, τ, Finset.Subset.refl _, hτcard, hτface, x, ?_, hxτ⟩
  exact ⟨SimplexFacet.realization_mono_of_isSubface hτsubu hxτ, hfxSeg⟩

def minimal_section5SegmentSubface_lowerBoundaryGeometry_of_card_eq_of_mem_coordinateFace_point
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    {τ : SimplexFacet n} (hτ : τ ∈ section5SegmentSubfaces u f)
    (hmin : ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card)
    (hτcard : τ.vertices.card = u.level)
    {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization)
    (hxFace : x ∈ coordinateFace (prefixRooms n u.level))
    (hfxSeg : f x ∈ prefixBarycenterSegment n u.level) :
    Section5MinimalSliceLowerBoundaryGeometry u f := by
  exact minimal_section5SegmentSubface_lowerBoundaryGeometry_of_card_eq_of_erase_realization_map_segment
    hfpl hu hτ hmin hτcard
    (minimal_section5SegmentSubface_erase_realization_map_segment_of_mem_coordinateFace_point
      hxτ hxFace hfxSeg)

def minimal_section5SegmentSubface_lowerBoundaryGeometry_of_card_eq_of_vertices_mem_coordinateFace
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    {τ : SimplexFacet n} (hτ : τ ∈ section5SegmentSubfaces u f)
    (hmin : ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card)
    (hτcard : τ.vertices.card = u.level)
    (hτface :
      ∀ ⦃v : RentSimplex n⦄, v ∈ τ.vertices → v ∈ coordinateFace (prefixRooms n u.level)) :
    Section5MinimalSliceLowerBoundaryGeometry u f := by
  classical
  let hx :=
    minimal_section5SegmentSubface_exists_mem_coordinateFace_point_of_vertices_mem_coordinateFace
      hfpl hu hτ hτface
  let x : RentSimplex n := Classical.choose hx
  have hxspec := Classical.choose_spec hx
  have hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization := hxspec.1
  have hxFace : x ∈ coordinateFace (prefixRooms n u.level) := hxspec.2.1
  have hfxSeg : f x ∈ prefixBarycenterSegment n u.level := hxspec.2.2
  exact minimal_section5SegmentSubface_lowerBoundaryGeometry_of_card_eq_of_mem_coordinateFace_point
    hfpl hu hτ hmin hτcard hxτ hxFace hfxSeg

theorem minimal_section5SegmentSubface_card_eq_and_vertices_mem_coordinateFace_of_lower_boundary_face
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    (hulevel : 0 < u.level)
    {τ ρ : SimplexFacet n}
    (hτ : τ ∈ section5SegmentSubfaces u f)
    (hmin : ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card)
    (hρsub : ρ.IsSubfaceOf τ)
    (hρcard : ρ.vertices.card = u.level)
    (hρface :
      ∀ ⦃w : RentSimplex n⦄, w ∈ ρ.vertices → w ∈ coordinateFace (prefixRooms n u.level))
    {x : RentSimplex n}
    (hxρ : ((x : RentSimplex n) : RentCoordinates n) ∈ ρ.realization)
    (hfxSeg : f x ∈ prefixBarycenterSegment n u.level) :
    τ.vertices.card = u.level ∧
      (∀ ⦃w : RentSimplex n⦄, w ∈ τ.vertices → w ∈ coordinateFace (prefixRooms n u.level)) := by
  have hτsubu : τ.IsSubfaceOf u.cell :=
    (mem_section5SegmentSubfaces_iff (u := u) (f := f) (τ := τ)).mp hτ |>.1
  have hρsubu : ρ.IsSubfaceOf u.cell := hρsub.trans hτsubu
  have hρne : ρ.vertices.Nonempty := by
    have hρcard_pos : 0 < ρ.vertices.card := by
      rw [hρcard]
      exact hulevel
    exact Finset.card_pos.mp hρcard_pos
  have hρmem : ρ ∈ section5SegmentSubfaces u f :=
    mem_section5SegmentSubfaces_of_mem_realization_map_segment hfpl hu hρsubu hρne hxρ hfxSeg
  have hτcard_le : τ.vertices.card ≤ ρ.vertices.card := hmin _ hρmem
  have hρcard_le : ρ.vertices.card ≤ τ.vertices.card := Finset.card_le_card hρsub
  have hcard_eq : τ.vertices.card = u.level := by
    have hfaces_card_eq : τ.vertices.card = ρ.vertices.card := le_antisymm hτcard_le hρcard_le
    rw [hfaces_card_eq, hρcard]
  have hverts_eq : ρ.vertices = τ.vertices := by
    exact Finset.eq_of_subset_of_card_le hρsub hτcard_le
  refine ⟨hcard_eq, ?_⟩
  intro w hw
  have hwρ : w ∈ ρ.vertices := by
    simpa [hverts_eq] using hw
  exact hρface hwρ

def minimal_section5SegmentSubface_lowerBoundaryGeometry_of_lower_boundary_face
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    (hulevel : 0 < u.level)
    {τ ρ : SimplexFacet n}
    (hτ : τ ∈ section5SegmentSubfaces u f)
    (hmin : ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card)
    (hρsub : ρ.IsSubfaceOf τ)
    (hρcard : ρ.vertices.card = u.level)
    (hρface :
      ∀ ⦃w : RentSimplex n⦄, w ∈ ρ.vertices → w ∈ coordinateFace (prefixRooms n u.level))
    {x : RentSimplex n}
    (hxρ : ((x : RentSimplex n) : RentCoordinates n) ∈ ρ.realization)
    (hfxSeg : f x ∈ prefixBarycenterSegment n u.level) :
    Section5MinimalSliceLowerBoundaryGeometry u f := by
  obtain ⟨hτcard, hτface⟩ :=
    minimal_section5SegmentSubface_card_eq_and_vertices_mem_coordinateFace_of_lower_boundary_face
      hfpl hu hulevel hτ hmin hρsub hρcard hρface hxρ hfxSeg
  exact minimal_section5SegmentSubface_lowerBoundaryGeometry_of_card_eq_of_vertices_mem_coordinateFace
    hfpl hu hτ hmin hτcard hτface

def Section5MinimalSliceLowerBoundaryFaceData.toLowerBoundaryGeometry
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    (hulevel : 0 < u.level) (hdata : Section5MinimalSliceLowerBoundaryFaceData u f) :
    Section5MinimalSliceLowerBoundaryGeometry u f := by
  exact minimal_section5SegmentSubface_lowerBoundaryGeometry_of_lower_boundary_face
    hfpl hu hulevel hdata.mem_segmentSubfaces hdata.minimal
    hdata.lower_boundary_isSubface hdata.lower_boundary_card_eq
    hdata.lower_boundary_prefix_vertices hdata.lower_boundary_point_mem_realization
    hdata.lower_boundary_point_map_mem_segment

def Section5MinimalSubfaceLowerBoundaryGenericity.toLowerBoundaryGeometry
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    (hulevel : 0 < u.level)
    (hgeneric : Section5MinimalSubfaceLowerBoundaryGenericity u f) :
    Section5MinimalSliceLowerBoundaryGeometry u f := by
  exact (hgeneric.toLowerBoundaryFaceData hu).toLowerBoundaryGeometry hfpl hu hulevel

theorem IsSection5GraphNode.vertex_mem_affineSpan_prefixVertexPoints {n : ℕ}
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) {v : RentSimplex n} (hv : v ∈ u.cell.vertices) :
    ((v : RentSimplex n) : RentCoordinates n) ∈
      affineSpan ℝ ((prefixVertexPoints n (u.level + 1) : Finset (RentCoordinates n)) :
        Set (RentCoordinates n)) := by
  exact mem_affineSpan_prefixVertexPoints_of_mem_coordinateFace (hu.prefix_vertices hv)

def section5FacetLowerPrefixVertices {n : ℕ} (u : Section5Node n)
    (τ : SimplexFacet n) : Finset (RentSimplex n) := by
  classical
  exact τ.vertices.filter fun v => v ∈ coordinateFace (prefixRooms n u.level)

theorem section5FacetLowerPrefixVertices_isSubface {n : ℕ} (u : Section5Node n)
    (τ : SimplexFacet n) :
    (⟨section5FacetLowerPrefixVertices u τ⟩ : SimplexFacet n).IsSubfaceOf τ := by
  classical
  intro v hv
  exact (Finset.mem_filter.mp hv).1

theorem mem_realization_section5FacetLowerPrefixVertices_of_mem_realization_of_mem_coordinateFace
    {n : ℕ} {u : Section5Node n} {τ : SimplexFacet n} {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization)
    (hxFace : x ∈ coordinateFace (prefixRooms n u.level)) :
    ((x : RentSimplex n) : RentCoordinates n) ∈
      (⟨section5FacetLowerPrefixVertices u τ⟩ : SimplexFacet n).realization := by
  classical
  let s : Finset (RentCoordinates n) :=
    τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n)
  have hxconv :
      ((x : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ (s : Set (RentCoordinates n)) := by
    simpa [s, SimplexFacet.realization, SimplexFacet.pointSet] using hxτ
  obtain ⟨w, hw_nonneg, hw_sum, hw_center⟩ := (Finset.mem_convexHull).mp hxconv
  let supp : Finset (RentCoordinates n) := s.filter fun y => w y ≠ 0
  have hsupp_sum : ∑ y ∈ supp, w y = 1 := by
    calc
      ∑ y ∈ supp, w y = ∑ y ∈ s, w y := by
        simpa [supp] using (Finset.sum_filter_ne_zero (s := s) (f := w))
      _ = 1 := hw_sum
  have hsupp_center :
      supp.centerMass w id = ((x : RentSimplex n) : RentCoordinates n) := by
    calc
      supp.centerMass w id = s.centerMass w id := by
        simpa [supp] using (Finset.centerMass_filter_ne_zero (t := s) (w := w) (z := id))
      _ = ((x : RentSimplex n) : RentCoordinates n) := hw_center
  have hsupp_conv :
      ((x : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ (supp : Set (RentCoordinates n)) := by
    rw [← hsupp_center]
    refine Finset.centerMass_id_mem_convexHull supp ?_ ?_
    · intro y hy
      exact hw_nonneg _ (Finset.mem_filter.mp hy).1
    · rw [hsupp_sum]
      norm_num
  have hxFace' :
      ((x : RentSimplex n) : RentCoordinates n) ∈ ambientCoordinateFace (prefixRooms n u.level) :=
    mem_ambientCoordinateFace_of_mem_coordinateFace hxFace
  have hsupp_face :
      ∀ y ∈ supp, y ∈ ambientCoordinateFace (prefixRooms n u.level) := by
    intro y hy
    exact point_mem_ambientCoordinateFace_of_nonzero_weight hxτ hxFace'
      hw_nonneg hw_sum hw_center (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2
  have hsupp_subset :
      (supp : Set (RentCoordinates n)) ⊆
        (⟨section5FacetLowerPrefixVertices u τ⟩ : SimplexFacet n).pointSet := by
    intro y hy
    rcases Finset.mem_image.mp (Finset.mem_filter.mp hy).1 with ⟨v, hv, rfl⟩
    have hvFace : v ∈ coordinateFace (prefixRooms n u.level) :=
      mem_coordinateFace_of_mem_ambientCoordinateFace (hsupp_face _ hy)
    exact Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n)
      (Finset.mem_filter.mpr ⟨hv, hvFace⟩)
  exact convexHull_mono hsupp_subset hsupp_conv

def section5LowerPrefixVertices {n : ℕ} (u : Section5Node n) : Finset (RentSimplex n) := by
  classical
  exact u.cell.vertices.filter fun v => v ∈ coordinateFace (prefixRooms n u.level)

theorem section5LowerPrefixVertices_isSubface {n : ℕ} (u : Section5Node n) :
    (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n).IsSubfaceOf u.cell := by
  classical
  intro v hv
  exact (Finset.mem_filter.mp hv).1

theorem mem_realization_section5LowerPrefixVertices_of_mem_realization_of_mem_coordinateFace
    {n : ℕ} {u : Section5Node n} {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ u.cell.realization)
    (hxFace : x ∈ coordinateFace (prefixRooms n u.level)) :
    ((x : RentSimplex n) : RentCoordinates n) ∈
      (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n).realization := by
  simpa [section5LowerPrefixVertices, section5FacetLowerPrefixVertices] using
    (mem_realization_section5FacetLowerPrefixVertices_of_mem_realization_of_mem_coordinateFace
      (u := u) (τ := u.cell) hxτ hxFace)

def minimal_section5SegmentSubface_lowerBoundaryGeometry_of_facetLowerPrefixVertices_card_eq
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    (hulevel : 0 < u.level)
    {τ : SimplexFacet n} (hτ : τ ∈ section5SegmentSubfaces u f)
    (hmin : ∀ σ ∈ section5SegmentSubfaces u f, τ.vertices.card ≤ σ.vertices.card)
    {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization)
    (hxFace : x ∈ coordinateFace (prefixRooms n u.level))
    (hfxSeg : f x ∈ prefixBarycenterSegment n u.level)
    (hρcard : (section5FacetLowerPrefixVertices u τ).card = u.level) :
    Section5MinimalSliceLowerBoundaryGeometry u f := by
  classical
  exact minimal_section5SegmentSubface_lowerBoundaryGeometry_of_lower_boundary_face
    hfpl hu hulevel hτ hmin
    (section5FacetLowerPrefixVertices_isSubface u τ)
    hρcard
    (by
      intro w hw
      exact (Finset.mem_filter.mp hw).2)
    (mem_realization_section5FacetLowerPrefixVertices_of_mem_realization_of_mem_coordinateFace
      (u := u) (τ := τ) hxτ hxFace)
    hfxSeg

theorem IsPiecewiseAffineOn.facetImageContains_section5LowerPrefixVertices_of_mem_realization
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ u.cell.realization)
    (hxFace : x ∈ coordinateFace (prefixRooms n u.level))
    (hfx : f x = prefixBarycenter n u.level) :
    FacetImageContains f (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n)
      (prefixBarycenter n u.level) := by
  have hσreal :
      ((x : RentSimplex n) : RentCoordinates n) ∈
        (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n).realization :=
    mem_realization_section5LowerPrefixVertices_of_mem_realization_of_mem_coordinateFace hxτ hxFace
  have hσFace : T.IsFace (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n) := by
    rcases hu.isFace with ⟨τ, hτ, hsub⟩
    exact ⟨τ, hτ, (section5LowerPrefixVertices_isSubface u).trans hsub⟩
  have hhit :
      FacetImageContains f (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n) (f x) :=
    hfpl.facetImageContains_of_mem_realization hσFace hσreal
  simpa [hfx] using hhit

theorem IsPiecewiseAffineOn.facetImageContains_of_mem_realization_of_vertices_mem_coordinateFace
    {n k : ℕ} [NeZero n] [NeZero k] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f) {σ : SimplexFacet n}
    (hσ : T.IsFace σ) (hk : k + 1 ≤ n) {x : RentSimplex n}
    (hxσ : ((x : RentSimplex n) : RentCoordinates n) ∈ σ.realization)
    (hσface : ∀ ⦃v : RentSimplex n⦄, v ∈ σ.vertices → v ∈ coordinateFace (prefixRooms n k))
    (hfxSeg : f x ∈ prefixBarycenterSegment n k) :
    FacetImageContains f σ (prefixBarycenter n k) := by
  have hxFace : x ∈ coordinateFace (prefixRooms n k) :=
    σ.mem_coordinateFace_of_mem_realization_of_vertices_mem_coordinateFace hxσ hσface
  have hfx : f x = prefixBarycenter n k := by
    exact hf.eq_prefixBarycenter_of_mem_coordinateFace_of_map_mem_prefixBarycenterSegment
      hk hxFace hfxSeg
  have hhit : FacetImageContains f σ (f x) :=
    hfpl.facetImageContains_of_mem_realization hσ hxσ
  simpa [hfx] using hhit

theorem IsPiecewiseAffineOn.facetImageContains_section5LowerPrefixVertices_of_mem_realization_of_map_mem_segment
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hulevel : 0 < u.level) {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ u.cell.realization)
    (hxFace : x ∈ coordinateFace (prefixRooms n u.level))
    (hfxSeg : f x ∈ prefixBarycenterSegment n u.level) :
    FacetImageContains f (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n)
      (prefixBarycenter n u.level) := by
  haveI : NeZero u.level := ⟨Nat.ne_of_gt hulevel⟩
  have hfx : f x = prefixBarycenter n u.level := by
    exact hf.eq_prefixBarycenter_of_mem_coordinateFace_of_map_mem_prefixBarycenterSegment
      hu.level_le hxFace hfxSeg
  exact hfpl.facetImageContains_section5LowerPrefixVertices_of_mem_realization hu hxτ hxFace hfx

theorem IsPiecewiseAffineOn.exists_mem_section5CellSlice_and_mem_coordinateFace_of_facetImageContains_section5LowerPrefixVertices
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n}
    (hu : IsSection5GraphNode T f u)
    (hhit : FacetImageContains f (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n)
      (prefixBarycenter n u.level)) :
    ∃ x : RentSimplex n,
      x ∈ section5CellSlice u f ∧ x ∈ coordinateFace (prefixRooms n u.level) := by
  classical
  have hσFace : T.IsFace (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n) := by
    rcases hu.isFace with ⟨τ, hτ, hsub⟩
    exact ⟨τ, hτ, (section5LowerPrefixVertices_isSubface u).trans hsub⟩
  rcases hfpl.exists_point_in_realization_of_facetImageContains hσFace hhit with
    ⟨x, hxσ, hfx⟩
  have hxcell : ((x : RentSimplex n) : RentCoordinates n) ∈ u.cell.realization :=
    SimplexFacet.realization_mono_of_isSubface (section5LowerPrefixVertices_isSubface u) hxσ
  have hxFace : x ∈ coordinateFace (prefixRooms n u.level) := by
    exact SimplexFacet.mem_coordinateFace_of_mem_realization_of_vertices_mem_coordinateFace
      (τ := (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n)) hxσ
      (by
        intro v hv
        exact (Finset.mem_filter.mp hv).2)
  have hxSeg : f x ∈ prefixBarycenterSegment n u.level := by
    simpa [hfx, prefixBarycenterSegment] using
      (left_mem_segment ℝ (prefixBarycenter n u.level) (prefixBarycenter n (u.level + 1)))
  exact ⟨x, (mem_section5CellSlice_iff.mpr ⟨hxcell, hxSeg⟩), hxFace⟩

theorem IsPiecewiseAffineOn.facetImageContains_section5LowerPrefixVertices_iff_exists_mem_section5CellSlice_and_mem_coordinateFace
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hulevel : 0 < u.level) :
    FacetImageContains f (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n)
      (prefixBarycenter n u.level) ↔
        ∃ x : RentSimplex n,
          x ∈ section5CellSlice u f ∧ x ∈ coordinateFace (prefixRooms n u.level) := by
  constructor
  · exact
      hfpl.exists_mem_section5CellSlice_and_mem_coordinateFace_of_facetImageContains_section5LowerPrefixVertices
        hu
  · rintro ⟨x, hxSlice, hxFace⟩
    exact hfpl.facetImageContains_section5LowerPrefixVertices_of_mem_realization_of_map_mem_segment
      hf hu hulevel (mem_section5CellSlice_iff.mp hxSlice).1 hxFace
      (mem_section5CellSlice_iff.mp hxSlice).2

theorem IsFaceRespecting.simplexSupport_eq_prefixRooms_of_mem_coordinateFace_of_map_prefixBarycenter
    {n k : ℕ} [NeZero k] {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f)
    {x : RentSimplex n} (hxFace : x ∈ coordinateFace (prefixRooms n k))
    (hfx : f x = prefixBarycenter n k) :
    simplexSupport x = prefixRooms n k := by
  apply Finset.Subset.antisymm hxFace
  intro i hi
  have hsupport :
      coordSupport (prefixBarycenter n k) ⊆ simplexSupport x := by
    simpa [hfx] using hf.coordSupport_subset x
  have hi' : i ∈ coordSupport (prefixBarycenter n k) := by
    simpa [coordSupport_prefixBarycenter] using hi
  exact hsupport hi'

theorem IsFaceRespecting.exists_vertex_support_of_facetImageContains_prefixBarycenter
    {n k : ℕ} [NeZero k] {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f)
    {σ : SimplexFacet n} (hk : k ≤ n)
    (hσ : FacetImageContains f σ (prefixBarycenter n k))
    {i : RoomIndex n} (hi : i ∈ prefixRooms n k) :
    ∃ v ∈ σ.vertices, i ∈ simplexSupport v := by
  by_contra hno
  have hverts :
      ∀ ⦃v : RentSimplex n⦄, v ∈ σ.vertices → v ∈ coordinateFace (Finset.univ.erase i) := by
    intro v hv
    rw [mem_coordinateFace_iff]
    intro j hj
    have hj_eq : j = i := by
      simpa using hj
    have hi_notin : i ∉ simplexSupport v := by
      intro hmem
      exact hno ⟨v, hv, hmem⟩
    simpa [hj_eq, mem_simplexSupport] using hi_notin
  have himage :
      FacetImageHull f σ ⊆ ambientCoordinateFace (Finset.univ.erase i) := by
    refine facetImageHull_subset_ambientCoordinateFace ?_
    intro v hv
    exact hf.mapsTo_ambientCoordinateFace (Finset.univ.erase i) (hverts hv)
  have hbad : prefixBarycenter n k ∈ ambientCoordinateFace (Finset.univ.erase i) := himage hσ
  exact prefixBarycenter_not_mem_ambientCoordinateFace_erase (n := n) (k := k) hk hi hbad

theorem IsFaceRespecting.exists_section5LowerPrefixVertex_support_of_facetImageContains
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    (hσ : FacetImageContains f (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n)
      (prefixBarycenter n u.level))
    {i : RoomIndex n} (hi : i ∈ prefixRooms n u.level) :
    ∃ v ∈ section5LowerPrefixVertices u, i ∈ simplexSupport v := by
  have hpos : 0 < u.level := by
    have hlt : i.1 < u.level := mem_prefixRooms_iff.mp hi
    exact lt_of_lt_of_le (Nat.zero_lt_succ i.1) (Nat.succ_le_of_lt hlt)
  haveI : NeZero u.level := ⟨Nat.ne_of_gt hpos⟩
  have hk : u.level ≤ n := le_trans (Nat.le_succ u.level) hu.level_le
  simpa using hf.exists_vertex_support_of_facetImageContains_prefixBarycenter
    (σ := (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n)) hk hσ hi

theorem IsSection5GraphNode.card_lowerPrefixVertices_le {n : ℕ}
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) :
    (section5LowerPrefixVertices u).card ≤ u.level := by
  classical
  rcases hu.isFace with ⟨τ, hτ, hsub⟩
  have hS : section5LowerPrefixVertices u ⊆ τ.vertices := by
    intro v hv
    exact hsub ((Finset.mem_filter.mp hv).1)
  have hface : ∀ ⦃v : RentSimplex n⦄,
      v ∈ section5LowerPrefixVertices u → v ∈ coordinateFace (prefixRooms n u.level) := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hcard_le_prefix :
      (section5LowerPrefixVertices u).card ≤ (prefixVertexPoints n u.level).card :=
    T.card_le_prefixVertexPoints_of_subset_coordinateFace hτ hS hface
  have hlevel_le : u.level ≤ n := le_trans (Nat.le_succ u.level) hu.level_le
  calc
    (section5LowerPrefixVertices u).card ≤ (prefixVertexPoints n u.level).card := hcard_le_prefix
    _ = u.level := prefixVertexPoints_card hlevel_le

/-- One step in the Section 5 graph: a codimension-one incidence at the next barycenter of the
chain. -/
def Section5Step {n : ℕ} (f : SelfMapOnRentSimplex n) (u v : Section5Node n) : Prop :=
  u.level + 1 = v.level ∧ u.cell.IsSubfaceOf v.cell ∧
    FacetImageContains f u.cell (prefixBarycenter n v.level)

theorem section5Step_vertices_eq_lowerPrefixVertices {n : ℕ} {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n} {u v : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hv : IsSection5GraphNode T f v)
    (hstep : Section5Step f u v) :
    u.cell.vertices = section5LowerPrefixVertices v := by
  classical
  have hsub : u.cell.vertices ⊆ section5LowerPrefixVertices v := by
    intro w hw
    refine Finset.mem_filter.mpr ⟨hstep.2.1 hw, ?_⟩
    simpa [section5LowerPrefixVertices, hstep.1] using hu.prefix_vertices hw
  refine Finset.eq_of_subset_of_card_le hsub ?_
  have hcard_le : (section5LowerPrefixVertices v).card ≤ v.level := by
    exact IsSection5GraphNode.card_lowerPrefixVertices_le hv
  have hcard_eq : u.cell.vertices.card = v.level := by
    rw [hu.card_eq, ← hstep.1]
  calc
    (section5LowerPrefixVertices v).card ≤ v.level := hcard_le
    _ = u.cell.vertices.card := hcard_eq.symm

theorem IsPiecewiseAffineOn.section5Step_card_eq_lowerPrefixVertices_and_exists_point
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u v : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hv : IsSection5GraphNode T f v)
    (hstep : Section5Step f v u) :
    (section5LowerPrefixVertices u).card = u.level ∧
      ∃ x : RentSimplex n,
        x ∈ section5CellSlice u f ∧ x ∈ coordinateFace (prefixRooms n u.level) := by
  have hverts : v.cell.vertices = section5LowerPrefixVertices u :=
    section5Step_vertices_eq_lowerPrefixVertices hv hu hstep
  have hcard : (section5LowerPrefixVertices u).card = u.level := by
    rw [← hverts, hv.card_eq, hstep.1]
  have hhit :
      FacetImageContains f (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n)
        (prefixBarycenter n u.level) := by
    simpa [← hverts] using hstep.2.2
  exact
    ⟨hcard,
      hfpl.exists_mem_section5CellSlice_and_mem_coordinateFace_of_facetImageContains_section5LowerPrefixVertices
        hu hhit⟩

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

theorem section5_levelOne_cell_vertices_eq_start_pair {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hlevel : u.level = 1)
    (hsub : (section5StartCell n).IsSubfaceOf u.cell) :
    ∃ w : RentSimplex n, w ≠ section5StartVertex n ∧ u.cell.vertices = {section5StartVertex n, w} := by
  have hcard : u.cell.vertices.card = 2 := by simpa [hlevel] using hu.card_eq
  have hstart_mem : section5StartVertex n ∈ u.cell.vertices := hsub (by simp [section5StartCell])
  rcases Finset.card_eq_two.mp hcard with ⟨x, y, hxy, hverts⟩
  rw [hverts] at hstart_mem
  rcases Finset.mem_insert.mp hstart_mem with hstart_eq_x | hstart_eq_y
  · refine ⟨y, ?_, ?_⟩
    · simpa [hstart_eq_x] using hxy.symm
    · simpa [hverts, hstart_eq_x]
  · have hstart_eq_y' : section5StartVertex n = y := by simpa using hstart_eq_y
    refine ⟨x, ?_, ?_⟩
    · simpa [hstart_eq_y'] using hxy
    · simpa [hverts, hstart_eq_y', Finset.insert_comm, Finset.pair_comm]

theorem section5_levelZero_cell_eq_startCell {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hlevel : u.level = 0) :
    u.cell = section5StartCell n := by
  cases u with
  | mk ul uc =>
      simp at hlevel
      subst hlevel
      have hcard : uc.vertices.card = 1 := by simpa using hu.card_eq
      rcases Finset.card_eq_one.mp hcard with ⟨v, hv⟩
      have hvFace : v ∈ coordinateFace (prefixRooms n 1) := by
        simpa using hu.prefix_vertices (by simpa [hv] using Finset.mem_singleton_self v)
      have hvEq : v = section5StartVertex n :=
        eq_section5StartVertex_of_mem_coordinateFace_prefixRooms_one hvFace
      have hverts : uc.vertices = (section5StartCell n).vertices := by
        simpa [section5StartCell, hvEq] using hv
      cases uc
      simpa [section5StartCell] using hverts

theorem section5_levelZero_eq_startNode {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hlevel : u.level = 0) :
    u = section5StartNode n := by
  cases u with
  | mk ul uc =>
      simp at hlevel
      subst hlevel
      have hcell : uc = section5StartCell n :=
        section5_levelZero_cell_eq_startCell (u := ⟨0, uc⟩) hu rfl
      simp [section5StartNode, hcell]

theorem section5StartComponent_pos_level_of_ne_start {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {u : section5StartComponent hstart}
    (hu_ne : u ≠ section5StartVertexInComponent hstart) :
    0 < u.1.1.level := by
  by_contra hzero
  have hu0 : u.1.1.level = 0 := Nat.eq_zero_of_not_pos hzero
  have hu_node : IsSection5GraphNode T f u.1.1 := (mem_section5Nodes_iff).mp u.1.2
  have hu_eq_start : u.1.1 = section5StartNode n := section5_levelZero_eq_startNode hu_node hu0
  apply hu_ne
  exact Subtype.ext (Subtype.ext hu_eq_start)

theorem exists_section5LowerStep_of_subface_card_eq_and_facetImageContains
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {u : Section5Node n} (hu : IsSection5GraphNode T f u) (hulevel : 0 < u.level)
    {τ : SimplexFacet n} (hτsub : τ.IsSubfaceOf u.cell)
    (hτcard : τ.vertices.card = u.level)
    (hτface : ∀ ⦃w : RentSimplex n⦄, w ∈ τ.vertices → w ∈ coordinateFace (prefixRooms n u.level))
    (hhit : FacetImageContains f τ (prefixBarycenter n u.level)) :
    ∃ v : Section5Node n, IsSection5GraphNode T f v ∧ Section5Step f v u := by
  let v : Section5Node n := ⟨u.level - 1, τ⟩
  have hlevel : v.level + 1 = u.level := by
    dsimp [v]
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt hulevel)
  have hv : IsSection5GraphNode T f v := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [hlevel] using le_trans (Nat.le_succ u.level) hu.level_le
    · rcases hu.isFace with ⟨σ, hσ, hσsub⟩
      exact ⟨σ, hσ, hτsub.trans hσsub⟩
    · calc
        v.cell.vertices.card = τ.vertices.card := by rfl
        _ = u.level := hτcard
        _ = v.level + 1 := hlevel.symm
    · intro w hw
      simpa [hlevel] using hτface hw
    · refine ⟨prefixBarycenter n u.level, hhit, ?_⟩
      simpa [prefixBarycenterSegment, hlevel] using
        right_mem_segment ℝ (prefixBarycenter n (u.level - 1)) (prefixBarycenter n u.level)
  refine ⟨v, hv, ?_⟩
  exact ⟨hlevel, hτsub, hhit⟩

theorem exists_section5StartComponentLowerStep_of_subface_card_eq_and_facetImageContains
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {u : section5StartComponent hstart}
    (hu_ne : u ≠ section5StartVertexInComponent hstart)
    {τ : SimplexFacet n} (hτsub : τ.IsSubfaceOf u.1.1.cell)
    (hτcard : τ.vertices.card = u.1.1.level)
    (hτface :
      ∀ ⦃w : RentSimplex n⦄, w ∈ τ.vertices →
        w ∈ coordinateFace (prefixRooms n u.1.1.level))
    (hhit : FacetImageContains f τ (prefixBarycenter n u.1.1.level)) :
    ∃ v : section5StartComponent hstart, Section5Step f v.1.1 u.1.1 := by
  have hu_node : IsSection5GraphNode T f u.1.1 := (mem_section5Nodes_iff).mp u.1.2
  have hulevel : 0 < u.1.1.level := by
    by_contra hzero
    have hu0 : u.1.1.level = 0 := Nat.eq_zero_of_not_pos hzero
    have hu_eq_start : u.1.1 = section5StartNode n := section5_levelZero_eq_startNode hu_node hu0
    apply hu_ne
    exact Subtype.ext (Subtype.ext hu_eq_start)
  rcases exists_section5LowerStep_of_subface_card_eq_and_facetImageContains
      hu_node hulevel hτsub hτcard hτface hhit with ⟨v0, hv0, hv0_step⟩
  let vnode : section5Nodes T f := ⟨v0, hv0.mem_section5Nodes⟩
  have hu_reach :
      (section5NodeGraph T f).Reachable (section5StartNodeInNodes hstart) u.1 := by
    exact (mem_section5StartComponent_iff_reachable (hstart := hstart)).mp u.2
  have hv0_adj : (section5NodeGraph T f).Adj vnode u.1 := by
    simpa [section5NodeGraph, section5SimpleGraph, vnode] using
      (Or.inl hv0_step : Section5Adjacent f v0 u.1.1)
  have hv_reach :
      (section5NodeGraph T f).Reachable (section5StartNodeInNodes hstart) vnode := by
    exact hu_reach.trans <| (SimpleGraph.reachable_comm.mp (SimpleGraph.Adj.reachable hv0_adj))
  refine ⟨⟨vnode, (mem_section5StartComponent_iff_reachable (hstart := hstart)).mpr hv_reach⟩, hv0_step⟩

theorem exists_section5LowerStep_of_subface_card_eq_and_mem_realization_map_segment
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f)
    {u : Section5Node n} (hu : IsSection5GraphNode T f u) (hulevel : 0 < u.level)
    {τ : SimplexFacet n} (hτsub : τ.IsSubfaceOf u.cell)
    (hτcard : τ.vertices.card = u.level)
    (hτface : ∀ ⦃w : RentSimplex n⦄, w ∈ τ.vertices → w ∈ coordinateFace (prefixRooms n u.level))
    {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization)
    (hfxSeg : f x ∈ prefixBarycenterSegment n u.level) :
    ∃ v : Section5Node n, IsSection5GraphNode T f v ∧ Section5Step f v u := by
  have hτisFace : T.IsFace τ := by
    rcases hu.isFace with ⟨σ, hσ, hσsub⟩
    exact ⟨σ, hσ, hτsub.trans hσsub⟩
  have hhit : FacetImageContains f τ (prefixBarycenter n u.level) := by
    haveI : NeZero u.level := ⟨Nat.ne_of_gt hulevel⟩
    exact hfpl.facetImageContains_of_mem_realization_of_vertices_mem_coordinateFace
      hf hτisFace hu.level_le hxτ hτface hfxSeg
  exact exists_section5LowerStep_of_subface_card_eq_and_facetImageContains
    hu hulevel hτsub hτcard hτface hhit

theorem exists_section5StartComponentLowerStep_of_subface_card_eq_and_mem_realization_map_segment
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {u : section5StartComponent hstart}
    (hu_ne : u ≠ section5StartVertexInComponent hstart)
    {τ : SimplexFacet n} (hτsub : τ.IsSubfaceOf u.1.1.cell)
    (hτcard : τ.vertices.card = u.1.1.level)
    (hτface :
      ∀ ⦃w : RentSimplex n⦄, w ∈ τ.vertices →
        w ∈ coordinateFace (prefixRooms n u.1.1.level))
    {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization)
    (hfxSeg : f x ∈ prefixBarycenterSegment n u.1.1.level) :
    ∃ v : section5StartComponent hstart, Section5Step f v.1.1 u.1.1 := by
  have hu_node : IsSection5GraphNode T f u.1.1 := (mem_section5Nodes_iff).mp u.1.2
  have hulevel : 0 < u.1.1.level := by
    by_contra hzero
    have hu0 : u.1.1.level = 0 := Nat.eq_zero_of_not_pos hzero
    have hu_eq_start : u.1.1 = section5StartNode n := section5_levelZero_eq_startNode hu_node hu0
    apply hu_ne
    exact Subtype.ext (Subtype.ext hu_eq_start)
  rcases exists_section5LowerStep_of_subface_card_eq_and_mem_realization_map_segment
      hf hfpl hu_node hulevel hτsub hτcard hτface hxτ hfxSeg with ⟨v0, hv0, hv0_step⟩
  let vnode : section5Nodes T f := ⟨v0, hv0.mem_section5Nodes⟩
  have hu_reach :
      (section5NodeGraph T f).Reachable (section5StartNodeInNodes hstart) u.1 := by
    exact (mem_section5StartComponent_iff_reachable (hstart := hstart)).mp u.2
  have hv0_adj : (section5NodeGraph T f).Adj vnode u.1 := by
    simpa [section5NodeGraph, section5SimpleGraph, vnode] using
      (Or.inl hv0_step : Section5Adjacent f v0 u.1.1)
  have hv_reach :
      (section5NodeGraph T f).Reachable (section5StartNodeInNodes hstart) vnode := by
    exact hu_reach.trans <| (SimpleGraph.reachable_comm.mp (SimpleGraph.Adj.reachable hv0_adj))
  refine ⟨⟨vnode, (mem_section5StartComponent_iff_reachable (hstart := hstart)).mpr hv_reach⟩, hv0_step⟩

/-- Direct lower-entry data on one Section 5 cell: a codimension-one lower face of `u.cell`
already hits the lower prefix barycenter. This packages the manuscript's "entry through a lower
face" picture before introducing any minimal segment-hitting carrier face. -/
structure Section5LowerEntryFaceData {n : ℕ} (u : Section5Node n)
    (f : SelfMapOnRentSimplex n) where
  face : SimplexFacet n
  isSubface : face.IsSubfaceOf u.cell
  card_eq : face.vertices.card = u.level
  lower_prefix_vertices :
    ∀ ⦃w : RentSimplex n⦄, w ∈ face.vertices → w ∈ coordinateFace (prefixRooms n u.level)
  hits_barycenter : FacetImageContains f face (prefixBarycenter n u.level)

theorem Section5LowerEntryFaceData.exists_lowerStep {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hulevel : 0 < u.level)
    (hentry : Section5LowerEntryFaceData u f) :
    ∃ v : Section5Node n, IsSection5GraphNode T f v ∧ Section5Step f v u := by
  exact exists_section5LowerStep_of_subface_card_eq_and_facetImageContains
    hu hulevel hentry.isSubface hentry.card_eq hentry.lower_prefix_vertices
    hentry.hits_barycenter

theorem Section5LowerEntryFaceData.exists_startComponentLowerStep {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {u : section5StartComponent hstart}
    (hu_ne : u ≠ section5StartVertexInComponent hstart)
    (hentry : Section5LowerEntryFaceData u.1.1 f) :
    ∃ v : section5StartComponent hstart, Section5Step f v.1.1 u.1.1 := by
  exact exists_section5StartComponentLowerStep_of_subface_card_eq_and_facetImageContains
    hu_ne hentry.isSubface hentry.card_eq hentry.lower_prefix_vertices
    hentry.hits_barycenter

theorem Section5LowerEntryFaceData.vertices_eq_lowerPrefixVertices {n : ℕ}
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hentry : Section5LowerEntryFaceData u f) :
    hentry.face.vertices = section5LowerPrefixVertices u := by
  classical
  have hsub : hentry.face.vertices ⊆ section5LowerPrefixVertices u := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨hentry.isSubface hw, hentry.lower_prefix_vertices hw⟩
  refine Finset.eq_of_subset_of_card_le hsub ?_
  calc
    (section5LowerPrefixVertices u).card ≤ u.level :=
      IsSection5GraphNode.card_lowerPrefixVertices_le hu
    _ = hentry.face.vertices.card := hentry.card_eq.symm

theorem Section5LowerEntryFaceData.face_eq_lowerPrefixVertices {n : ℕ}
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hentry : Section5LowerEntryFaceData u f) :
    hentry.face = (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n) := by
  classical
  cases hentry with
  | mk face isSubface card_eq lower_prefix_vertices hits_barycenter =>
      cases face with
      | mk vertices =>
          change ({ vertices := vertices } : SimplexFacet n) =
            ({ vertices := section5LowerPrefixVertices u } : SimplexFacet n)
          have hverts : vertices = section5LowerPrefixVertices u := by
            have hsub : vertices ⊆ section5LowerPrefixVertices u := by
              intro w hw
              exact Finset.mem_filter.mpr ⟨isSubface hw, lower_prefix_vertices hw⟩
            refine Finset.eq_of_subset_of_card_le hsub ?_
            calc
              (section5LowerPrefixVertices u).card ≤ u.level :=
                IsSection5GraphNode.card_lowerPrefixVertices_le hu
              _ = vertices.card := card_eq.symm
          cases hverts
          rfl

theorem Section5LowerEntryFaceData.facetImageContains_lowerPrefixVertices {n : ℕ}
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hentry : Section5LowerEntryFaceData u f) :
    FacetImageContains f (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n)
      (prefixBarycenter n u.level) := by
  simpa [hentry.face_eq_lowerPrefixVertices hu] using hentry.hits_barycenter

theorem Section5LowerEntryFaceData.card_eq_lowerPrefixVertices {n : ℕ}
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hentry : Section5LowerEntryFaceData u f) :
    (section5LowerPrefixVertices u).card = u.level := by
  simpa [hentry.vertices_eq_lowerPrefixVertices hu] using hentry.card_eq

theorem section5LowerEntryFaceData_nonempty_iff_card_eq_and_facetImageContains_lowerPrefixVertices
    {n : ℕ} {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u : Section5Node n}
    (hu : IsSection5GraphNode T f u) :
    Nonempty (Section5LowerEntryFaceData u f) ↔
      (section5LowerPrefixVertices u).card = u.level ∧
        FacetImageContains f (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n)
          (prefixBarycenter n u.level) := by
  classical
  constructor
  · rintro ⟨hentry⟩
    exact ⟨hentry.card_eq_lowerPrefixVertices hu,
      hentry.facetImageContains_lowerPrefixVertices hu⟩
  · rintro ⟨hcard, hhit⟩
    refine ⟨⟨⟨section5LowerPrefixVertices u⟩, section5LowerPrefixVertices_isSubface u, hcard, ?_,
      hhit⟩⟩
    intro w hw
    exact (Finset.mem_filter.mp hw).2

theorem Section5MinimalSliceLowerBoundaryGeometry.card_eq_lowerPrefixVertices_and_exists_point
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f)
    {u : Section5Node n} (hu : IsSection5GraphNode T f u) (hulevel : 0 < u.level)
    (hgeom : Section5MinimalSliceLowerBoundaryGeometry u f) :
    (section5LowerPrefixVertices u).card = u.level ∧
      ∃ x : RentSimplex n,
        x ∈ section5CellSlice u f ∧ x ∈ coordinateFace (prefixRooms n u.level) := by
  have hτsubu : hgeom.minimal_face.IsSubfaceOf u.cell :=
    (mem_section5SegmentSubfaces_iff
      (u := u) (f := f) (τ := hgeom.minimal_face)).mp hgeom.mem_segmentSubfaces |>.1
  have hρsubu : hgeom.lower_boundary_face.IsSubfaceOf u.cell :=
    hgeom.lower_boundary_isSubface.trans hτsubu
  have hxFace :
      hgeom.lower_boundary_point ∈ coordinateFace (prefixRooms n u.level) := by
    exact hgeom.lower_boundary_face.mem_coordinateFace_of_mem_realization_of_vertices_mem_coordinateFace
      hgeom.lower_boundary_point_mem_realization hgeom.lower_boundary_prefix_vertices
  have hρface : T.IsFace hgeom.lower_boundary_face := by
    rcases hu.isFace with ⟨σ, hσ, hσsub⟩
    exact ⟨σ, hσ, hρsubu.trans hσsub⟩
  have hhit :
      FacetImageContains f hgeom.lower_boundary_face (prefixBarycenter n u.level) := by
    haveI : NeZero u.level := ⟨Nat.ne_of_gt hulevel⟩
    exact hfpl.facetImageContains_of_mem_realization_of_vertices_mem_coordinateFace
      hf hρface hu.level_le hgeom.lower_boundary_point_mem_realization
      hgeom.lower_boundary_prefix_vertices hgeom.lower_boundary_point_mem_slice.2
  let hentry : Section5LowerEntryFaceData u f :=
    ⟨hgeom.lower_boundary_face, hρsubu, hgeom.lower_boundary_card_eq,
      hgeom.lower_boundary_prefix_vertices, hhit⟩
  refine ⟨hentry.card_eq_lowerPrefixVertices hu, ?_⟩
  exact ⟨hgeom.lower_boundary_point, hgeom.lower_boundary_point_mem_slice, hxFace⟩

def section5LowerEntryFaceData_of_card_eq_and_facetImageContains {n : ℕ}
    {f : SelfMapOnRentSimplex n} (u : Section5Node n)
    (hcard : (section5LowerPrefixVertices u).card = u.level)
    (hhit :
      FacetImageContains f (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n)
        (prefixBarycenter n u.level)) :
    Section5LowerEntryFaceData u f := by
  classical
  refine ⟨⟨section5LowerPrefixVertices u⟩, section5LowerPrefixVertices_isSubface u, hcard, ?_,
    hhit⟩
  intro w hw
  exact (Finset.mem_filter.mp hw).2

def section5LowerEntryFaceData_of_card_eq_and_mem_realization_map_prefixBarycenter
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ u.cell.realization)
    (hxFace : x ∈ coordinateFace (prefixRooms n u.level))
    (hfx : f x = prefixBarycenter n u.level)
    (hcard : (section5LowerPrefixVertices u).card = u.level) :
    Section5LowerEntryFaceData u f := by
  exact section5LowerEntryFaceData_of_card_eq_and_facetImageContains u hcard
    (hfpl.facetImageContains_section5LowerPrefixVertices_of_mem_realization hu hxτ hxFace hfx)

def section5LowerEntryFaceData_of_card_eq_and_mem_realization_map_segment
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f)
    {u : Section5Node n} (hu : IsSection5GraphNode T f u) (hulevel : 0 < u.level)
    {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ u.cell.realization)
    (hxFace : x ∈ coordinateFace (prefixRooms n u.level))
    (hfxSeg : f x ∈ prefixBarycenterSegment n u.level)
    (hcard : (section5LowerPrefixVertices u).card = u.level) :
    Section5LowerEntryFaceData u f := by
  exact section5LowerEntryFaceData_of_card_eq_and_facetImageContains u hcard
    (hfpl.facetImageContains_section5LowerPrefixVertices_of_mem_realization_of_map_mem_segment
      hf hu hulevel hxτ hxFace hfxSeg)

theorem exists_section5LowerStep_of_card_eq_and_mem_realization_map_prefixBarycenter
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f) {u : Section5Node n} (hu : IsSection5GraphNode T f u)
    (hulevel : 0 < u.level) {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ u.cell.realization)
    (hxFace : x ∈ coordinateFace (prefixRooms n u.level))
    (hfx : f x = prefixBarycenter n u.level)
    (hcard : (section5LowerPrefixVertices u).card = u.level) :
    ∃ v : Section5Node n, IsSection5GraphNode T f v ∧ Section5Step f v u := by
  classical
  let v : Section5Node n := ⟨u.level - 1, ⟨section5LowerPrefixVertices u⟩⟩
  have hlevel : v.level + 1 = u.level := by
    dsimp [v]
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt hulevel)
  have hhit :
      FacetImageContains f v.cell (prefixBarycenter n u.level) := by
    simpa [v] using hfpl.facetImageContains_section5LowerPrefixVertices_of_mem_realization
      hu hxτ hxFace hfx
  have hv : IsSection5GraphNode T f v := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [hlevel] using le_trans (Nat.le_succ u.level) hu.level_le
    · rcases hu.isFace with ⟨τ, hτ, hsub⟩
      exact ⟨τ, hτ, (section5LowerPrefixVertices_isSubface u).trans hsub⟩
    · calc
        v.cell.vertices.card = (section5LowerPrefixVertices u).card := by simp [v]
        _ = u.level := hcard
        _ = v.level + 1 := hlevel.symm
    · intro w hw
      have hw' : w ∈ section5LowerPrefixVertices u := by simpa [v] using hw
      have hwFace : w ∈ coordinateFace (prefixRooms n u.level) := (Finset.mem_filter.mp hw').2
      simpa [hlevel] using hwFace
    · refine ⟨prefixBarycenter n u.level, hhit, ?_⟩
      simpa [prefixBarycenterSegment, hlevel] using
        right_mem_segment ℝ (prefixBarycenter n (u.level - 1)) (prefixBarycenter n u.level)
  refine ⟨v, hv, hlevel, section5LowerPrefixVertices_isSubface u, hhit⟩

theorem exists_section5StartComponentLowerStep_of_card_eq_and_mem_realization_map_prefixBarycenter
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {u : section5StartComponent hstart}
    (hu_ne : u ≠ section5StartVertexInComponent hstart) {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ u.1.1.cell.realization)
    (hxFace : x ∈ coordinateFace (prefixRooms n u.1.1.level))
    (hfx : f x = prefixBarycenter n u.1.1.level)
    (hcard : (section5LowerPrefixVertices u.1.1).card = u.1.1.level) :
    ∃ v : section5StartComponent hstart, Section5Step f v.1.1 u.1.1 := by
  have hu_node : IsSection5GraphNode T f u.1.1 := (mem_section5Nodes_iff).mp u.1.2
  have hulevel : 0 < u.1.1.level := by
    by_contra hzero
    have hu0 : u.1.1.level = 0 := Nat.eq_zero_of_not_pos hzero
    have hu_eq_start : u.1.1 = section5StartNode n := section5_levelZero_eq_startNode hu_node hu0
    apply hu_ne
    exact Subtype.ext (Subtype.ext hu_eq_start)
  rcases exists_section5LowerStep_of_card_eq_and_mem_realization_map_prefixBarycenter hfpl hu_node
      hulevel hxτ hxFace hfx hcard with ⟨v0, hv0, hv0_step⟩
  let vnode : section5Nodes T f := ⟨v0, hv0.mem_section5Nodes⟩
  have hu_reach :
      (section5NodeGraph T f).Reachable (section5StartNodeInNodes hstart) u.1 := by
    exact (mem_section5StartComponent_iff_reachable (hstart := hstart)).mp u.2
  have hv0_adj : (section5NodeGraph T f).Adj vnode u.1 := by
    simpa [section5NodeGraph, section5SimpleGraph, vnode] using
      (Or.inl hv0_step : Section5Adjacent f v0 u.1.1)
  have hv_reach :
      (section5NodeGraph T f).Reachable (section5StartNodeInNodes hstart) vnode := by
    exact hu_reach.trans <| (SimpleGraph.reachable_comm.mp (SimpleGraph.Adj.reachable hv0_adj))
  refine ⟨⟨vnode, (mem_section5StartComponent_iff_reachable (hstart := hstart)).mpr hv_reach⟩, hv0_step⟩

theorem exists_section5StartComponentLowerStep_of_card_eq_and_mem_realization_map_segment
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {u : section5StartComponent hstart}
    (hu_ne : u ≠ section5StartVertexInComponent hstart) {x : RentSimplex n}
    (hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ u.1.1.cell.realization)
    (hxFace : x ∈ coordinateFace (prefixRooms n u.1.1.level))
    (hfxSeg : f x ∈ prefixBarycenterSegment n u.1.1.level)
    (hcard : (section5LowerPrefixVertices u.1.1).card = u.1.1.level) :
    ∃ v : section5StartComponent hstart, Section5Step f v.1.1 u.1.1 := by
  have hu_node : IsSection5GraphNode T f u.1.1 := (mem_section5Nodes_iff).mp u.1.2
  have hulevel : 0 < u.1.1.level := by
    by_contra hzero
    have hu0 : u.1.1.level = 0 := Nat.eq_zero_of_not_pos hzero
    have hu_eq_start : u.1.1 = section5StartNode n := section5_levelZero_eq_startNode hu_node hu0
    apply hu_ne
    exact Subtype.ext (Subtype.ext hu_eq_start)
  have hfx : f x = prefixBarycenter n u.1.1.level := by
    haveI : NeZero u.1.1.level := ⟨Nat.ne_of_gt hulevel⟩
    exact hf.eq_prefixBarycenter_of_mem_coordinateFace_of_map_mem_prefixBarycenterSegment
      hu_node.level_le hxFace hfxSeg
  exact exists_section5StartComponentLowerStep_of_card_eq_and_mem_realization_map_prefixBarycenter
    hfpl hu_ne hxτ hxFace hfx hcard

theorem Section5MinimalSliceFaceData.exists_startComponentLowerStep {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {u : section5StartComponent hstart}
    (hu_ne : u ≠ section5StartVertexInComponent hstart)
    (hdata : Section5MinimalSliceFaceData u.1.1 f) :
    ∃ v : section5StartComponent hstart, Section5Step f v.1.1 u.1.1 := by
  have hu_node : IsSection5GraphNode T f u.1.1 := (mem_section5Nodes_iff).mp u.1.2
  rcases hdata.exists_point_mem_slice hfpl hu_node with ⟨x, hxSlice, hxface⟩
  exact exists_section5StartComponentLowerStep_of_subface_card_eq_and_mem_realization_map_segment
    hf hfpl hu_ne hdata.face_isSubface hdata.card_eq hdata.lower_prefix_vertices hxface hxSlice.2

theorem section5StartComponentGraph_lower_neighbor_unique {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {u w v : section5StartComponent hstart}
    (huv : (section5StartComponentGraph hstart).Adj u v)
    (huLevel : u.1.1.level + 1 = v.1.1.level)
    (hwv : (section5StartComponentGraph hstart).Adj w v)
    (hwLevel : w.1.1.level + 1 = v.1.1.level) :
    u = w := by
  have huv' := (section5StartComponentGraph_adj_iff hstart).mp huv
  have hwv' := (section5StartComponentGraph_adj_iff hstart).mp hwv
  have hu_node : IsSection5GraphNode T f u.1.1 := (mem_section5Nodes_iff).mp u.1.2
  have hw_node : IsSection5GraphNode T f w.1.1 := (mem_section5Nodes_iff).mp w.1.2
  have hv_node : IsSection5GraphNode T f v.1.1 := (mem_section5Nodes_iff).mp v.1.2
  have huv_step : Section5Step f u.1.1 v.1.1 := by
    rcases huv' with huv_step | hvu_step
    · exact huv_step
    · have hcontra : u.1.1.level + 1 + 1 = u.1.1.level := by
        simpa [huLevel, Nat.add_assoc] using hvu_step.1
      omega
  have hwv_step : Section5Step f w.1.1 v.1.1 := by
    rcases hwv' with hwv_step | hvw_step
    · exact hwv_step
    · have hcontra : w.1.1.level + 1 + 1 = w.1.1.level := by
        simpa [hwLevel, Nat.add_assoc] using hvw_step.1
      omega
  have huverts := section5Step_vertices_eq_lowerPrefixVertices hu_node hv_node huv_step
  have hwverts := section5Step_vertices_eq_lowerPrefixVertices hw_node hv_node hwv_step
  have hcell_verts : u.1.1.cell.vertices = w.1.1.cell.vertices := by
    rw [huverts, hwverts]
  have hlevel_eq : u.1.1.level = w.1.1.level := by omega
  have hnode_eq : u.1.1 = w.1.1 := by
    cases hnode_u : u.1.1 with
    | mk ul uc =>
        cases hnode_w : w.1.1 with
        | mk wl wc =>
            have hlevel_eq' : ul = wl := by
              simpa [hnode_u, hnode_w] using hlevel_eq
            have hcell_verts' : uc.vertices = wc.vertices := by
              simpa [hnode_u, hnode_w] using hcell_verts
            cases hlevel_eq'
            cases uc
            cases wc
            simpa using hcell_verts'
  have hnodes_eq : u.1 = w.1 := by
    exact Subtype.ext hnode_eq
  exact Subtype.ext hnodes_eq

theorem section5StartComponentGraph_lower_neighbor_of_levelOne_eq_start {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {u v : section5StartComponent hstart}
    (_huv : (section5StartComponentGraph hstart).Adj u v)
    (huLevel : u.1.1.level + 1 = v.1.1.level) (hvLevel : v.1.1.level = 1) :
    u = section5StartVertexInComponent hstart := by
  apply Subtype.ext
  show u.1 = section5StartNodeInNodes hstart
  apply Subtype.ext
  have huNode : IsSection5GraphNode T f u.1.1 := (mem_section5Nodes_iff).mp u.1.2
  have huLevelZero : u.1.1.level = 0 := by omega
  simpa [section5StartVertexInComponent, section5StartNodeInNodes] using
    (section5_levelZero_eq_startNode (T := T) (f := f) (u := u.1.1) huNode huLevelZero)

theorem section5StartComponentGraph_lower_neighbor_unique_of_levelOne {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {u w v : section5StartComponent hstart}
    (huv : (section5StartComponentGraph hstart).Adj u v)
    (huLevel : u.1.1.level + 1 = v.1.1.level)
    (hwv : (section5StartComponentGraph hstart).Adj w v)
    (hwLevel : w.1.1.level + 1 = v.1.1.level)
    (hvLevel : v.1.1.level = 1) :
    u = w := by
  rw [section5StartComponentGraph_lower_neighbor_of_levelOne_eq_start huv huLevel hvLevel]
  exact (section5StartComponentGraph_lower_neighbor_of_levelOne_eq_start hwv hwLevel hvLevel).symm

theorem section5_levelOne_start_subface_unique {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} {u v : Section5Node n}
    (hu : IsSection5GraphNode T f u) (hv : IsSection5GraphNode T f v)
    (hulevel : u.level = 1) (hvlevel : v.level = 1)
    (husub : (section5StartCell n).IsSubfaceOf u.cell)
    (hvsub : (section5StartCell n).IsSubfaceOf v.cell) :
    u = v := by
  obtain ⟨a, ha_ne, huverts⟩ := section5_levelOne_cell_vertices_eq_start_pair hu hulevel husub
  obtain ⟨b, hb_ne, hvverts⟩ := section5_levelOne_cell_vertices_eq_start_pair hv hvlevel hvsub
  by_cases hab : a = b
  · subst hab
    have hcell_verts : u.cell.vertices = v.cell.vertices := by
      simpa using huverts.trans hvverts.symm
    cases u with
    | mk ul uc =>
      cases v with
      | mk vl vc =>
        simp at hulevel hvlevel
        subst hulevel
        subst hvlevel
        have hc : uc = vc := by
          cases uc
          cases vc
          simpa using hcell_verts
        cases hc
        rfl
  · obtain ⟨τu, hτu, hτu_sub⟩ := hu.isFace
    obtain ⟨τv, hτv, hτv_sub⟩ := hv.isFace
    have ha_ucell : a ∈ u.cell.vertices := by
      rw [huverts]
      simp
    have hb_vcell : b ∈ v.cell.vertices := by
      rw [hvverts]
      simp
    have ha_face :
        ((a : RentSimplex n) : RentCoordinates n) ∈ ambientCoordinateFace (prefixRooms n 2) := by
      exact mem_ambientCoordinateFace_of_mem_coordinateFace <|
        (by simpa [hulevel] using hu.prefix_vertices ha_ucell)
    have hb_face :
        ((b : RentSimplex n) : RentCoordinates n) ∈ ambientCoordinateFace (prefixRooms n 2) := by
      exact mem_ambientCoordinateFace_of_mem_coordinateFace <|
        (by simpa [hvlevel] using hv.prefix_vertices hb_vcell)
    have ha_ne_coord : ((a : RentSimplex n) : RentCoordinates n) ≠ prefixBarycenter n 1 := by
      intro ha_coord
      apply ha_ne
      apply Subtype.ext
      simpa [section5StartVertex] using ha_coord
    have hb_ne_coord : ((b : RentSimplex n) : RentCoordinates n) ≠ prefixBarycenter n 1 := by
      intro hb_coord
      apply hb_ne
      apply Subtype.ext
      simpa [section5StartVertex] using hb_coord
    have ha_τu : a ∈ τu.vertices := hτu_sub ha_ucell
    have hb_τv : b ∈ τv.vertices := hτv_sub hb_vcell
    rcases le_total (((b : RentSimplex n) : RentCoordinates n) (0 : RoomIndex n))
        (((a : RentSimplex n) : RentCoordinates n) (0 : RoomIndex n)) with hba | hab'
    · have ha_seg :
          ((a : RentSimplex n) : RentCoordinates n) ∈
            segment ℝ (prefixBarycenter n 1) ((b : RentSimplex n) : RentCoordinates n) :=
        mem_segment_prefixBarycenter_one_of_boundary_zero_order ha_face hb_face hb_ne_coord hba
      have ha_vcell :
          ((a : RentSimplex n) : RentCoordinates n) ∈ v.cell.realization := by
        rw [SimplexFacet.realization_eq_segment_of_vertices_eq_pair v.cell hvverts]
        simpa [section5StartVertex] using ha_seg
      have ha_τv_real :
          ((a : RentSimplex n) : RentCoordinates n) ∈ τv.realization :=
        SimplexFacet.realization_mono_of_isSubface hτv_sub ha_vcell
      have ha_τv : a ∈ τv.vertices :=
        SimplexTriangulation.mem_vertices_of_vertex_mem_realization hτv hτu ha_τu ha_τv_real
      have hpair_sub : ({section5StartVertex n, b} : Finset (RentSimplex n)) ⊆ τv.vertices := by
        simpa [SimplexFacet.IsSubfaceOf, hvverts] using hτv_sub
      have hpair_image :
          (((↑) : RentSimplex n → RentCoordinates n) '' ↑({section5StartVertex n, b} :
            Finset (RentSimplex n))) =
            ({prefixBarycenter n 1, ((b : RentSimplex n) : RentCoordinates n)} :
              Set (RentCoordinates n)) := by
        ext z
        constructor
        · rintro ⟨c, hc, rfl⟩
          simp [Finset.coe_insert, Finset.coe_singleton, section5StartVertex] at hc
          rcases hc with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        · intro hz
          rcases hz with rfl | rfl
          · exact ⟨section5StartVertex n, by simp [Finset.coe_insert, Finset.coe_singleton],
              rfl⟩
          · exact ⟨b, by simp [Finset.coe_insert, Finset.coe_singleton], rfl⟩
      have ha_pair_hull :
          ((a : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ
            (((↑) : RentSimplex n → RentCoordinates n) ''
              ↑({section5StartVertex n, b} : Finset (RentSimplex n))) := by
        rw [hpair_image]
        rwa [convexHull_pair]
      have ha_pair : a ∈ ({section5StartVertex n, b} : Finset (RentSimplex n)) :=
        SimplexTriangulation.mem_subset_of_vertex_mem_convexHull hτv hpair_sub ha_τv ha_pair_hull
      have : a = b := by
        simpa [ha_ne] using ha_pair
      exact False.elim (hab this)
    · have hb_seg :
          ((b : RentSimplex n) : RentCoordinates n) ∈
            segment ℝ (prefixBarycenter n 1) ((a : RentSimplex n) : RentCoordinates n) :=
        mem_segment_prefixBarycenter_one_of_boundary_zero_order hb_face ha_face ha_ne_coord hab'
      have hb_ucell :
          ((b : RentSimplex n) : RentCoordinates n) ∈ u.cell.realization := by
        rw [SimplexFacet.realization_eq_segment_of_vertices_eq_pair u.cell huverts]
        simpa [section5StartVertex] using hb_seg
      have hb_τu_real :
          ((b : RentSimplex n) : RentCoordinates n) ∈ τu.realization :=
        SimplexFacet.realization_mono_of_isSubface hτu_sub hb_ucell
      have hb_τu : b ∈ τu.vertices :=
        SimplexTriangulation.mem_vertices_of_vertex_mem_realization hτu hτv hb_τv hb_τu_real
      have hpair_sub : ({section5StartVertex n, a} : Finset (RentSimplex n)) ⊆ τu.vertices := by
        simpa [SimplexFacet.IsSubfaceOf, huverts] using hτu_sub
      have hpair_image :
          (((↑) : RentSimplex n → RentCoordinates n) '' ↑({section5StartVertex n, a} :
            Finset (RentSimplex n))) =
            ({prefixBarycenter n 1, ((a : RentSimplex n) : RentCoordinates n)} :
              Set (RentCoordinates n)) := by
        ext z
        constructor
        · rintro ⟨c, hc, rfl⟩
          simp [Finset.coe_insert, Finset.coe_singleton, section5StartVertex] at hc
          rcases hc with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        · intro hz
          rcases hz with rfl | rfl
          · exact ⟨section5StartVertex n, by simp [Finset.coe_insert, Finset.coe_singleton],
              rfl⟩
          · exact ⟨a, by simp [Finset.coe_insert, Finset.coe_singleton], rfl⟩
      have hb_pair_hull :
          ((b : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ
            (((↑) : RentSimplex n → RentCoordinates n) ''
              ↑({section5StartVertex n, a} : Finset (RentSimplex n))) := by
        rw [hpair_image]
        rwa [convexHull_pair]
      have hb_pair : b ∈ ({section5StartVertex n, a} : Finset (RentSimplex n)) :=
        SimplexTriangulation.mem_subset_of_vertex_mem_convexHull hτu hpair_sub hb_τu hb_pair_hull
      have : b = a := by
        simpa [hb_ne] using hb_pair
      exact False.elim (hab this.symm)

theorem existsUnique_section5_levelOne_start_subface_of_exists {n : ℕ} [NeZero n]
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
  have hv_node : IsSection5GraphNode T f v.1.1 := (mem_section5Nodes_iff).mp v.1.2
  have hw_node : IsSection5GraphNode T f w.1.1 := (mem_section5Nodes_iff).mp w.1.2
  apply Subtype.ext
  apply Subtype.ext
  exact (section5_levelOne_start_subface_unique hv_node hw_node hv.1 hw.1 hv.2 hw.2).symm

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

/-- The actual start component, now canonically available from face preservation. -/
abbrev section5CanonicalStartComponent {n : ℕ} [NeZero n] {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f) :=
  section5StartComponent (T := T) (f := f) hf.section5StartNode_isGraphNode

/-- The Section 5 graph on the canonical start component. -/
abbrev section5CanonicalStartComponentGraph {n : ℕ} [NeZero n] {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f) :=
  section5StartComponentGraph (T := T) (f := f) (hstart := hf.section5StartNode_isGraphNode)

/-- The start node, viewed in the canonical start component attached to a face-respecting map. -/
abbrev section5CanonicalStartVertexInComponent {n : ℕ} [NeZero n] {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f) :=
  section5StartVertexInComponent (T := T) (f := f) (hstart := hf.section5StartNode_isGraphNode)

/-- The degree function on the canonical start component. -/
abbrev section5CanonicalStartComponentNodeDegree {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f)
    (v : section5CanonicalStartComponent (T := T) (f := f) hf) : ℕ :=
  section5StartComponentNodeDegree (hstart := hf.section5StartNode_isGraphNode) v

theorem IsFaceRespecting.section5CanonicalStartGraph_adj_iff {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f)
    {v : section5CanonicalStartComponent (T := T) (f := f) hf} :
    (section5CanonicalStartComponentGraph (T := T) (f := f) hf).Adj
        (section5CanonicalStartVertexInComponent (T := T) (f := f) hf) v ↔
      v.1.1.level = 1 ∧ (section5StartCell n).IsSubfaceOf v.1.1.cell := by
  constructor
  · intro hv
    rcases (section5StartComponentGraph_adj_start_iff
      (hstart := hf.section5StartNode_isGraphNode)).mp hv with ⟨hlevel, hsub, _⟩
    exact ⟨hlevel, hsub⟩
  · rintro ⟨hlevel, hsub⟩
    exact (section5StartComponentGraph_adj_start_iff
      (hstart := hf.section5StartNode_isGraphNode)).mpr
        ⟨hlevel, hsub, hf.startCell_hits_prefixBarycenter⟩

/-- The remaining start-boundary input can now be phrased canonically from face preservation:
there is a unique level-1 graph node in the actual start component whose cell contains `e₁`. -/
structure Section5CanonicalBoundarySuccessorData {n : ℕ} [NeZero n]
    (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n)
    (hf : IsFaceRespecting f) : Prop where
  exists_unique_levelOne_successor :
    ∃! v : section5CanonicalStartComponent (T := T) (f := f) hf,
      v.1.1.level = 1 ∧ (section5StartCell n).IsSubfaceOf v.1.1.cell

theorem IsFaceRespecting.section5CanonicalBoundarySuccessorData_of_exists {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f)
    (hex :
      ∃ v : section5CanonicalStartComponent (T := T) (f := f) hf,
        v.1.1.level = 1 ∧ (section5StartCell n).IsSubfaceOf v.1.1.cell) :
    Section5CanonicalBoundarySuccessorData T f hf := by
  refine ⟨?_⟩
  exact existsUnique_section5_levelOne_start_subface_of_exists
    (hstart := hf.section5StartNode_isGraphNode) hex

theorem IsFaceRespecting.exists_levelOne_canonical_start_subface {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} (hn : 2 ≤ n)
    (hf : IsFaceRespecting f) :
    ∃ v : section5CanonicalStartComponent (T := T) (f := f) hf,
      v.1.1.level = 1 ∧ (section5StartCell n).IsSubfaceOf v.1.1.cell := by
  classical
  let B : Finset (RentSimplex n) :=
    T.vertices.filter fun v => v ∈ coordinateFace (prefixRooms n 2) ∧ v ≠ section5StartVertex n
  have hB_nonempty : B.Nonempty := by
    rcases exists_boundaryEdgeVertex_ne_start hn T with ⟨v, hvT, hvFace, hvNe⟩
    exact ⟨v, Finset.mem_filter.mpr ⟨hvT, hvFace, hvNe⟩⟩
  let c : ℝ :=
    B.sup' hB_nonempty fun v => ((v : RentSimplex n) : RentCoordinates n) (0 : RoomIndex n)
  have hc_lt_one : c < 1 := by
    rcases Finset.exists_mem_eq_sup' hB_nonempty
        (fun v => ((v : RentSimplex n) : RentCoordinates n) (0 : RoomIndex n)) with
      ⟨vmax, hvmaxB, hc_eq⟩
    have hvmax_face : vmax ∈ coordinateFace (prefixRooms n 2) := (Finset.mem_filter.mp hvmaxB).2.1
    have hvmax_ne : vmax ≠ section5StartVertex n := (Finset.mem_filter.mp hvmaxB).2.2
    have hvmax_face' :
        ((vmax : RentSimplex n) : RentCoordinates n) ∈ ambientCoordinateFace (prefixRooms n 2) :=
      mem_ambientCoordinateFace_of_mem_coordinateFace hvmax_face
    have hvmax_ne' :
        ((vmax : RentSimplex n) : RentCoordinates n) ≠ prefixBarycenter n 1 := by
      intro h
      apply hvmax_ne
      apply Subtype.ext
      simpa [section5StartVertex] using h
    have hvmax_lt :
        ((vmax : RentSimplex n) : RentCoordinates n) (0 : RoomIndex n) < 1 :=
      ambientCoordinateFace_prefixRooms_two_apply_zero_lt_one_of_ne_start hvmax_face' hvmax_ne'
    simpa [c, hc_eq] using hvmax_lt
  have hc_nonneg : 0 ≤ c := by
    rcases Finset.exists_mem_eq_sup' hB_nonempty
        (fun v => ((v : RentSimplex n) : RentCoordinates n) (0 : RoomIndex n)) with
      ⟨vmax, _hvmaxB, hc_eq⟩
    have : 0 ≤ ((vmax : RentSimplex n) : RentCoordinates n) (0 : RoomIndex n) := vmax.2.1 _
    simpa [c, hc_eq] using this
  let z : RentCoordinates n :=
    AffineMap.lineMap (prefixBarycenter n 1) (prefixBarycenter n 2) (1 - c)
  have hz_seg : z ∈ segment ℝ (prefixBarycenter n 1) (prefixBarycenter n 2) := by
    refine ⟨c, 1 - c, hc_nonneg, sub_nonneg.mpr (le_of_lt hc_lt_one), by linarith, ?_⟩
    simp [z, AffineMap.lineMap_apply_module]
  have hz_face : z ∈ ambientCoordinateFace (prefixRooms n 2) := by
    exact (convex_ambientCoordinateFace (prefixRooms n 2)).segment_subset
      prefixBarycenter_one_mem_ambientCoordinateFace_two
      (prefixBarycenter_mem_ambientCoordinateFace (n := n) (k := 2) hn)
      hz_seg
  have hz0_gt : c < z (0 : RoomIndex n) := by
    dsimp [z]
    simp [AffineMap.lineMap_apply_module, prefixBarycenter]
    linarith
  have hz0_lt_one : z (0 : RoomIndex n) < 1 := by
    dsimp [z]
    simp [AffineMap.lineMap_apply_module, prefixBarycenter]
    linarith
  have hz_ne_start : z ≠ prefixBarycenter n 1 := by
    intro hz
    have : z (0 : RoomIndex n) = 1 := by simpa [hz, prefixBarycenter]
    linarith
  let x : RentSimplex n := ⟨z, by simpa [RentSimplex, scaledSimplex] using hz_face.1⟩
  obtain ⟨τ, hτ, hxτ⟩ := T.covers_simplex x
  let s : Finset (RentCoordinates n) :=
    τ.vertices.image fun v : RentSimplex n => ((v : RentSimplex n) : RentCoordinates n)
  have hxconv : ((x : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ (s : Set (RentCoordinates n)) := by
    simpa [s, SimplexFacet.realization, SimplexFacet.pointSet] using hxτ
  obtain ⟨w, hw_nonneg, hw_sum, hw_center⟩ := (Finset.mem_convexHull).mp hxconv
  let supp : Finset (RentCoordinates n) := s.filter fun y => w y ≠ 0
  have hsupp_sum : ∑ y ∈ supp, w y = 1 := by
    calc
      ∑ y ∈ supp, w y = ∑ y ∈ s, w y := by
        simpa [supp] using (Finset.sum_filter_ne_zero (s := s) (f := w))
      _ = 1 := hw_sum
  have hsupp_nonempty : supp.Nonempty := by
    by_contra hsupp
    have : (∑ y ∈ supp, w y) = 0 := by
      simp [Finset.not_nonempty_iff_eq_empty.mp hsupp]
    linarith
  have hsupp_center :
      supp.centerMass w id = ((x : RentSimplex n) : RentCoordinates n) := by
    calc
      supp.centerMass w id = s.centerMass w id := by
        simpa [supp] using (Finset.centerMass_filter_ne_zero (t := s) (w := w) (z := id))
      _ = ((x : RentSimplex n) : RentCoordinates n) := hw_center
  have hsupp_conv :
      ((x : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ (supp : Set (RentCoordinates n)) := by
    rw [← hsupp_center]
    refine Finset.centerMass_id_mem_convexHull supp ?_ ?_
    · intro y hy
      exact hw_nonneg _ (Finset.mem_filter.mp hy).1
    · rw [hsupp_sum]
      norm_num
  have hsupp_boundary :
      ∀ y ∈ supp, y ∈ ambientCoordinateFace (prefixRooms n 2) := by
    intro y hy
    exact point_mem_ambientCoordinateFace_prefixRooms_two_of_nonzero_weight hxτ hz_face
      hw_nonneg hw_sum hw_center (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2
  have hstart_mem_supp : prefixBarycenter n 1 ∈ supp := by
    by_contra hstart_notin
    have hsupp_le_c : ∀ y ∈ supp, y (0 : RoomIndex n) ≤ c := by
      intro y hy
      rcases Finset.mem_image.mp (Finset.mem_filter.mp hy).1 with ⟨v, hvτ, rfl⟩
      have hvT : v ∈ T.vertices := by
        simpa [SimplexTriangulation.vertices] using Finset.mem_biUnion.mpr ⟨τ, hτ, hvτ⟩
      have hvFace : v ∈ coordinateFace (prefixRooms n 2) :=
        mem_coordinateFace_prefixRooms_two_of_mem_ambientCoordinateFace (hsupp_boundary _ hy)
      have hvNe : v ≠ section5StartVertex n := by
        intro hvEq
        apply hstart_notin
        simpa [hvEq] using hy
      have hvB : v ∈ B := Finset.mem_filter.mpr ⟨hvT, hvFace, hvNe⟩
      exact Finset.le_sup' (f := fun v => ((v : RentSimplex n) : RentCoordinates n)
        (0 : RoomIndex n)) hvB
    have hx0_le_sup :
        ((x : RentSimplex n) : RentCoordinates n) (0 : RoomIndex n) ≤
          supp.sup' hsupp_nonempty (fun y => y (0 : RoomIndex n)) := by
      have hp :
          ConvexOn ℝ (Set.univ : Set (RentCoordinates n))
            (LinearMap.proj (R := ℝ) (0 : RoomIndex n)) :=
        (LinearMap.proj (R := ℝ) (0 : RoomIndex n)).convexOn convex_univ
      simpa using
        (ConvexOn.le_sup_of_mem_convexHull (t := supp) (s := (Set.univ : Set (RentCoordinates n)))
          (f := LinearMap.proj (R := ℝ) (0 : RoomIndex n)) hp (by intro y hy; simp) hsupp_conv)
    have hsupp_sup_le_c :
        supp.sup' hsupp_nonempty (fun y => y (0 : RoomIndex n)) ≤ c :=
      Finset.sup'_le hsupp_nonempty _ hsupp_le_c
    have hx0_eq : ((x : RentSimplex n) : RentCoordinates n) (0 : RoomIndex n) = z (0 : RoomIndex n) := rfl
    linarith
  have hstart_vertex_mem : section5StartVertex n ∈ τ.vertices := by
    rcases Finset.mem_image.mp (Finset.mem_filter.mp hstart_mem_supp).1 with ⟨v, hvτ, hvEq⟩
    have : v = section5StartVertex n := by
      apply Subtype.ext
      simpa [section5StartVertex] using hvEq
    simpa [this] using hvτ
  have hother :
      ∃ y ∈ supp, y ≠ prefixBarycenter n 1 := by
    by_contra hno
    have hsupp_subset :
        (supp : Set (RentCoordinates n)) ⊆ {prefixBarycenter n 1} := by
      intro y hy
      simp
      by_contra hy_ne
      exact hno ⟨y, hy, hy_ne⟩
    have hx_eq_start : ((x : RentSimplex n) : RentCoordinates n) = prefixBarycenter n 1 := by
      have hx_singleton :
          ((x : RentSimplex n) : RentCoordinates n) ∈
            convexHull ℝ ({prefixBarycenter n 1} : Set (RentCoordinates n)) :=
        convexHull_mono hsupp_subset hsupp_conv
      simpa [convexHull_singleton] using hx_singleton
    exact hz_ne_start hx_eq_start
  rcases hother with ⟨y, hy_supp, hy_ne⟩
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hy_supp).1 with ⟨vOther, hvOtherτ, rfl⟩
  have hvOther_face : vOther ∈ coordinateFace (prefixRooms n 2) :=
    mem_coordinateFace_prefixRooms_two_of_mem_ambientCoordinateFace (hsupp_boundary _ hy_supp)
  have hvOther_ne : vOther ≠ section5StartVertex n := by
    intro hvEq
    apply hy_ne
    rw [hvEq]
    rfl
  let σ : SimplexFacet n := ⟨{section5StartVertex n, vOther}⟩
  have hσ_subface : σ.IsSubfaceOf τ := by
    intro v hv
    simp [σ] at hv
    rcases hv with rfl | rfl
    · exact hstart_vertex_mem
    · exact hvOtherτ
  have hstart_subface : (section5StartCell n).IsSubfaceOf σ := by
    intro v hv
    have hv' : v = section5StartVertex n := by simpa [section5StartCell] using hv
    subst hv'
    simp [σ]
  let u : Section5Node n := ⟨1, σ⟩
  have hu_node : IsSection5GraphNode T f u := by
    refine ⟨by omega, ⟨τ, hτ, hσ_subface⟩, by
      simpa [u, σ, Finset.pair_comm] using Finset.card_pair hvOther_ne, ?_, ?_⟩
    · intro v hv
      simp [u, σ] at hv
      rcases hv with rfl | rfl
      · exact coordinateFace_mono (prefixRooms_mono (by omega))
          (section5StartVertex_mem_coordinateFace n)
      · exact hvOther_face
    · refine ⟨prefixBarycenter n 1, ?_, ?_⟩
      · rw [← hf.map_section5StartVertex_eq_prefixBarycenter]
        rw [FacetImageHull]
        refine subset_convexHull ℝ _ ?_
        exact Set.mem_image_of_mem (fun v : RentSimplex n => f v) <| by
          simp [u, σ]
      · simpa [prefixBarycenterSegment] using
          left_mem_segment ℝ (prefixBarycenter n 1) (prefixBarycenter n 2)
  have hu_adj : Section5Adjacent f (section5StartNode n) u := by
    exact section5Adjacent_startNode_iff.mpr ⟨rfl, hstart_subface, hf.startCell_hits_prefixBarycenter⟩
  let unode : section5Nodes T f := ⟨u, hu_node.mem_section5Nodes⟩
  have hreach :
      (section5NodeGraph T f).Reachable
        (section5StartNodeInNodes hf.section5StartNode_isGraphNode) unode := by
    exact SimpleGraph.Adj.reachable <| by
      simpa [section5NodeGraph, section5SimpleGraph, unode, u] using hu_adj
  refine ⟨⟨unode, (mem_section5StartComponent_iff_reachable
    (hstart := hf.section5StartNode_isGraphNode)).2 hreach⟩, ?_⟩
  exact ⟨rfl, hstart_subface⟩

theorem IsFaceRespecting.section5CanonicalBoundarySuccessorData_of_two_le {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} (hn : 2 ≤ n)
    (hf : IsFaceRespecting f) :
    Section5CanonicalBoundarySuccessorData T f hf := by
  exact hf.section5CanonicalBoundarySuccessorData_of_exists
    (hf.exists_levelOne_canonical_start_subface hn)

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

theorem section5StartComponentGraph_adj_levels {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {u v : section5StartComponent hstart}
    (huv : (section5StartComponentGraph hstart).Adj u v) :
    u.1.1.level + 1 = v.1.1.level ∨ v.1.1.level + 1 = u.1.1.level := by
  rw [section5StartComponentGraph_adj_iff hstart] at huv
  rcases huv with huv | huv
  · exact Or.inl huv.1
  · exact Or.inr huv.1

def section5LowerNeighbors {n : ℕ} [NeZero n] {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (v : section5StartComponent hstart) : Finset (section5StartComponent hstart) := by
  classical
  exact Finset.univ.filter fun u : section5StartComponent hstart =>
    (section5StartComponentGraph hstart).Adj u v ∧ u.1.1.level + 1 = v.1.1.level

def section5UpperNeighbors {n : ℕ} [NeZero n] {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (v : section5StartComponent hstart) : Finset (section5StartComponent hstart) := by
  classical
  exact Finset.univ.filter fun w : section5StartComponent hstart =>
    (section5StartComponentGraph hstart).Adj v w ∧ v.1.1.level + 1 = w.1.1.level

def section5BoundaryNeighbors {n : ℕ} [NeZero n] {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (v : section5StartComponent hstart) : Finset (section5StartComponent hstart) := by
  classical
  exact section5LowerNeighbors v ∪ section5UpperNeighbors v

@[simp]
theorem mem_section5LowerNeighbors_iff {n : ℕ} [NeZero n] {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {u v : section5StartComponent hstart} :
    u ∈ section5LowerNeighbors v ↔
      (section5StartComponentGraph hstart).Adj u v ∧ u.1.1.level + 1 = v.1.1.level := by
  classical
  simp [section5LowerNeighbors]

@[simp]
theorem mem_section5UpperNeighbors_iff {n : ℕ} [NeZero n] {T : SimplexTriangulation n}
    {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {v w : section5StartComponent hstart} :
    w ∈ section5UpperNeighbors v ↔
      (section5StartComponentGraph hstart).Adj v w ∧ v.1.1.level + 1 = w.1.1.level := by
  classical
  simp [section5UpperNeighbors]

@[simp]
theorem mem_section5BoundaryNeighbors_iff {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {v w : section5StartComponent hstart} :
    w ∈ section5BoundaryNeighbors v ↔ (section5StartComponentGraph hstart).Adj v w := by
  classical
  constructor
  · intro hw
    rw [section5BoundaryNeighbors, Finset.mem_union] at hw
    rcases hw with hw | hw
    · exact (mem_section5LowerNeighbors_iff.mp hw).1.symm
    · exact (mem_section5UpperNeighbors_iff.mp hw).1
  · intro hw
    rcases section5StartComponentGraph_adj_levels (hstart := hstart) hw with hlevel | hlevel
    · rw [section5BoundaryNeighbors, Finset.mem_union]
      exact Or.inr <| (mem_section5UpperNeighbors_iff).mpr ⟨hw, hlevel⟩
    · rw [section5BoundaryNeighbors, Finset.mem_union]
      exact Or.inl <| (mem_section5LowerNeighbors_iff).mpr ⟨hw.symm, hlevel⟩

structure Section5BoundarySegmentGenericity {n : ℕ} [NeZero n]
    (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n)
    (hstart : IsSection5GraphNode T f (section5StartNode n)) : Prop where
  boundaryNeighbors_card_le_two :
    ∀ v : section5StartComponent hstart,
      (section5BoundaryNeighbors v).card ≤ 2
  single_boundary_neighbor_is_endpoint :
    ∀ v : section5StartComponent hstart,
      v ≠ section5StartVertexInComponent hstart →
        (section5BoundaryNeighbors v).card = 1 →
          IsSection5Endpoint T f v.1.1

/-- Global simplex-slice genericity on the real start component. The lower field is phrased using
a minimal segment-hitting subface inside each cell so it can be discharged from local slice
geometry and then fed directly to the existing lower-step constructor. -/
structure Section5SimplexSliceGenericity {n : ℕ} [NeZero n]
    (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n)
    (hstart : IsSection5GraphNode T f (section5StartNode n)) where
  lower_minimal_slice_face_of_ne_start :
    ∀ v : section5StartComponent hstart,
      v ≠ section5StartVertexInComponent hstart →
        Section5MinimalSliceFaceData v.1.1 f
  upper_step_unique :
    ∀ {v u w : section5StartComponent hstart},
      Section5Step f v.1.1 u.1.1 →
      Section5Step f v.1.1 w.1.1 →
        u = w
  no_upper_step_is_endpoint :
    ∀ v : section5StartComponent hstart,
      (¬ ∃ w : section5StartComponent hstart, Section5Step f v.1.1 w.1.1) →
        IsSection5Endpoint T f v.1.1

/-- A slightly richer local package than `Section5SimplexSliceGenericity`: for each non-start
node, choose a minimal segment-hitting face together with a lower boundary face of that minimal
face carrying an actual slice point. The local theorem
`Section5MinimalSliceLowerBoundaryGeometry.toMinimalSliceFaceData` collapses this geometry back to
the simpler codimension-one data used by the existing perturbation bridge. -/
structure Section5SimplexSliceBoundaryGeometry {n : ℕ} [NeZero n]
    (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n)
    (hstart : IsSection5GraphNode T f (section5StartNode n)) where
  lower_boundary_geometry_of_ne_start :
    ∀ v : section5StartComponent hstart,
      v ≠ section5StartVertexInComponent hstart →
        Section5MinimalSliceLowerBoundaryGeometry v.1.1 f
  upper_step_unique :
    ∀ {v u w : section5StartComponent hstart},
      Section5Step f v.1.1 u.1.1 →
      Section5Step f v.1.1 w.1.1 →
        u = w
  no_upper_step_is_endpoint :
    ∀ v : section5StartComponent hstart,
      (¬ ∃ w : section5StartComponent hstart, Section5Step f v.1.1 w.1.1) →
        IsSection5Endpoint T f v.1.1

/-- Exact support-layer version of the paper's quoted genericity sentence in lower-boundary-face
language: every non-start cell has minimal segment-hitting data with one codimension-one lower
entry face carrying a point on the barycenter segment, while the upper continuation and endpoint
fields remain in the step language. -/
structure Section5BoundaryFaceGenericity {n : ℕ} [NeZero n]
    (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n)
    (hstart : IsSection5GraphNode T f (section5StartNode n)) where
  lower_boundary_face_data_of_ne_start :
    ∀ v : section5StartComponent hstart,
      v ≠ section5StartVertexInComponent hstart →
        Section5MinimalSliceLowerBoundaryFaceData v.1.1 f
  upper_step_unique :
    ∀ {v u w : section5StartComponent hstart},
      Section5Step f v.1.1 u.1.1 →
      Section5Step f v.1.1 w.1.1 →
        u = w
  no_upper_step_is_endpoint :
    ∀ v : section5StartComponent hstart,
      (¬ ∃ w : section5StartComponent hstart, Section5Step f v.1.1 w.1.1) →
        IsSection5Endpoint T f v.1.1

/-- Direct global genericity in the manuscript's lower-entry-face language: every non-start cell
is entered through a lower codimension-one face whose image contains the next prefix barycenter,
while the upper continuation and endpoint fields remain in step language. -/
structure Section5EntryFaceGenericity {n : ℕ} [NeZero n]
    (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n)
    (hstart : IsSection5GraphNode T f (section5StartNode n)) where
  lower_entry_face_of_ne_start :
    ∀ v : section5StartComponent hstart,
      v ≠ section5StartVertexInComponent hstart →
        Section5LowerEntryFaceData v.1.1 f
  upper_step_unique :
    ∀ {v u w : section5StartComponent hstart},
      Section5Step f v.1.1 u.1.1 →
      Section5Step f v.1.1 w.1.1 →
        u = w
  no_upper_step_is_endpoint :
    ∀ v : section5StartComponent hstart,
      (¬ ∃ w : section5StartComponent hstart, Section5Step f v.1.1 w.1.1) →
        IsSection5Endpoint T f v.1.1

theorem Section5EntryFaceGenericity.lower_entry_face_of_ne_start_canonical {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hentry : Section5EntryFaceGenericity T f hstart)
    (v : section5StartComponent hstart)
    (hv : v ≠ section5StartVertexInComponent hstart) :
    (section5LowerPrefixVertices v.1.1).card = v.1.1.level ∧
      FacetImageContains f (⟨section5LowerPrefixVertices v.1.1⟩ : SimplexFacet n)
        (prefixBarycenter n v.1.1.level) := by
  have hv_node : IsSection5GraphNode T f v.1.1 := (mem_section5Nodes_iff).mp v.1.2
  exact
    (section5LowerEntryFaceData_nonempty_iff_card_eq_and_facetImageContains_lowerPrefixVertices
      hv_node).mp
      ⟨hentry.lower_entry_face_of_ne_start v hv⟩

theorem Section5SimplexSliceGenericity.exists_point_mem_section5CellSlice_and_mem_coordinateFace
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hslice : Section5SimplexSliceGenericity T f hstart)
    (hfpl : IsPiecewiseAffineOn T f)
    (v : section5StartComponent hstart)
    (hv : v ≠ section5StartVertexInComponent hstart) :
    ∃ x : RentSimplex n,
      x ∈ section5CellSlice v.1.1 f ∧
        x ∈ coordinateFace (prefixRooms n v.1.1.level) := by
  have hv_node : IsSection5GraphNode T f v.1.1 := (mem_section5Nodes_iff).mp v.1.2
  exact
    (hslice.lower_minimal_slice_face_of_ne_start v hv).exists_point_mem_slice_and_mem_coordinateFace
      hfpl hv_node

theorem Section5SimplexSliceGenericity.card_eq_lowerPrefixVertices_and_exists_point
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hslice : Section5SimplexSliceGenericity T f hstart)
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f)
    (v : section5StartComponent hstart)
    (hv : v ≠ section5StartVertexInComponent hstart) :
    (section5LowerPrefixVertices v.1.1).card = v.1.1.level ∧
      ∃ x : RentSimplex n,
        x ∈ section5CellSlice v.1.1 f ∧
          x ∈ coordinateFace (prefixRooms n v.1.1.level) := by
  have hv_node : IsSection5GraphNode T f v.1.1 := (mem_section5Nodes_iff).mp v.1.2
  obtain ⟨u, huStep⟩ :=
    (hslice.lower_minimal_slice_face_of_ne_start v hv).exists_startComponentLowerStep hf hfpl hv
  have hu_node : IsSection5GraphNode T f u.1.1 := (mem_section5Nodes_iff).mp u.1.2
  exact hfpl.section5Step_card_eq_lowerPrefixVertices_and_exists_point hv_node hu_node huStep

theorem Section5SimplexSliceBoundaryGeometry.card_eq_lowerPrefixVertices_and_exists_point
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgeom : Section5SimplexSliceBoundaryGeometry T f hstart)
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f)
    (v : section5StartComponent hstart)
    (hv : v ≠ section5StartVertexInComponent hstart) :
    (section5LowerPrefixVertices v.1.1).card = v.1.1.level ∧
      ∃ x : RentSimplex n,
        x ∈ section5CellSlice v.1.1 f ∧
          x ∈ coordinateFace (prefixRooms n v.1.1.level) := by
  have hv_node : IsSection5GraphNode T f v.1.1 := (mem_section5Nodes_iff).mp v.1.2
  have hv_level : 0 < v.1.1.level := section5StartComponent_pos_level_of_ne_start hv
  exact
    (hgeom.lower_boundary_geometry_of_ne_start v hv).card_eq_lowerPrefixVertices_and_exists_point
      hf hfpl hv_node hv_level

def Section5BoundaryFaceGenericity.toSimplexSliceBoundaryGeometry {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hface : Section5BoundaryFaceGenericity T f hstart) :
    Section5SimplexSliceBoundaryGeometry T f hstart := by
  refine ⟨?_, hface.upper_step_unique, hface.no_upper_step_is_endpoint⟩
  intro v hv
  have hv_node : IsSection5GraphNode T f v.1.1 := (mem_section5Nodes_iff).mp v.1.2
  have hv_level : 0 < v.1.1.level := section5StartComponent_pos_level_of_ne_start hv
  exact (hface.lower_boundary_face_data_of_ne_start v hv).toLowerBoundaryGeometry
    hfpl hv_node hv_level

def Section5SimplexSliceBoundaryGeometry.toSimplexSliceGenericity {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hfpl : IsPiecewiseAffineOn T f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgeom : Section5SimplexSliceBoundaryGeometry T f hstart) :
    Section5SimplexSliceGenericity T f hstart := by
  refine ⟨?_, hgeom.upper_step_unique, hgeom.no_upper_step_is_endpoint⟩
  intro v hv
  have hv_node : IsSection5GraphNode T f v.1.1 := (mem_section5Nodes_iff).mp v.1.2
  have hv_level : 0 < v.1.1.level := section5StartComponent_pos_level_of_ne_start hv
  exact (hgeom.lower_boundary_geometry_of_ne_start v hv).toMinimalSliceFaceData
    hfpl hv_node hv_level

theorem section5LowerNeighbors_eq_singleton_of_ne_start {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hlower :
      ∀ v : section5StartComponent hstart,
        v ≠ section5StartVertexInComponent hstart →
          ∃ u : section5StartComponent hstart,
            (section5StartComponentGraph hstart).Adj u v ∧
              u.1.1.level + 1 = v.1.1.level)
    {v : section5StartComponent hstart}
    (hv : v ≠ section5StartVertexInComponent hstart) :
    ∃ u : section5StartComponent hstart, section5LowerNeighbors v = {u} := by
  classical
  rcases hlower v hv with ⟨u, huAdj, huLevel⟩
  refine ⟨u, Finset.ext ?_⟩
  intro x
  constructor
  · intro hx
    have hxAdj : (section5StartComponentGraph hstart).Adj x v :=
      (mem_section5LowerNeighbors_iff).mp hx |>.1
    have hxLevel : x.1.1.level + 1 = v.1.1.level :=
      (mem_section5LowerNeighbors_iff).mp hx |>.2
    have hxEq : x = u :=
      section5StartComponentGraph_lower_neighbor_unique hxAdj hxLevel huAdj huLevel
    simp [hxEq]
  · intro hx
    have hx' : x = u := by simpa using hx
    subst hx'
    exact (mem_section5LowerNeighbors_iff).mpr ⟨huAdj, huLevel⟩

theorem section5UpperNeighbors_eq_empty_of_noUpper {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {v : section5StartComponent hstart}
    (hno :
      ¬ ∃ w : section5StartComponent hstart,
        (section5StartComponentGraph hstart).Adj v w ∧
          v.1.1.level + 1 = w.1.1.level) :
    section5UpperNeighbors v = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  exact hno ⟨w, (mem_section5UpperNeighbors_iff).mp hw⟩

theorem section5LowerNeighbors_card_le_one {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (v : section5StartComponent hstart) :
    (section5LowerNeighbors v).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro u hu w hw
  exact section5StartComponentGraph_lower_neighbor_unique
    (mem_section5LowerNeighbors_iff.mp hu).1
    (mem_section5LowerNeighbors_iff.mp hu).2
    (mem_section5LowerNeighbors_iff.mp hw).1
    (mem_section5LowerNeighbors_iff.mp hw).2

theorem section5LowerUpperNeighbors_disjoint {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (v : section5StartComponent hstart) :
    Disjoint (section5LowerNeighbors v) (section5UpperNeighbors v) := by
  classical
  rw [Finset.disjoint_left]
  intro u hu hu'
  have huLevel : u.1.1.level + 1 = v.1.1.level :=
    (mem_section5LowerNeighbors_iff.mp hu).2
  have huLevel' : v.1.1.level + 1 = u.1.1.level :=
    (mem_section5UpperNeighbors_iff.mp hu').2
  have : u.1.1.level + 1 + 1 = u.1.1.level := by
    simpa [huLevel, Nat.add_assoc] using huLevel'
  omega

theorem section5BoundaryNeighbors_card_eq_lower_add_upper {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (v : section5StartComponent hstart) :
    (section5BoundaryNeighbors v).card =
      (section5LowerNeighbors v).card + (section5UpperNeighbors v).card := by
  classical
  rw [section5BoundaryNeighbors, Finset.card_union_of_disjoint]
  exact section5LowerUpperNeighbors_disjoint v

theorem section5BoundaryNeighbors_card_le_two_of_upper_card_le_one {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    {v : section5StartComponent hstart}
    (hupper : (section5UpperNeighbors v).card ≤ 1) :
    (section5BoundaryNeighbors v).card ≤ 2 := by
  rw [section5BoundaryNeighbors_card_eq_lower_add_upper]
  have hlower : (section5LowerNeighbors v).card ≤ 1 := section5LowerNeighbors_card_le_one v
  omega

theorem section5UpperNeighbors_card_le_one_of_step_unique {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hupper :
      ∀ {v u w : section5StartComponent hstart},
        Section5Step f v.1.1 u.1.1 →
        Section5Step f v.1.1 w.1.1 →
          u = w)
    (v : section5StartComponent hstart) :
    (section5UpperNeighbors v).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro u hu w hw
  have huAdj : (section5StartComponentGraph hstart).Adj v u :=
    (mem_section5UpperNeighbors_iff.mp hu).1
  have huLevel : v.1.1.level + 1 = u.1.1.level :=
    (mem_section5UpperNeighbors_iff.mp hu).2
  have hwAdj : (section5StartComponentGraph hstart).Adj v w :=
    (mem_section5UpperNeighbors_iff.mp hw).1
  have hwLevel : v.1.1.level + 1 = w.1.1.level :=
    (mem_section5UpperNeighbors_iff.mp hw).2
  have huStep : Section5Step f v.1.1 u.1.1 := by
    rcases (section5StartComponentGraph_adj_iff hstart).mp huAdj with huStep | huuStep
    · exact huStep
    · have hcontra : v.1.1.level + 1 + 1 = v.1.1.level := by
        simpa [huLevel, Nat.add_assoc] using huuStep.1
      omega
  have hwStep : Section5Step f v.1.1 w.1.1 := by
    rcases (section5StartComponentGraph_adj_iff hstart).mp hwAdj with hwStep | hwwStep
    · exact hwStep
    · have hcontra : v.1.1.level + 1 + 1 = v.1.1.level := by
        simpa [hwLevel, Nat.add_assoc] using hwwStep.1
      omega
  exact hupper huStep hwStep

/-- Minimal perturbation/genericity input in the manuscript's step-level language: every non-start
Section 5 cell is entered through a lower codimension-one face, has at most one upper
continuation along the next barycenter-chain segment, and if there is no such continuation then
the cell already hits the final barycenter. -/
structure Section5PerturbationGenericity {n : ℕ} [NeZero n]
    (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n)
    (hstart : IsSection5GraphNode T f (section5StartNode n)) : Prop where
  lower_step_exists_of_ne_start :
    ∀ v : section5StartComponent hstart,
      v ≠ section5StartVertexInComponent hstart →
        ∃ u : section5StartComponent hstart, Section5Step f u.1.1 v.1.1
  upper_step_unique :
    ∀ {v u w : section5StartComponent hstart},
      Section5Step f v.1.1 u.1.1 →
      Section5Step f v.1.1 w.1.1 →
        u = w
  no_upper_step_is_endpoint :
    ∀ v : section5StartComponent hstart,
      (¬ ∃ w : section5StartComponent hstart, Section5Step f v.1.1 w.1.1) →
        IsSection5Endpoint T f v.1.1

/-- A local 1-dimensional-cell-complex package for the real Section 5 start component.
It records that every non-start node is entered from a unique lower-level neighbor, each node has
at most one higher-level continuation, and a node with no higher-level continuation already hits
the final barycenter. -/
structure Section5OneComplexGeometry {n : ℕ} [NeZero n]
    (T : SimplexTriangulation n) (f : SelfMapOnRentSimplex n)
    (hstart : IsSection5GraphNode T f (section5StartNode n)) : Prop where
  lower_exists_of_ne_start :
    ∀ v : section5StartComponent hstart,
      v ≠ section5StartVertexInComponent hstart →
        ∃ u : section5StartComponent hstart,
          (section5StartComponentGraph hstart).Adj u v ∧
            u.1.1.level + 1 = v.1.1.level
  lower_unique :
    ∀ {u w v : section5StartComponent hstart},
      (section5StartComponentGraph hstart).Adj u v →
      u.1.1.level + 1 = v.1.1.level →
      (section5StartComponentGraph hstart).Adj w v →
      w.1.1.level + 1 = v.1.1.level →
        u = w
  upper_unique :
    ∀ {v u w : section5StartComponent hstart},
      (section5StartComponentGraph hstart).Adj v u →
      v.1.1.level + 1 = u.1.1.level →
      (section5StartComponentGraph hstart).Adj v w →
      v.1.1.level + 1 = w.1.1.level →
        u = w
  no_upper_neighbor_is_endpoint :
    ∀ v : section5StartComponent hstart,
      (¬ ∃ w : section5StartComponent hstart,
        (section5StartComponentGraph hstart).Adj v w ∧
          v.1.1.level + 1 = w.1.1.level) →
        IsSection5Endpoint T f v.1.1

theorem section5OneComplexGeometry_of_remainingFields {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hlower :
      ∀ v : section5StartComponent hstart,
        v ≠ section5StartVertexInComponent hstart →
          ∃ u : section5StartComponent hstart,
            (section5StartComponentGraph hstart).Adj u v ∧
              u.1.1.level + 1 = v.1.1.level)
    (hupper :
      ∀ {v u w : section5StartComponent hstart},
        (section5StartComponentGraph hstart).Adj v u →
        v.1.1.level + 1 = u.1.1.level →
        (section5StartComponentGraph hstart).Adj v w →
        v.1.1.level + 1 = w.1.1.level →
          u = w)
    (hendpoint :
      ∀ v : section5StartComponent hstart,
        (¬ ∃ w : section5StartComponent hstart,
          (section5StartComponentGraph hstart).Adj v w ∧
            v.1.1.level + 1 = w.1.1.level) →
          IsSection5Endpoint T f v.1.1) :
    Section5OneComplexGeometry T f hstart := by
  refine ⟨hlower, ?_, hupper, hendpoint⟩
  intro u w v huv huLevel hwv hwLevel
  exact section5StartComponentGraph_lower_neighbor_unique huv huLevel hwv hwLevel

theorem section5OneComplexGeometry_of_stepGenericity {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hlower :
      ∀ v : section5StartComponent hstart,
        v ≠ section5StartVertexInComponent hstart →
          ∃ u : section5StartComponent hstart, Section5Step f u.1.1 v.1.1)
    (hupper :
      ∀ {v u w : section5StartComponent hstart},
        Section5Step f v.1.1 u.1.1 →
        Section5Step f v.1.1 w.1.1 →
          u = w)
    (hendpoint :
      ∀ v : section5StartComponent hstart,
        (¬ ∃ w : section5StartComponent hstart, Section5Step f v.1.1 w.1.1) →
          IsSection5Endpoint T f v.1.1) :
    Section5OneComplexGeometry T f hstart := by
  refine section5OneComplexGeometry_of_remainingFields ?_ ?_ ?_
  · intro v hv
    rcases hlower v hv with ⟨u, huStep⟩
    refine ⟨u, ?_, huStep.1⟩
    exact (section5StartComponentGraph_adj_iff hstart).mpr (Or.inl huStep)
  · intro v u w huAdj huLevel hwAdj hwLevel
    have huStep : Section5Step f v.1.1 u.1.1 := by
      rcases (section5StartComponentGraph_adj_iff hstart).mp huAdj with huStep | huuStep
      · exact huStep
      · have hcontra : v.1.1.level + 1 + 1 = v.1.1.level := by
          simpa [huLevel, Nat.add_assoc] using huuStep.1
        omega
    have hwStep : Section5Step f v.1.1 w.1.1 := by
      rcases (section5StartComponentGraph_adj_iff hstart).mp hwAdj with hwStep | hwwStep
      · exact hwStep
      · have hcontra : v.1.1.level + 1 + 1 = v.1.1.level := by
          simpa [hwLevel, Nat.add_assoc] using hwwStep.1
        omega
    exact hupper huStep hwStep
  · intro v hno
    apply hendpoint v
    intro hstep
    rcases hstep with ⟨w, hwStep⟩
    exact hno ⟨w, (section5StartComponentGraph_adj_iff hstart).mpr (Or.inl hwStep), hwStep.1⟩

theorem Section5PerturbationGenericity.upperNeighbors_card_le_one {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hpert : Section5PerturbationGenericity T f hstart)
    (v : section5StartComponent hstart) :
    (section5UpperNeighbors v).card ≤ 1 := by
  exact section5UpperNeighbors_card_le_one_of_step_unique hpert.upper_step_unique v

theorem Section5SimplexSliceBoundaryGeometry.toPerturbationGenericity {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgeom : Section5SimplexSliceBoundaryGeometry T f hstart) :
    Section5PerturbationGenericity T f hstart := by
  refine ⟨?_, hgeom.upper_step_unique, hgeom.no_upper_step_is_endpoint⟩
  intro v hv
  have hv_node : IsSection5GraphNode T f v.1.1 := (mem_section5Nodes_iff).mp v.1.2
  have hv_level : 0 < v.1.1.level := section5StartComponent_pos_level_of_ne_start hv
  exact ((hgeom.lower_boundary_geometry_of_ne_start v hv).toMinimalSliceFaceData
    hfpl hv_node hv_level).exists_startComponentLowerStep hf hfpl hv

theorem Section5BoundaryFaceGenericity.toPerturbationGenericity {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hface : Section5BoundaryFaceGenericity T f hstart) :
    Section5PerturbationGenericity T f hstart := by
  exact (hface.toSimplexSliceBoundaryGeometry hfpl).toPerturbationGenericity hf hfpl

theorem Section5EntryFaceGenericity.toPerturbationGenericity {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hentry : Section5EntryFaceGenericity T f hstart) :
    Section5PerturbationGenericity T f hstart := by
  refine ⟨?_, hentry.upper_step_unique, hentry.no_upper_step_is_endpoint⟩
  intro v hv
  exact (hentry.lower_entry_face_of_ne_start v hv).exists_startComponentLowerStep hv

theorem Section5SimplexSliceGenericity.toPerturbationGenericity {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hslice : Section5SimplexSliceGenericity T f hstart) :
    Section5PerturbationGenericity T f hstart := by
  refine ⟨?_, hslice.upper_step_unique, hslice.no_upper_step_is_endpoint⟩
  intro v hv
  exact (hslice.lower_minimal_slice_face_of_ne_start v hv).exists_startComponentLowerStep
    hf hfpl hv

theorem Section5PerturbationGenericity.toBoundarySegmentGenericity {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hpert : Section5PerturbationGenericity T f hstart) :
    Section5BoundarySegmentGenericity T f hstart := by
  refine ⟨?_, ?_⟩
  · intro v
    exact section5BoundaryNeighbors_card_le_two_of_upper_card_le_one
      (hpert.upperNeighbors_card_le_one v)
  · intro v hv hcard
    rcases hpert.lower_step_exists_of_ne_start v hv with ⟨u, huStep⟩
    have huMem : u ∈ section5LowerNeighbors v := by
      exact (mem_section5LowerNeighbors_iff).mpr
        ⟨(section5StartComponentGraph_adj_iff hstart).mpr (Or.inl huStep), huStep.1⟩
    have hlower_pos : 0 < (section5LowerNeighbors v).card := Finset.card_pos.mpr ⟨u, huMem⟩
    have hlower_le : (section5LowerNeighbors v).card ≤ 1 := section5LowerNeighbors_card_le_one v
    have hlower_eq : (section5LowerNeighbors v).card = 1 := by
      omega
    have hupper_eq : (section5UpperNeighbors v).card = 0 := by
      rw [section5BoundaryNeighbors_card_eq_lower_add_upper] at hcard
      omega
    apply hpert.no_upper_step_is_endpoint v
    intro hupper
    rcases hupper with ⟨w, hwStep⟩
    have hwMem : w ∈ section5UpperNeighbors v := by
      exact (mem_section5UpperNeighbors_iff).mpr
        ⟨(section5StartComponentGraph_adj_iff hstart).mpr (Or.inl hwStep), hwStep.1⟩
    have hupper_pos : 0 < (section5UpperNeighbors v).card := Finset.card_pos.mpr ⟨w, hwMem⟩
    omega

theorem Section5EntryFaceGenericity.toBoundarySegmentGenericity {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hentry : Section5EntryFaceGenericity T f hstart) :
    Section5BoundarySegmentGenericity T f hstart := by
  exact hentry.toPerturbationGenericity.toBoundarySegmentGenericity

theorem Section5BoundaryFaceGenericity.toBoundarySegmentGenericity {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hface : Section5BoundaryFaceGenericity T f hstart) :
    Section5BoundarySegmentGenericity T f hstart := by
  exact (hface.toPerturbationGenericity hf hfpl).toBoundarySegmentGenericity

theorem Section5SimplexSliceGenericity.toBoundarySegmentGenericity {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hslice : Section5SimplexSliceGenericity T f hstart) :
    Section5BoundarySegmentGenericity T f hstart := by
  exact (hslice.toPerturbationGenericity hf hfpl).toBoundarySegmentGenericity

theorem Section5SimplexSliceBoundaryGeometry.toBoundarySegmentGenericity {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hfpl : IsPiecewiseAffineOn T f)
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgeom : Section5SimplexSliceBoundaryGeometry T f hstart) :
    Section5BoundarySegmentGenericity T f hstart := by
  exact (hgeom.toPerturbationGenericity hf hfpl).toBoundarySegmentGenericity

theorem Section5PerturbationGenericity.toOneComplexGeometry {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hpert : Section5PerturbationGenericity T f hstart) :
    Section5OneComplexGeometry T f hstart := by
  exact section5OneComplexGeometry_of_stepGenericity
    hpert.lower_step_exists_of_ne_start
    hpert.upper_step_unique
    hpert.no_upper_step_is_endpoint

theorem Section5OneComplexGeometry.degree_le_two {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgeom : Section5OneComplexGeometry T f hstart) :
    ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v ≤ 2 := by
  intro v
  classical
  let neighbors : Finset (section5StartComponent hstart) :=
    Finset.univ.filter fun w : section5StartComponent hstart =>
      (section5StartComponentGraph hstart).Adj v w
  by_cases hlower :
      ∃ u : section5StartComponent hstart,
        (section5StartComponentGraph hstart).Adj u v ∧
          u.1.1.level + 1 = v.1.1.level
  · rcases hlower with ⟨u, huAdj, huLevel⟩
    by_cases hupper :
        ∃ w : section5StartComponent hstart,
          (section5StartComponentGraph hstart).Adj v w ∧
            v.1.1.level + 1 = w.1.1.level
    · rcases hupper with ⟨w, hwAdj, hwLevel⟩
      have hsubset : neighbors ⊆ ({u, w} : Finset (section5StartComponent hstart)) := by
        intro x hx
        have hxAdj : (section5StartComponentGraph hstart).Adj v x := by
          simpa [neighbors] using hx
        rcases section5StartComponentGraph_adj_levels (hstart := hstart) hxAdj with
          hxLevel | hxLevel
        · have hxEq : x = w := hgeom.upper_unique hxAdj hxLevel hwAdj hwLevel
          simp [hxEq]
        · have hxEq : x = u := hgeom.lower_unique hxAdj.symm hxLevel huAdj huLevel
          simp [hxEq]
      calc
        section5StartComponentNodeDegree v = neighbors.card := by rfl
        _ ≤ ({u, w} : Finset (section5StartComponent hstart)).card := Finset.card_le_card hsubset
        _ ≤ 2 := Finset.card_le_two
    · have hsubset : neighbors ⊆ ({u} : Finset (section5StartComponent hstart)) := by
        intro x hx
        have hxAdj : (section5StartComponentGraph hstart).Adj v x := by
          simpa [neighbors] using hx
        rcases section5StartComponentGraph_adj_levels (hstart := hstart) hxAdj with
          hxLevel | hxLevel
        · exact False.elim <| hupper ⟨x, hxAdj, hxLevel⟩
        · have hxEq : x = u := hgeom.lower_unique hxAdj.symm hxLevel huAdj huLevel
          simp [hxEq]
      calc
        section5StartComponentNodeDegree v = neighbors.card := by rfl
        _ ≤ ({u} : Finset (section5StartComponent hstart)).card := Finset.card_le_card hsubset
        _ ≤ 2 := by simp
  · by_cases hupper :
      ∃ w : section5StartComponent hstart,
        (section5StartComponentGraph hstart).Adj v w ∧
          v.1.1.level + 1 = w.1.1.level
    · rcases hupper with ⟨w, hwAdj, hwLevel⟩
      have hsubset : neighbors ⊆ ({w} : Finset (section5StartComponent hstart)) := by
        intro x hx
        have hxAdj : (section5StartComponentGraph hstart).Adj v x := by
          simpa [neighbors] using hx
        rcases section5StartComponentGraph_adj_levels (hstart := hstart) hxAdj with
          hxLevel | hxLevel
        · have hxEq : x = w := hgeom.upper_unique hxAdj hxLevel hwAdj hwLevel
          simp [hxEq]
        · exact False.elim <| hlower ⟨x, hxAdj.symm, hxLevel⟩
      calc
        section5StartComponentNodeDegree v = neighbors.card := by rfl
        _ ≤ ({w} : Finset (section5StartComponent hstart)).card := Finset.card_le_card hsubset
        _ ≤ 2 := by simp
    · have hneighbors_empty : neighbors = ∅ := by
        dsimp [neighbors]
        refine Finset.filter_false_of_mem ?_
        intro x _ hxAdj
        rcases section5StartComponentGraph_adj_levels (hstart := hstart) hxAdj with
          hxLevel | hxLevel
        · exact hupper ⟨x, hxAdj, hxLevel⟩
        · exact hlower ⟨x, hxAdj.symm, hxLevel⟩
      calc
        section5StartComponentNodeDegree v = neighbors.card := by rfl
        _ = 0 := by simp [hneighbors_empty]
        _ ≤ 2 := by omega

theorem Section5OneComplexGeometry.nonstart_degree_one_is_endpoint {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hgeom : Section5OneComplexGeometry T f hstart) :
    ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v = 1 →
      v ≠ section5StartVertexInComponent hstart →
        IsSection5Endpoint T f v.1.1 := by
  intro v hv hne
  classical
  rcases hgeom.lower_exists_of_ne_start v hne with ⟨u, huAdj, huLevel⟩
  rw [section5StartComponentNodeDegree, Finset.card_eq_one] at hv
  rcases hv with ⟨w, hw⟩
  have huMem :
      u ∈ Finset.univ.filter fun x : section5StartComponent hstart =>
        (section5StartComponentGraph hstart).Adj v x := by
    simp [huAdj.symm]
  have huEq : u = w := by simpa [hw] using huMem
  have hnoUpper :
      ¬ ∃ x : section5StartComponent hstart,
        (section5StartComponentGraph hstart).Adj v x ∧
          v.1.1.level + 1 = x.1.1.level := by
    intro hUpper
    rcases hUpper with ⟨x, hxAdj, hxLevel⟩
    have hxMem :
        x ∈ Finset.univ.filter fun y : section5StartComponent hstart =>
          (section5StartComponentGraph hstart).Adj v y := by
      simp [hxAdj]
    have hxEq : x = w := by simpa [hw] using hxMem
    subst hxEq
    subst huEq
    omega
  exact hgeom.no_upper_neighbor_is_endpoint v hnoUpper

theorem section5SegmentGeometry_of_startBoundaryAndOneComplexGeometry {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hstartGeom : Section5StartBoundaryGeometry T f hstart)
    (hcomplex : Section5OneComplexGeometry T f hstart) :
    Section5SegmentGeometry T f hstart := by
  refine ⟨hstartGeom.start_unique_neighbor, hcomplex.degree_le_two, ?_⟩
  exact hcomplex.nonstart_degree_one_is_endpoint

theorem Section5BoundarySegmentGenericity.degree_le_two {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hseg : Section5BoundarySegmentGenericity T f hstart) :
    ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v ≤ 2 := by
  intro v
  classical
  let neighbors : Finset (section5StartComponent hstart) :=
    Finset.univ.filter fun w : section5StartComponent hstart =>
      (section5StartComponentGraph hstart).Adj v w
  have hneighbors : neighbors = section5BoundaryNeighbors v := by
    ext w
    simp [neighbors]
  calc
    section5StartComponentNodeDegree v = neighbors.card := by rfl
    _ = (section5BoundaryNeighbors v).card := by rw [hneighbors]
    _ ≤ 2 := hseg.boundaryNeighbors_card_le_two v

theorem Section5BoundarySegmentGenericity.nonstart_degree_one_is_endpoint {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hseg : Section5BoundarySegmentGenericity T f hstart) :
    ∀ v : section5StartComponent hstart, section5StartComponentNodeDegree v = 1 →
      v ≠ section5StartVertexInComponent hstart →
        IsSection5Endpoint T f v.1.1 := by
  intro v hv hne
  classical
  let neighbors : Finset (section5StartComponent hstart) :=
    Finset.univ.filter fun w : section5StartComponent hstart =>
      (section5StartComponentGraph hstart).Adj v w
  have hneighbors : neighbors = section5BoundaryNeighbors v := by
    ext w
    simp [neighbors]
  have hcard : (section5BoundaryNeighbors v).card = 1 := by
    simpa [section5StartComponentNodeDegree, hneighbors, neighbors] using hv
  exact hseg.single_boundary_neighbor_is_endpoint v hne hcard

theorem section5SegmentGeometry_of_startBoundaryAndBoundarySegmentGenericity {n : ℕ}
    [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    {hstart : IsSection5GraphNode T f (section5StartNode n)}
    (hstartGeom : Section5StartBoundaryGeometry T f hstart)
    (hseg : Section5BoundarySegmentGenericity T f hstart) :
    Section5SegmentGeometry T f hstart := by
  refine ⟨hstartGeom.start_unique_neighbor, hseg.degree_le_two, ?_⟩
  exact hseg.nonstart_degree_one_is_endpoint

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

theorem Section5CanonicalBoundarySuccessorData.toStartBoundaryGeometry {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f)
    (hsucc : Section5CanonicalBoundarySuccessorData T f hf) :
    Section5StartBoundaryGeometry T f hf.section5StartNode_isGraphNode := by
  refine section5StartBoundaryGeometry_of_faceRespectingAndSuccessorData
    (T := T) (f := f) (hstart := hf.section5StartNode_isGraphNode) hf ?_
  exact hsucc.exists_unique_levelOne_successor

theorem Section5CanonicalBoundarySuccessorData.start_unique_neighbor {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f)
    (hsucc : Section5CanonicalBoundarySuccessorData T f hf) :
    ∃! v : section5CanonicalStartComponent (T := T) (f := f) hf,
      (section5CanonicalStartComponentGraph (T := T) (f := f) hf).Adj
        (section5CanonicalStartVertexInComponent (T := T) (f := f) hf) v := by
  rcases hsucc.exists_unique_levelOne_successor with ⟨v, hv, huniq⟩
  refine ⟨v, (hf.section5CanonicalStartGraph_adj_iff).2 hv, ?_⟩
  intro w hw
  exact huniq w ((hf.section5CanonicalStartGraph_adj_iff).1 hw)

theorem Section5CanonicalBoundarySuccessorData.start_degreeOne {n : ℕ} [NeZero n]
    {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n} (hf : IsFaceRespecting f)
    (hsucc : Section5CanonicalBoundarySuccessorData T f hf) :
    section5CanonicalStartComponentNodeDegree (T := T) (f := f) hf
      (section5CanonicalStartVertexInComponent (T := T) (f := f) hf) = 1 := by
  simpa [section5CanonicalStartComponentNodeDegree, section5CanonicalStartVertexInComponent] using
    (hsucc.toStartBoundaryGeometry hf).start_degree_one

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

theorem Section5CanonicalBoundarySuccessorData.exists_targetFacet_of_localDegreeData {n : ℕ}
    [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hsucc : Section5CanonicalBoundarySuccessorData T f hf)
    (hdeg :
      ∀ v : section5CanonicalStartComponent (T := T) (f := f) hf,
        section5CanonicalStartComponentNodeDegree (T := T) (f := f) hf v ≤ 2)
    (hendpoint :
      ∀ v : section5CanonicalStartComponent (T := T) (f := f) hf,
        section5CanonicalStartComponentNodeDegree (T := T) (f := f) hf v = 1 →
          v ≠ section5CanonicalStartVertexInComponent (T := T) (f := f) hf →
            IsSection5Endpoint T f v.1.1) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact (hsucc.toStartBoundaryGeometry hf).exists_targetFacet_of_localDegreeData hf
    (by simpa [section5CanonicalStartComponentNodeDegree] using hdeg)
    (by
      intro v hv hne
      exact hendpoint v (by simpa [section5CanonicalStartComponentNodeDegree] using hv)
        (by simpa [section5CanonicalStartVertexInComponent] using hne))

theorem Section5CanonicalBoundarySuccessorData.exists_targetFacet_of_oneComplexGeometry {n : ℕ}
    [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hsucc : Section5CanonicalBoundarySuccessorData T f hf)
    (hcomplex :
      Section5OneComplexGeometry T f hf.section5StartNode_isGraphNode) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact (section5SegmentGeometry_of_startBoundaryAndOneComplexGeometry
    (T := T) (f := f) (hstart := hf.section5StartNode_isGraphNode)
    (hsucc.toStartBoundaryGeometry hf) hcomplex).exists_targetFacet hf

theorem Section5CanonicalBoundarySuccessorData.exists_targetFacet_of_boundarySegmentGenericity
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hsucc : Section5CanonicalBoundarySuccessorData T f hf)
    (hseg : Section5BoundarySegmentGenericity T f hf.section5StartNode_isGraphNode) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact (section5SegmentGeometry_of_startBoundaryAndBoundarySegmentGenericity
    (T := T) (f := f) (hstart := hf.section5StartNode_isGraphNode)
    (hsucc.toStartBoundaryGeometry hf) hseg).exists_targetFacet hf

theorem Section5CanonicalBoundarySuccessorData.exists_targetFacet_of_stepGenericity
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hsucc : Section5CanonicalBoundarySuccessorData T f hf)
    (hlower :
      ∀ v : section5CanonicalStartComponent (T := T) (f := f) hf,
        v ≠ section5CanonicalStartVertexInComponent (T := T) (f := f) hf →
          ∃ u : section5CanonicalStartComponent (T := T) (f := f) hf, Section5Step f u.1.1 v.1.1)
    (hupper :
      ∀ {v u w : section5CanonicalStartComponent (T := T) (f := f) hf},
        Section5Step f v.1.1 u.1.1 →
        Section5Step f v.1.1 w.1.1 →
          u = w)
    (hendpoint :
      ∀ v : section5CanonicalStartComponent (T := T) (f := f) hf,
        (¬ ∃ w : section5CanonicalStartComponent (T := T) (f := f) hf,
          Section5Step f v.1.1 w.1.1) →
          IsSection5Endpoint T f v.1.1) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact hsucc.exists_targetFacet_of_oneComplexGeometry hf <|
    section5OneComplexGeometry_of_stepGenericity
      (T := T) (f := f) (hstart := hf.section5StartNode_isGraphNode) hlower hupper hendpoint

theorem IsFaceRespecting.exists_barycenter_targetFacet_of_two_le_and_boundarySegmentGenericity
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hn : 2 ≤ n) (hf : IsFaceRespecting f)
    (hseg : Section5BoundarySegmentGenericity T f hf.section5StartNode_isGraphNode) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact Section5CanonicalBoundarySuccessorData.exists_targetFacet_of_boundarySegmentGenericity
    (T := T) (f := f) hf (hf.section5CanonicalBoundarySuccessorData_of_two_le hn) hseg

theorem IsFaceRespecting.exists_barycenter_targetFacet_of_two_le_and_stepGenericity
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hn : 2 ≤ n) (hf : IsFaceRespecting f)
    (hlower :
      ∀ v : section5CanonicalStartComponent (T := T) (f := f) hf,
        v ≠ section5CanonicalStartVertexInComponent (T := T) (f := f) hf →
          ∃ u : section5CanonicalStartComponent (T := T) (f := f) hf, Section5Step f u.1.1 v.1.1)
    (hupper :
      ∀ {v u w : section5CanonicalStartComponent (T := T) (f := f) hf},
        Section5Step f v.1.1 u.1.1 →
        Section5Step f v.1.1 w.1.1 →
          u = w)
    (hendpoint :
      ∀ v : section5CanonicalStartComponent (T := T) (f := f) hf,
        (¬ ∃ w : section5CanonicalStartComponent (T := T) (f := f) hf,
          Section5Step f v.1.1 w.1.1) →
          IsSection5Endpoint T f v.1.1) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact Section5CanonicalBoundarySuccessorData.exists_targetFacet_of_stepGenericity
    (T := T) (f := f) hf (hf.section5CanonicalBoundarySuccessorData_of_two_le hn)
    hlower hupper hendpoint

theorem Section5CanonicalBoundarySuccessorData.exists_targetFacet_of_perturbationGenericity
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f) (hsucc : Section5CanonicalBoundarySuccessorData T f hf)
    (hpert : Section5PerturbationGenericity T f hf.section5StartNode_isGraphNode) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact hsucc.exists_targetFacet_of_stepGenericity hf
    hpert.lower_step_exists_of_ne_start
    hpert.upper_step_unique
    hpert.no_upper_step_is_endpoint

theorem IsFaceRespecting.exists_barycenter_targetFacet_of_two_le_and_perturbationGenericity
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hn : 2 ≤ n) (hf : IsFaceRespecting f)
    (hpert : Section5PerturbationGenericity T f hf.section5StartNode_isGraphNode) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  exact Section5CanonicalBoundarySuccessorData.exists_targetFacet_of_perturbationGenericity
    (T := T) (f := f) hf (hf.section5CanonicalBoundarySuccessorData_of_two_le hn) hpert

theorem IsFaceRespecting.exists_barycenter_targetFacet_of_boundarySegmentGenericity
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f)
    (hseg :
      2 ≤ n → Section5BoundarySegmentGenericity T f hf.section5StartNode_isGraphNode) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  by_cases h1 : n = 1
  · subst h1
    exact hf.exists_barycenter_targetFacet_of_eq_one
  · have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hn : 2 ≤ n := by omega
    exact hf.exists_barycenter_targetFacet_of_two_le_and_boundarySegmentGenericity hn (hseg hn)

theorem IsFaceRespecting.exists_barycenter_targetFacet_of_upperCardLeOneAndEndpointRule
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsFaceRespecting f)
    (hupper :
      ∀ v : section5CanonicalStartComponent (T := T) (f := f) hf,
        (section5UpperNeighbors v).card ≤ 1)
    (hendpoint :
      ∀ v : section5CanonicalStartComponent (T := T) (f := f) hf,
        v ≠ section5CanonicalStartVertexInComponent (T := T) (f := f) hf →
          (section5BoundaryNeighbors v).card = 1 →
            IsSection5Endpoint T f v.1.1) :
    ∃ τ ∈ T.facets,
      FacetImageContains f τ ((rentBarycenter n : RentSimplex n) : RentCoordinates n) := by
  refine hf.exists_barycenter_targetFacet_of_boundarySegmentGenericity ?_
  intro hn
  refine ⟨?_, ?_⟩
  · intro v
    exact section5BoundaryNeighbors_card_le_two_of_upper_card_le_one (hupper v)
  · intro v hv hcard
    exact hendpoint v hv hcard

end Arxiv170207325
