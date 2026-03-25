import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Powerset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
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

end Arxiv170207325
