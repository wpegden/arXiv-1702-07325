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

theorem section5SimpleGraph.exists_other_degreeOne {n : ℕ}
    (nodes : Finset (Section5Node n)) (f : SelfMapOnRentSimplex n) {start : nodes}
    (hstart : section5NodeDegree nodes f start = 1)
    (hdeg : ∀ v : nodes, section5NodeDegree nodes f v ≤ 2) :
    ∃ finish : nodes,
      finish ≠ start ∧ section5NodeDegree nodes f finish = 1 := by
  classical
  let G : SimpleGraph nodes := section5SimpleGraph nodes f
  have hstart' : G.degree start = 1 := by
    rw [← G.card_neighborFinset_eq_degree]
    simpa [section5NodeDegree, G] using hstart
  have hdeg' : ∀ v : nodes, G.degree v ≤ 2 := by
    intro v
    rw [← G.card_neighborFinset_eq_degree]
    simpa [section5NodeDegree, G] using hdeg v
  have hstartOdd : Odd (G.degree start) := by
    rw [hstart']
    decide
  let S : Finset nodes := Finset.univ.filter fun w => w ≠ start ∧ Odd (G.degree w)
  have hodd : Odd S.card := by
    simpa [S] using G.odd_card_odd_degree_vertices_ne start hstartOdd
  obtain ⟨finish, hfinish⟩ := Finset.card_pos.mp hodd.pos
  have hfinish_ne : finish ≠ start := by
    exact (Finset.mem_filter.mp hfinish).2.1
  have hfinishOdd : Odd (G.degree finish) := by
    exact (Finset.mem_filter.mp hfinish).2.2
  have hfinish_deg : G.degree finish = 1 := by
    have hfinish_le : G.degree finish ≤ 2 := hdeg' finish
    have hcases : G.degree finish = 0 ∨ G.degree finish = 1 ∨ G.degree finish = 2 := by
      omega
    rcases hcases with h0 | h1 | h2
    · exfalso
      exact (by decide : ¬ Odd 0) (h0 ▸ hfinishOdd)
    · exact h1
    · exfalso
      exact (by decide : ¬ Odd 2) (h2 ▸ hfinishOdd)
  exact ⟨finish, hfinish_ne, by
    have hcard : ((section5SimpleGraph nodes f).neighborFinset finish).card = 1 := by
      simpa [G] using (G.card_neighborFinset_eq_degree (v := finish)).trans hfinish_deg
    simpa [section5NodeDegree] using hcard⟩

theorem section5SimpleGraph.exists_other_endpoint {n : ℕ}
    (nodes : Finset (Section5Node n)) (f : SelfMapOnRentSimplex n) {start : nodes}
    (hstart : section5NodeDegree nodes f start = 1)
    (hdeg : ∀ v : nodes, section5NodeDegree nodes f v ≤ 2)
    (hconn : (section5SimpleGraph nodes f).Preconnected) :
    ∃ finish : nodes,
      finish ≠ start ∧
      section5NodeDegree nodes f finish = 1 ∧
      (section5SimpleGraph nodes f).Reachable start finish := by
  rcases section5SimpleGraph.exists_other_degreeOne nodes f hstart hdeg with
    ⟨finish, hfinish_ne, hfinish_deg⟩
  exact ⟨finish, hfinish_ne, hfinish_deg, hconn start finish⟩

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

end Arxiv170207325
