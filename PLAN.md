# Formalization Plan

## Scope
- Formalize the paper-facing definitions and theorem statements from `paper/arxiv-1702.07325.tex`, with proofs allowed to live in support files.
- Prioritize the actual mathematical results used later in the paper over duplicate expository proofs. In particular, formalize one robust route through the piecewise-affine/Sperner machinery first; treat the trap-door parity proof and the ad hoc `n = 3` pair-label proof as secondary corollaries unless they become necessary.
- Avoid unapproved axioms and avoid building general topological degree theory. The plan should stay within finite-dimensional convex geometry, affine independence, finite combinatorics, and Hall's marriage theorem.

## Core Modeling Decisions

### Ambient simplex
- Use `Fin n` for the set of rooms.
- Model the rent simplex as `stdSimplex R (Fin n)` from `Mathlib.Analysis.Convex.StdSimplex`, with `R = ℝ` for the main paper-facing statements.
- Use `stdSimplex.vertex` for the standard vertices and `stdSimplex.barycenter` for the barycenter.
- Work in the ambient vector space `Fin n → ℝ`; this keeps faces, coordinates, convex hulls, and averages concrete.

### Preferences and the "one-cent error" condition
- Do not attempt to formalize roommate utility continuity directly.
- Instead, formalize the paper's combinatorics as labelings on vertices of a sufficiently fine triangulation.
- Record the interpretation from `PAPERNOTES.md`: the one-cent condition is only used to justify passing from consistent vertex labels on a small simplex to one rent division inside that simplex.

### Triangulations
- Start from `Geometry.SimplicialComplex ℝ (Fin n → ℝ)` in `Mathlib.Analysis.Convex.SimplicialComplex.Basic`, but wrap it in a paper-local finite structure.
- The wrapper should bundle finiteness of the relevant facets and vertices.
- The wrapper should record that the underlying space equals the standard simplex.
- The wrapper should record that every facet has the expected cardinality.
- The wrapper should provide easy access to the vertices of a facet as a finite affine-independent family.
- If the existing simplicial-complex API is too awkward, keep the wrapper minimal and expose only the lemmas needed by the paper.

### Labelings
- Define a paper-local `SpernerLabeling` on a triangulation, with the boundary rule expressed in terms of the smallest face of the standard simplex containing a vertex.
- Keep separate the paper's actual roommate choices and the encoded Sperner labels.
- Section 4 needs the cyclic permutation trick: actual free-room choices live on complement faces, and composing with the inverse cyclic permutation produces genuine Sperner data.

## Expected Mathlib Reuse
- `Mathlib.Analysis.Convex.StdSimplex`
  for the standard simplex, its vertices, convexity, compactness, and barycenter.
- `Mathlib.Analysis.Convex.Hull`
  for convex hulls and facet-image arguments.
- `Mathlib.Analysis.Convex.Segment`
  for line segments and the Section 5 path/entrance arguments.
- `Mathlib.LinearAlgebra.AffineSpace.Independent`
  for affine independence.
- `Mathlib.LinearAlgebra.AffineSpace.AffineMap`
  for affine interpolation and `AffineMap.lineMap`.
- `Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic`
  and `Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid`
  for simplex centroids and face lemmas if needed.
- `Mathlib.Analysis.Convex.SimplicialComplex.Basic`
  for the ambient triangulation structure, if it proves ergonomic enough.
- `Mathlib.Combinatorics.SimpleGraph.Hall`
  for Hall's marriage theorem in the final matching step.

## Infrastructure We Probably Need Locally
- A finite triangulation wrapper around the ambient simplicial-complex data.
- A clean API for coordinate faces of the standard simplex.
- That API should include support of a simplex point, membership in a coordinate face, interior-point lemmas for positive coordinates, and barycenter/centroid coordinate identities.
- A paper-local representation of the piecewise-affine map attached to a labeling.
- A convenient statement saying "the image of a facet contains `y`" in terms of the convex hull of the images of that facet's vertices.
- Lightweight wrappers around Hall so the main theorem can stay paper-facing instead of graph-API-facing.

## Proposed File Layout
- `repo/PaperDefinitions.lean`
  paper-facing definitions and aliases only.
- `repo/PaperTheorems.lean`
  paper-facing theorem statements only, with short wrappers around support results.
- `repo/Arxiv170207325/SimplexModel.lean`
  standard-simplex setup, coordinate faces, barycenter lemmas, cyclic permutation helper.
- `repo/Arxiv170207325/Triangulation.lean`
  finite triangulation wrapper and facet API.
- `repo/Arxiv170207325/Labeling.lean`
  Sperner labelings, encoded roommate labelings, label sets on facets.
- `repo/Arxiv170207325/InteriorTarget.lean`
  initial Section 5 support file for ambient coordinate faces, interior points, and the first
  face-preserving map lemmas feeding the target-hitting theorem.
- `repo/Arxiv170207325/Section5Triangulation.lean`
  finite combinatorics for the remaining Section 5 proof: facet/subface incidence, adjacency, and
  the discrete graph built from the triangulation.
- `repo/Arxiv170207325/Section5Path.lean`
  the geometric/path-following half of Section 5: the barycenter chain, preimage graph, and the
  endpoint argument producing a target-containing facet.
- `repo/Arxiv170207325/PiecewiseAffine.lean`
  facetwise affine images and the global target-hitting theorem.
- `repo/Arxiv170207325/HallTools.lean`
  bipartite-graph wrappers specialized to acceptable-room relations.
- `repo/Arxiv170207325/Sperner.lean`
  Sperner lemma and immediate corollaries.
- `repo/Arxiv170207325/SecretiveRoommate.lean`
  Section 4 main theorem and the `n = 3` corollaries if desired.
- `repo/Arxiv170207325/Generalizations.lean`
  Section 6 theorems.
- `repo/Arxiv170207325/Algorithmic.lean`
  Section 5 graph/path theorem if it is cleaner to separate from `PiecewiseAffine.lean`.

## Paper-Facing Definitions To Expose Early
- `RentSimplex n := stdSimplex ℝ (Fin n)`
- `rentBarycenter : RentSimplex n`
- `SimplexTriangulation n`
- `SpernerLabeling (T : SimplexTriangulation n)`
- `EncodedPreferenceLabeling (T : SimplexTriangulation n)`
- `facetLabelSet`
- `facetDistinctLabelCount`
- `facetMultiplicityVector`
- a theorem-level wrapper for the cyclic permutation encoding from Section 4

## Central Dependency Plan

### Stage 1: simplex and face bookkeeping
- Prove reusable facts about coordinate faces of `stdSimplex`.
- Prove barycenter facts in coordinates.
- Prove the cyclic-permutation face lemma from `PAPERNOTES.md`: for every proper support set `I`, there exists `i in I` with `pi(i) notin I`.

### Stage 2: triangulation and labelings
- Define the triangulation wrapper and its facets.
- Define labelings on vertices and the induced label sets on facets.
- Define the facetwise affine image simplex attached to a labeling.

### Stage 3: the central geometric theorem
- Main technical target:
  if a piecewise-affine self-map of a triangulated standard simplex respects coordinate faces, then for a chosen target point in the interior of the simplex there exists a facet whose image contains that target.
- File-split decision for the remaining Section 5 proof:
  keep `InteriorTarget.lean` for face/interior reductions, move triangulation-side graph and
  adjacency lemmas to `Section5Triangulation.lean`, and isolate the preimage-path geometry in
  `Section5Path.lean`.
- Current support status:
  `Section5Triangulation.lean` now contains the first common-face, subface, incidence, and
  codimension-one degree lower-bound lemmas, while `Section5Path.lean` contains the paper's
  nested prefix faces `conv{e_1, ..., e_k}`, their barycenters `b_k`, the first Section 5 graph
  node/edge/path definitions, the concrete start node `e_1 = b_1`, the actual finite node set
  built from triangulation-face candidates, the explicit start connected component inside that
  concrete node graph, an abstract finite-graph endpoint theorem together with its
  specialization to the full concrete node set, and a second specialization
  `section5StartComponentGraph.exists_targetFacet_of_endpoint_rule` on the actual start
  component itself, now connected to the packaged graph-theoretic assumptions via
  `Section5StartComponentGenericity.exists_targetFacet`, with a further wrapper
  `Section5SegmentGeometry.exists_targetFacet` isolating the paper's sketch-level generic
  segment-intersection input from the pure graph theory, plus a start-boundary layer
  `Section5StartBoundaryGeometry` that separates the unique level-1 successor geometry from the
  rest of the local degree argument and records that a face-respecting map already forces the
  singleton start cell `e_1` to hit `b_1`; in addition, the triangulation API now proves that any
  facet realization containing the original simplex vertex `e_1` must actually have `e_1` as a
  vertex, so `section5StartNode` is automatically a genuine Section 5 graph node under face
  preservation; the boundary-start interface has now also been repackaged canonically into
  `Section5CanonicalBoundarySuccessorData`, and the new boundary-ordering lemmas on
  `ambientCoordinateFace (prefixRooms n 2)` together with facet-realization recovery now show
  that any level-1 Section 5 cell containing `e_1` is automatically unique whenever it exists, so
  the remaining local goal was reduced to the existence of a level-1 successor on the real start
  component from actual boundary geometry rather than a separate uniqueness proof. That existence
  step is now also proved in the genuine boundary-edge range `2 ≤ n`: `Section5Path.lean`
  extracts a non-start triangulation vertex on `[e_1,e_2]`, uses a maximal boundary vertex to
  force `e_1` into the support of a nearby covered point, and packages the resulting start edge as
  `IsFaceRespecting.exists_levelOne_canonical_start_subface` and
  `IsFaceRespecting.section5CanonicalBoundarySuccessorData_of_two_le`; the remaining wrappers are
  now collapsed into a
  direct theorem saying that face preservation, a concrete unique start successor, and the
  two local-degree hypotheses already imply a target-containing facet.
- Next local objective:
  discharge the compiled simplex-slice bridge from the actual Section 5 geometry:
  the start-successor problem is now solved in the interesting range `2 ≤ n`, and the remaining
  critical path no longer goes through the older `Section5OneComplexGeometry` abstraction. The
  next work is to prove the manuscript's local segment-intersection picture in the more concrete
  forms `Section5MinimalSliceLowerBoundaryGeometry` and `Section5SimplexSliceBoundaryGeometry`:
  for each non-start node `u`, choose a minimal segment-hitting subface `τ`, show
  `section5CellSlice u f` is a genuine 1-dimensional segment inside `u.cell`, and prove its lower
  boundary lies in a unique codimension-one subface of `τ` contained in
  `coordinateFace (prefixRooms n u.level)` with exactly `u.level` vertices. Once those local
  fields are available, the existing bridge already compiles them into
  `Section5MinimalSliceFaceData`, `Section5SimplexSliceGenericity`,
  `Section5PerturbationGenericity`, and finally `Section5BoundarySegmentGenericity`.
  The newest reduction makes this target more explicit and proof-local: `Section5Path.lean` now
  proves that for a minimal segment-hitting face `τ`, if every vertex of `τ` outside the lower
  prefix face can be erased while retaining a slice point on the opposite face, then all vertices
  of `τ` already lie in `coordinateFace (prefixRooms n u.level)`; if in addition
  `τ.vertices.card = u.level`, this immediately packages as
  `Section5MinimalSliceLowerBoundaryGeometry u f`. The newest local collapse is sharper still:
  `minimal_section5SegmentSubface_card_eq_and_vertices_mem_coordinateFace_of_lower_boundary_face`
  shows that one codimension-one lower boundary face `ρ ≤ τ` with `ρ.vertices.card = u.level`,
  all `ρ`-vertices in the lower prefix face, and one slice point on `ρ` already forces both
  remaining face-level conclusions for `τ`. The latest refinement makes that lower face canonical:
  for any lower-prefix slice point `x ∈ τ.realization`, the filtered face
  `section5FacetLowerPrefixVertices u τ` automatically contains `x`, and
  `minimal_section5SegmentSubface_lowerBoundaryGeometry_of_facetLowerPrefixVertices_card_eq`
  packages the whole lower-boundary theorem as soon as one proves
  `(section5FacetLowerPrefixVertices u τ).card = u.level`. So the remaining geometry is now
  concentrated in a single honest manuscript-level task: prove that the 1-dimensional slice
  inside a minimal segment-hitting face actually reaches the lower prefix face, and that the
  resulting canonical filtered subface has the expected cardinality `u.level`. The new theorem
  `minimal_section5SegmentSubface_exists_mem_coordinateFace_point_of_vertices_mem_coordinateFace`
  now makes the lower-prefix slice point automatic from the vertex condition, so one no longer
  has to construct that point separately once the face-in-lower-prefix statement is known.
  The current recovery route moves the lower-step proof boundary back onto `u.cell` itself.
  `Section5Path.lean` now has the direct local package `Section5LowerEntryFaceData` and the
  global wrapper `Section5EntryFaceGenericity`, and
  `Section5EntryFaceGenericity.toPerturbationGenericity` feeds that data directly into
  `exists_section5StartComponentLowerStep_of_subface_card_eq_and_facetImageContains`. So the
  next honest geometric theorem is no longer "a chosen minimal `τ` contains the lower face";
  instead it is to construct the lower entry face `ρ ≤ u.cell` from the manuscript's
  1-dimensional slice picture, with `ρ.vertices.card = u.level`, every vertex of `ρ` in
  `coordinateFace (prefixRooms n u.level)`, and `FacetImageContains f ρ
  (prefixBarycenter n u.level)`.
  The newest cleanup makes this canonical rather than existential: the filtered face
  `⟨section5LowerPrefixVertices u⟩` is now packaged directly as `Section5LowerEntryFaceData u f`
  as soon as one proves its cardinality is `u.level` and its image contains
  `prefixBarycenter n u.level` (or equivalently exhibits one lower-prefix slice point mapping
  there). So the remaining local geometry has been reduced to exactly those two cell-level facts
  on the canonical lower-prefix face, rather than to a search for an unnamed subface `ρ`.
  This reduction is now checked in Lean in both local and global forms:
  `section5LowerEntryFaceData_nonempty_iff_card_eq_and_facetImageContains_lowerPrefixVertices`
  identifies lower-entry data with those two canonical facts on one cell, and
  `Section5EntryFaceGenericity.lower_entry_face_of_ne_start_canonical` exposes the same pair of
  obligations for every non-start node in the start component. The barycenter-hit half has now
  been sharpened one step further: `FacetImageContains f (⟨section5LowerPrefixVertices u⟩ :
  SimplexFacet n) (prefixBarycenter n u.level)` is equivalent to the existence of a point
  `x ∈ section5CellSlice u f` that also lies in `coordinateFace (prefixRooms n u.level)`.
  This slice-point half is now also automatic once one has the older local slice package:
  `Section5MinimalSliceFaceData.exists_point_mem_slice_and_mem_coordinateFace` extracts such a
  point directly, so any future proof of `Section5SimplexSliceGenericity` or
  `Section5SimplexSliceBoundaryGeometry` already supplies the canonical lower-prefix slice point.
  The same is now true from the step language itself:
  `IsPiecewiseAffineOn.section5Step_card_eq_lowerPrefixVertices_and_exists_point` shows that a
  single lower predecessor `Section5Step f v u` already forces both canonical lower-entry facts
  on `u`, namely `(section5LowerPrefixVertices u).card = u.level` and existence of a slice point
  in the lower prefix face. The older simplex-slice genericity package now also compiles all the
  way to that same canonical pair:
  `Section5SimplexSliceGenericity.card_eq_lowerPrefixVertices_and_exists_point` passes from the
  existing lower-step theorem to the predecessor-step bridge, so no further conversion work
  remains between the old slice package and the new canonical lower-entry route.
  So the remaining honest geometry on `u.cell` is now: prove that the slice reaches the lower
  prefix face, and prove that the canonical lower-prefix face has exactly `u.level` vertices.
  The older `Section5OneComplexGeometry` layer remains useful as cleanup, but it is no longer the
  main proof boundary.
  A first concrete fragment is already in place: level `0` is rigidly the start node, so any
  lower neighbor of a level-`1` node is automatically and uniquely the start vertex. The trivial
  `n = 1` bookkeeping is already separated by direct one-dimensional target-facet lemmas, so the
  remaining nontrivial Section 5 path argument can stay focused on `2 ≤ n`.
  The new reusable local tool is `prefixVertexPoints`: `Section5Path.lean` now proves that every
  point in `coordinateFace (prefixRooms n k)` lies in the convex hull, hence the affine span, of
  the first `k` standard simplex vertices, and every Section 5 graph-node vertex inherits this
  affine-span membership at level `u.level + 1`. The intended next use is to combine these span
  lemmas with `SimplexTriangulation.facet_affineIndependent` to bound how many lower-prefix
  vertices can occur in one higher-level cell. That affine/cardinality step is now carried out:
  `Section5Path.lean` defines `section5LowerPrefixVertices`, proves
  `SimplexTriangulation.card_le_prefixVertexPoints_of_subset_coordinateFace`,
  upgrades it to `IsSection5GraphNode.card_lowerPrefixVertices_le`, and then shows any actual
  lower continuation `u -> v` must satisfy
  `u.cell.vertices = section5LowerPrefixVertices v`. As a consequence,
  `section5StartComponentGraph_lower_neighbor_unique` is now proved on the real start component
  without assuming any genericity package. In addition, the remaining manuscript-level genericity
  sentence has now been isolated exactly as `Section5BoundarySegmentGenericity`: a local support
  layer saying the current barycenter-chain segment contributes at most two boundary neighbors, and
  exactly one when the segment ends inside the face. `Section5Path.lean` now proves that this
  package, together with the already-solved canonical start-successor data, directly yields
  `Section5SegmentGeometry` and therefore a target-containing facet; so `Section5OneComplexGeometry`
  is no longer on the critical path for the paper-facing theorem, even though it remains useful
  internal structure. The last wrapper gap has also been removed: `Section5Path.lean` now exposes
  `IsFaceRespecting.exists_barycenter_targetFacet_of_boundarySegmentGenericity`, which combines the
  trivial `n = 1` base case with the `2 ≤ n` canonical-start theorem, so the only missing input
  at the Section 5 theorem boundary is a proof of `Section5BoundarySegmentGenericity` itself.
  The lower-side part of that package is now completely explicit: `Section5Path.lean` proves
  `(section5LowerNeighbors v).card ≤ 1`, that lower and upper neighbor finsets are disjoint, and
  that `section5BoundaryNeighbors v` has cardinality equal to the sum of the lower and upper
  cardinalities. So the remaining geometric input has been narrowed further to the upper-side
  bound and the endpoint rule when no upper continuation exists. The last proof-theoretic wrapper
  has now also been removed: `Section5Path.lean` exposes
  `IsFaceRespecting.exists_barycenter_targetFacet_of_upperCardLeOneAndEndpointRule`, so once the
  manuscript's perturbation argument is formalized strongly enough to show
  `(section5UpperNeighbors v).card ≤ 1` and the corresponding endpoint rule, the final Section 5
  target-facet theorem follows immediately without any further graph packaging. In addition,
  `Section5Path.lean` now has an even closer bridge to the manuscript's segment language:
  uniqueness of upper `Section5Step` continuations implies `(section5UpperNeighbors v).card ≤ 1`,
  and step-level lower/upper/endpoint hypotheses assemble directly into
  `Section5OneComplexGeometry` and the canonical target-facet theorem. So the remaining proof
  boundary can now be stated entirely in terms of the barycenter-chain segment hitting the
  codimension-one faces of one simplex cell. This interface is now named
  `Section5PerturbationGenericity`, and the theorem
  `IsFaceRespecting.exists_barycenter_targetFacet_of_two_le_and_perturbationGenericity` shows
  that once the manuscript's perturbation sentence is proved in this explicit step language, the
  Section 5 target-facet conclusion is immediate. A separate modeling correction was also made at
  the paper-facing boundary: `IsPiecewiseAffineOn` now means agreement with one affine chart on
  the whole realization of each triangulation facet, not only on its vertices. With that stronger
  and manuscript-faithful hypothesis, `Section5Triangulation.lean` now proves the two-way bridge
  between `FacetImageContains` and actual simplex points: one can extract a point of
  `σ.realization` from a hull hit, and conversely any point of `σ.realization` maps back into
  `FacetImageHull f σ`. `Section5Path.lean` already specializes the extraction direction to
  Section 5 graph nodes via `IsPiecewiseAffineOn.exists_point_in_cell_realization_of_graphNode`,
  which is the new starting point for the remaining perturbation proof.
- Current structural blocker:
  the present `SimplexTriangulation` wrapper does not yet expose the induced simplicial
  subdivision of the prefix faces, especially the boundary edge `[e_1,e_2]`, and it also does
  not formalize the perturbation/genericity argument that makes the barycenter-chain preimage a
  finite 1-dimensional cell complex. The start-successor existence claim has now been recovered
  directly from boundary-edge geometry, and the residual local graph obligations have been reduced
  further to proving the concrete fields of `Section5BoundarySegmentGenericity` from actual simplex
  intersections with the barycenter chain. A later cleanup may still derive the remaining
  `Section5OneComplexGeometry` fields from the same input, but that is no longer the main blocker
  for the target-facet theorem. The support-shrinking half of the lower-step argument is now in
  place: if a point of one Section 5 cell already lies in the lower prefix face and its image
  still lies on `[b_k,b_{k+1}]`, the new endpoint lemma forces that image to be exactly `b_k`;
  then the filtered subface `section5LowerPrefixVertices` already realizes that point and its
  image hull contains `b_k`. More importantly, `Section5Path.lean` now has the direct
  manuscript-shaped predecessor theorem: if the geometry produces an actual codimension-one lower
  face `τ ≤ u.cell` with `τ.vertices.card = u.level`, all vertices of `τ` in the lower prefix
  face, and `b_k ∈ λ(τ)`, then that face already gives the predecessor `Section5Step`. The newest
  packaging goes one step closer to the manuscript's prose: `Section5Path.lean` now has the
  explicit local structures `Section5MinimalSliceLowerBoundaryGeometry` and
  `Section5SimplexSliceBoundaryGeometry`, together with compiled bridges reducing them to
  `Section5MinimalSliceFaceData` and `Section5SimplexSliceGenericity`. So the remaining blocker is
  no longer how to transport a proved local geometry statement through the graph wrappers; it is
  specifically the honest geometric theorem that the preimage slice inside one simplex cell really
  is a segment with the required lower boundary face. The latest support theorem sharpens this
  further: once a minimal face `τ` has the manuscript's erased-face slice witnesses for vertices
  outside the lower prefix face, the new theorem
  `minimal_section5SegmentSubface_vertices_mem_coordinateFace_of_erase_realization_map_segment`
  forces all vertices of `τ` into the lower prefix face, and
  `minimal_section5SegmentSubface_lowerBoundaryGeometry_of_card_eq_of_erase_realization_map_segment`
  then packages the result as `Section5MinimalSliceLowerBoundaryGeometry`. So the unresolved
  content is now even more local: the new theorem
  `mem_erase_realization_of_mem_realization_of_mem_coordinateFace_of_not_mem_coordinateFace`
  shows that one slice point of `τ` already lying in the lower prefix face automatically belongs
  to every erased face `τ.erase v` for a bad vertex `v`, hence
  `minimal_section5SegmentSubface_erase_realization_map_segment_of_mem_coordinateFace_point`
  supplies all erased-face witnesses at once. So the unresolved geometric content is now
  precisely to prove that all vertices of a minimal face already lie in the lower prefix face and
  to prove the cardinality statement `τ.vertices.card = u.level`; the new theorem
  `minimal_section5SegmentSubface_exists_mem_coordinateFace_point_of_vertices_mem_coordinateFace`
  recovers the lower-prefix slice point automatically from that vertex condition, and
  `minimal_section5SegmentSubface_lowerBoundaryGeometry_of_card_eq_of_vertices_mem_coordinateFace`
  then feeds the result directly into the existing lower-boundary bridge.
  bridge removes even that final `b_k ∈ λ(τ)` packaging step: if the geometry gives a point of
  `τ.realization` whose image stays on `[b_k,b_{k+1}]`, convexity forces that whole face to lie in
  the lower prefix face, the endpoint lemma turns the image into `b_k`, and the direct theorem
  `exists_section5StartComponentLowerStep_of_subface_card_eq_and_mem_realization_map_segment`
  yields the predecessor immediately. The support layer now also makes the finite-combinatorial
  route explicit: for each cell `u.cell` there is a finite family `section5SegmentSubfaces u f`
  of nonempty subfaces whose image meets `[b_k,b_{k+1}]`, a minimal-cardinality member of that
  family exists, and the existing piecewise-affine API extracts an actual point of that minimal
  face mapping to the segment. The newest refinement is that this witness can now be chosen with
  nonzero barycentric weight on every vertex of the minimal face, via
  `IsPiecewiseAffineOn.exists_point_with_nonzero_weights_of_minimal_section5SegmentSubface`, and
  the erased-face API still isolates the concrete counterexample showing why the old codomain
  lemma cannot be salvaged from ambient-face data alone. Rather than pushing that false route
  further, `Section5Path.lean` now exposes the honest replacement interface:
  `section5CellSlice` is the actual preimage slice of `[b_k,b_{k+1}]` inside one cell,
  `Section5MinimalSliceFaceData` packages a minimal segment-hitting codimension-one lower face,
  and `Section5SimplexSliceGenericity` records these local slice facts on every non-start node.
  The new bridge theorem
  `Section5SimplexSliceGenericity.toPerturbationGenericity` feeds the lower field directly into
  `exists_section5StartComponentLowerStep_of_subface_card_eq_and_mem_realization_map_segment`, and
  `Section5PerturbationGenericity.toBoundarySegmentGenericity` then recovers the manuscript-level
  boundary-neighbor package automatically. So the immediate frontier is now precise: prove the
  actual fields of `Section5SimplexSliceGenericity` from the paper's generic segment-intersection
  sentence, rather than trying to deduce them from erased codomain endpoints. Concretely, the
  next local theorem should show that for a minimal `τ ∈ section5SegmentSubfaces u f`, the slice
  `section5CellSlice u f` behaves as a genuine 1-dimensional segment in `u.cell`, so its boundary
  meets at most two codimension-one subfaces of `τ` and, when it terminates at `b_k`, exactly one
  such boundary face lies in `coordinateFace (prefixRooms n u.level)`. That statement should
  produce `Section5MinimalSliceFaceData` for the lower predecessor and simultaneously feed the
  existing upper-step uniqueness / endpoint rules.
- Then generalize to arbitrary interior targets if Section 6 needs it.
- If full surjectivity is still awkward, keep the theorem in the "target in interior" form first; that already covers the barycenter and the interior `y` used in the first Section 6 theorem.

### Stage 4: Sperner lemma
- Build the usual vertex-label map to simplex vertices.
- Apply the Stage 3 target-hitting theorem at the barycenter.
- Conclude that the chosen facet must be fully labeled.
- The odd-count version of Sperner is lower priority and can be postponed.

### Stage 5: main secretive-roommate theorem
- For each visible roommate, build the encoded Sperner labeling via the cyclic permutation.
- Average the corresponding facetwise affine maps.
- Apply the Stage 3 theorem at the barycenter.
- Prove the coordinate-sum lemma:
  any `k` visible roommates jointly exhibiting at most `k` labels on the chosen facet would force the average map away from the barycenter.
- Convert the resulting combinatorial condition into Hall's condition on a bipartite graph between visible roommates and untaken rooms.

### Stage 6: Section 6 generalizations
- First theorem: replace the average by a sum map to `m • simplex`, use the interior target `y`, and show the containing simplex is a facet because lower-dimensional faces only use at most `n` lattice points.
- Second theorem: use the weighted average with coefficients `alpha_j`, hit the barycenter, define the `beta_ij` weights, and use the integrality/counting argument from `PAPERNOTES.md`.

## Section-By-Section Proof Roadmaps

### Section 2: Sperner's lemma
- Formalize the second proof first, since it feeds every later section.
- Keep the first proof and the odd-parity refinement optional unless we need them for a theorem statement.

### Section 3: three roommates
- Do not start with the pair-label proof.
- Instead, obtain the `n = 3` case as a corollary of the general theorem.
- If time permits, add the pair-label argument as a finite combinatorial lemma over the nine label pairs.

### Section 4: the general case
- This is the primary target after the central geometric theorem.
- Most of the proof is algebraic once the barycenter-hitting result exists: cyclic boundary encoding, average map, the coordinate-sum contradiction, and Hall.

### Section 5: algorithmic aspects
- Formalize enough of the path-following graph argument to support the central geometric theorem.
- Keep the fully executable algorithm as optional; the paper's needs are satisfied by an existence theorem for a path ending in a target-containing facet.

### Section 6: generalizations
- Both theorems should become short corollaries once Section 4's average-map framework is abstracted properly.
- The main extra work is packaging multiplicity vectors and the weighted-count argument cleanly.

## Concrete First Milestones
1. Create `PaperDefinitions.lean` with the ambient simplex aliases and paper-facing structures.
2. Build `SimplexModel.lean` with support/face/barycenter lemmas and the cyclic permutation encoding.
3. Build `Triangulation.lean` and `Labeling.lean`.
4. State the central Stage 3 theorem in `PaperTheorems.lean` before proving it elsewhere.
5. Prove the Stage 3 barycenter-hitting theorem.
6. Derive the Section 2 Sperner theorem.
7. Derive the Section 4 secretive-roommate theorem.
8. Finish the Section 6 generalizations.

## Main Risks
- `Geometry.SimplicialComplex` is available, but the paper needs a finite, facet-oriented API; the wrapper may be nontrivial.
- The paper's Section 5 argument is written at a sketch level, so the Lean proof should be organized around an explicit graph/path invariant instead of following the prose literally.
- Dimension bookkeeping is easy to get wrong: `n` rooms correspond to the simplex on `Fin n`, whose geometric dimension is `n - 1`, while the paper's notation `Delta_n` in Section 6 corresponds to `Fin (n + 1)` in Lean.
- It is likely better to prove a strong local geometric theorem once than to separately formalize each paper proof variant.

## Out Of Scope Until The Core Theorems Land
- Full formalization of the trap-door parity count in Sperner's lemma.
- A polished executable search algorithm extracted from the Section 5 proof.
- Any attempt to encode the original roommate preference axioms directly as topological data.
