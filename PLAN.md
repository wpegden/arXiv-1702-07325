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
  discharge `Section5SegmentGeometry` from the actual Section 5 geometry:
  the start-successor problem is now solved in the interesting range `2 ≤ n`, so the next work is
  to prove the manuscript's actual 1-dimensional continuation axioms on the canonical start
  component, now packaged as `Section5OneComplexGeometry`: every non-start node is entered from a
  unique lower-level neighbor, every node has at most one higher-level continuation, and the
  absence of a higher-level continuation forces a barycenter endpoint. These local one-complex
  axioms now mechanically imply the old degree/endpoint hypotheses and the target-facet theorem.
  A first concrete fragment is already in place: level `0` is rigidly the start node, so any
  lower neighbor of a level-`1` node is automatically and uniquely the start vertex.
  The trivial `n = 1` bookkeeping is already separated by direct one-dimensional target-facet
  lemmas, so the remaining nontrivial Section 5 path argument can stay focused on `2 ≤ n`.
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
- Current lower-side transversality status:
  `Section5Path.lean` now isolates the exact missing codomain-side hypothesis as
  `Section5LocalLowerTransversality u f`. This predicate formalizes the branch-local claim that if
  a segment-hit point of one cell is written as `lineMap x' v c` with `0 < c < 1` and `v` outside
  the lower prefix face, then the erased-face point `x'` already maps back to the same barycenter
  segment. The support layer now proves that this hypothesis is enough to make the erased-face
  construction usable: it turns
  `IsPiecewiseAffineOn.exists_erased_face_point_of_minimal_section5SegmentSubface` into actual
  erased-face membership in `section5SegmentSubfaces`, and therefore forces every vertex of a
  minimal segment-hitting subface to lie in the lower prefix face whenever that minimal subface
  has more than one vertex. The remaining obstruction is now fully explicit: add the missing
  nondegeneracy/codimension-one boundary-face statement on top of this local transversality, or
  finish the interval-endpoint route and extract the same codimension-one witnesses directly from
  `section5HitParamLeft/Right`.
- Current exact-endpoint frontier:
  `Section5Path.lean` now also has the exact-point subface families
  `section5PointHitSubfaces`, `section5HitParamLeftSubfaces`, and
  `section5HitParamRightSubfaces`. For the left/right endpoint images these families are nonempty,
  admit minimal-cardinality members, provide exact realization witnesses, and are known to lie
  inside the older `section5SegmentSubfaces` family. The support layer now also carries the
  point-hit analogues of the minimal-support/erased-face API:
  `IsPiecewiseAffineOn.exists_point_with_nonzero_weights_of_minimal_section5PointHitSubface`,
  `IsPiecewiseAffineOn.exists_erased_face_point_of_minimal_section5PointHitSubface`, and
  `minimal_section5PointHitSubface_erase_not_mem`. This is now the right interface for the next
  step: prove the endpoint-specific geometric implication that turns the erased-face witness for a
  minimal left/right endpoint-hit subface back into an exact endpoint hit on the erased face when
  appropriate, then extract a codimension-one lower face on the left and the corresponding
  uniqueness/endpoint facts on the right.
- Current explicit left-side proof boundary:
  the exact remaining lower-entry statement is now named
  `Section5LocalLeftBoundaryFaceGenericity u f`. It says that a minimal member of
  `section5HitParamLeftSubfaces u f` already has `u.level` vertices and all of them lie in
  `coordinateFace (prefixRooms n u.level)`. `Section5Path.lean` now proves this hypothesis is
  exactly enough to close the lower-step side immediately: from one minimal exact left hit it
  extracts the predecessor `Section5Step`, packages the start-component version, and threads the
  resulting `hlower` field directly into `Section5PerturbationGenericity` and the canonical
  target-facet wrapper
  `IsFaceRespecting.exists_barycenter_targetFacet_of_two_le_and_localLeftBoundaryFaceAndUpperEndpoint`.
  So the lower-side frontier is no longer an implicit “something codimension-one happens”
  placeholder; it is specifically the proof of `Section5LocalLeftBoundaryFaceGenericity` from the
  existing exact-point/transversality geometry, together with the still-separate right-side upper
  uniqueness and endpoint hypotheses.
  The latest refinement narrows the higher-level portion further: the support layer now names the
  bare numeric remainder as `Section5LocalLeftCodimensionGenericity u f`, and proves that for
  `1 < u.level` this cardinality statement plus `Section5LocalLowerTransversality u f` already
  upgrades to the full `Section5LocalLeftBoundaryFaceGenericity u f` and hence to the lower
  predecessor theorem. So for higher-level cells the left-side proof boundary is now purely the
  codimension/cardinality claim; only the degenerate exact-endpoint cases (notably the level-1
  regime) still require additional geometry beyond that. The support layer now also closes the
  easy numeric part of the level-1 start-subface case: if `u.level = 1` and `section5StartCell n`
  is a subface of `u.cell`, then `section5HitParamLeft u f = 0`, `section5StartCell n` is an exact
  left hit, minimal exact left hits are singletons, and therefore `Section5LocalLeftCodimensionGenericity u f`
  already holds in that explicit regime. What remains there is no longer cardinality; it is the
  genuinely geometric claim that such a singleton exact left hit must be the lower face itself.
  The newest reduction makes that level-1 gap completely explicit: the support layer now proves
  that any singleton facet whose unique vertex lies in `coordinateFace (prefixRooms n 1)` is
  literally `section5StartCell n`, and packages a conditional
  `section5LocalLeftBoundaryFaceGenericity_of_levelOne_and_start_subface_of_minimal_vertex_mem`.
  Lean now names the missing premise itself as `Section5LocalLevelOneLeftVertexGenericity u f`.
  So the remaining level-1 work is exactly to prove that named local hypothesis, i.e. to show
  that the unique vertex of a minimal singleton exact left hit lies in that lower face. Current
  exploration strongly suggests this is not derivable from `IsFaceRespecting` alone: the existing
  hypotheses force `f(e₁)=b₁` but do not rule out the second vertex of a level-1 cell from also
  mapping to `b₁`. So the level-1 left frontier should now be treated as either a separate
  level-one geometric lemma or an explicit extra local genericity assumption, not as something the
  present face-respecting API is expected to imply automatically. The new `n = 3` diagnostic now
  confirms this concretely: on the triangulation with vertices `e₁,e₂,e₃,m₁₂,c` and facets
  `[e₁,m₁₂,c]`, `[m₁₂,e₂,c]`, `[e₂,e₃,c]`, `[e₃,e₁,c]`, the face-respecting simplicial map fixing
  `e₁,e₂,e₃` and sending `m₁₂,c` to `e₁` already falsifies
  `Section5LocalLevelOneLeftVertexGenericity`.
  Dually, the exact remaining right-endpoint input is now also named explicitly:
  `Section5LocalUpperEndpointGenericity T f hstart` bundles the two still-unproved fields that
  the manuscript's generic path argument needs on the outgoing side, namely uniqueness of an upper
  `Section5Step` and the fact that a node with no such upper step already hits the final barycenter.
  The current exact-right-endpoint machinery does not yet reach those fields directly, because it
  analyzes minimal right-endpoint hits by taking subfaces of a fixed cell `u.cell`, while
  `upper_step_unique` and `no_upper_step_is_endpoint` are statements about the cofaces in the star
  of `u.cell`. So the actual remaining outgoing lemma is not another erased-subface statement but
  a local star-of-a-cell genericity claim: among higher-level Section 5 cells containing `u.cell`,
  the barycenter-chain segment has at most one outgoing continuation through the right endpoint,
  and if there is no such continuation then that right endpoint is already the final barycenter.
  The same `n = 3` diagnostic shows that the endpoint part is genuinely additional: the reachable
  graph node `[e₁,m₁₂]` in the example above has no upper `Section5Step` and still does not hit the
  final barycenter. The small search did not find a counterexample to `upper_step_unique`, so the
  next genuine proof target is now that uniqueness field alone, together with a decision to treat
  the left level-1 and right endpoint assertions as extra local genericity whenever the paper's
  perturbation sentence is invoked. A richer `n = 4` tetrahedral diagnostic now still finds no
  `upper_step_unique` counterexample in a fixed 4-room search, so the best current proof route is
  to stop treating that field as another hidden genericity axiom and instead prove a structural
  boundary-coface lemma: a positive-level Section 5 node is already a full-dimensional simplex in
  the boundary face `coordinateFace (prefixRooms n (k + 1))`, hence it should have at most one
  incident `(k+1)`-cell on the `coordinateFace (prefixRooms n (k + 2))` side. The level-`0`
  source case is now formally discharged separately in `Section5Path.lean` from the existing
  canonical start-edge uniqueness theorems. Concretely, the reduction is now exact: if `u,v,w`
  are Section 5 graph nodes with `Section5Step f u v` and `Section5Step f u w`, then
  `section5Step_vertices_eq_lowerPrefixVertices` already gives
  `u.cell.vertices = section5LowerPrefixVertices v = section5LowerPrefixVertices w`, so the
  remaining theorem is purely triangulation-side for `0 < u.level`. The newest Lean reduction now
  sharpens it twice more. First, any graph node `u` and any upper step `v -> u` are identified
  with the exact prefix-face vertex filter cut out inside an ambient facet:
  `u.cell.vertices = facetPrefixVertices τ (u.level + 1)` for every facet `τ` containing `u.cell`,
  and `v.cell.vertices = facetPrefixVertices τ u.level` for every such `τ`. Second, same-source
  upper-step uniqueness is now reduced to equality of those next-prefix filters:
  if two ambient facets `τu, τw` containing the two target cells satisfy
  `facetPrefixVertices τu (u.level + 1) = facetPrefixVertices τw (w.level + 1)`, then the two
  upper cells are already equal. The older common-ambient-facet theorem is therefore only one
  sufficient corollary of this sharper filter-equality reduction. So the actual unresolved
  structural lemma is now a boundary-star statement: for any full-dimensional boundary cell `σ` in
  `coordinateFace (prefixRooms n (k + 1))`, any two incident facets on the
  `coordinateFace (prefixRooms n (k + 2))` side cut out the same `facetPrefixVertices` filter,
  equivalently determine the same `(k+1)`-cell above `σ`. The newest Lean step toward that
  geometric statement is now in place: if `u` is a Section 5 graph node, then the vertices of
  `u.cell` already span exactly the same affine subspace as `prefixVertexPoints n (u.level + 1)`.
  So the remaining proof burden is no longer to show that the source cell is full-dimensional in
  the lower prefix face. `Section5Path.lean` now also proves the exact next reduction:
  an overlap point in the realization of `τu.commonFace τw` which lies in the upper prefix face
  `coordinateFace (prefixRooms n (k + 2))` but not in the lower one already yields a shared extra
  vertex, hence equality of the two upper Section 5 steps. The only live right-side construction
  problem is therefore to produce that overlap point from the affine-coordinate data of the two
  upper simplices.
  On the packaging side, the remaining graph-theoretic conversion gap is now gone: the support
  layer proves `Section5PerturbationGenericity.toBoundarySegmentGenericity`, and the existing
  local-left/upper-endpoint wrapper is rerouted through
  `section5BoundarySegmentGenericity_of_localLeftBoundaryFaceAndUpperEndpoint`. So any future
  proof of the literal endpoint geometry can now discharge either the step-level or the
  boundary-segment formulation without further interface work.
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
  `IsPiecewiseAffineOn.exists_point_with_nonzero_weights_of_minimal_section5SegmentSubface`, so
  the remaining lower-step work is now best phrased as one local contradiction lemma on a
  canonical relative-interior point of this chosen face. The support layer now sharpens this one
  step further: `minimal_section5SegmentSubface_erase_not_mem` and
  `minimal_section5SegmentSubface_vertices_mem_coordinateFace_of_erase_mem` reduce the bad-vertex
  contradiction to a single concrete erased-face statement. It is now enough to show that if a
  vertex of the minimal segment-hitting face lies outside the lower prefix face, then erasing
  that one vertex still leaves a face whose image meets `[b_k,b_{k+1}]`; minimality then yields
  the contradiction automatically. The newest helper
  `IsPiecewiseAffineOn.exists_erased_face_point_of_minimal_section5SegmentSubface` now packages
  the domain-side part of this erasure completely: after choosing `v`, it builds a point `x'` in
  the erased face realization and a coefficient `0 < c < 1` such that the original witness point
  is `lineMap x' v c` and its image is `lineMap (f x') (f v) c`. However, a direct codomain lemma
  saying that `lineMap (f x') (f v) c ∈ [b_k,b_{k+1}]` forces `f x' ∈ [b_k,b_{k+1}]` is false
  under the current ambient-face hypotheses alone; a concrete counterexample now appears in
  `PAPERNOTES.md`. So the next move is not to keep pushing that bare erased-face lemma, but to
  encode the extra transversality/genericity input the manuscript is actually using on one cell,
  or else to return to `Section5BoundarySegmentGenericity` as the honest statement of the missing
  geometric content. The older `section5LowerPrefixVertices` route remains
  available as a fallback, and the new local
  obstruction theorem still records that if the
  filtered lower subface already hits `b_k`, then every room in `prefixRooms n k` appears in the
  support of some lower-prefix vertex, while any actual lower-face preimage of `b_k` has simplex
  support exactly `prefixRooms n k`. The newest infrastructure now follows the supervisor's
  interval route directly: `Section5Path.lean` defines the affine parameterization
  `section5HitParamMap n k`, the hit-parameter set `section5HitParams u f ⊆ [0,1]`, and its two
  endpoint parameters `section5HitParamLeft` / `section5HitParamRight`. For every actual Section 5
  graph node `u`, the file now proves that `section5HitParams u f` is nonempty, compact, convex,
  and therefore equal to the closed interval between those two endpoint parameters. This removes
  the remaining ambiguity about the correct viewpoint: the next proof step is now concretely to
  identify which codimension-one faces are hit by the left and right endpoints of this interval.
  The support layer now already covers the immediate endpoint bookkeeping: the endpoint images lie
  on the relevant barycenter segment, `IsPiecewiseAffineOn` extracts actual points of
  `u.cell.realization` mapping to `section5HitParamLeft` and `section5HitParamRight`, and a
  codimension-one lower-face witness at the left endpoint can be handed directly to
  `exists_section5StartComponentLowerStep_of_subface_card_eq_and_mem_realization_map_segment`
  through the new wrapper
  `exists_section5StartComponentLowerStep_of_subface_card_eq_and_map_eq_hitParamLeft`. So the
  remaining work is no longer to rebuild any segment/predecessor infrastructure, but specifically
  to prove that the endpoint realization points lie on the correct lower and upper boundary faces,
  then to feed the left-endpoint face into the predecessor theorem and the right-endpoint face
  into the upper-neighbor / endpoint parts of `Section5BoundarySegmentGenericity`. The latest
  refinement makes the left side much sharper: for a minimal `card > 1` member of
  `section5HitParamLeftSubfaces u f`, the exact-point erased-face theorem plus
  `Section5LocalLowerTransversality` now shows that every vertex already lies in the lower prefix
  face, and the new wrapper
  `Section5LocalLowerTransversality.exists_section5(StartComponent)LowerStep_of_minimal_section5HitParamLeftSubface_card_eq`
  turns the remaining cardinality statement `τ.vertices.card = u.level` directly into the desired
  lower predecessor. So the unresolved lower-side work is now precisely that codimension-one
  cardinality upgrade for minimal exact left-endpoint hits; the unresolved upper-side work is the
  corresponding uniqueness / endpoint extraction from minimal exact right-endpoint hits.
- The right-side uniqueness proof is now pinned down more concretely than the older
  common-facet / `facetPrefixVertices` reductions. `Section5Path.lean` already proves:
  every positive-level source cell spans the full affine span of the lower prefix face; any
  overlap point in the common-face realization of two upper ambient facets, lying in the upper
  prefix face but outside the lower one, forces the two upper steps to be equal; and the extra
  vertex of one upper step has an affine-combination expansion over the other upper cell with
  strictly positive coefficient on that other step's extra vertex. So the only remaining live
  positive-level `upper_step_unique` task is the explicit small-parameter convexity argument that
  mixes those affine weights with a source-cell interior barycentric vector to keep all merged
  source weights nonnegative and thereby produce the required overlap point. The latest direct
  Lean attempt now identifies the exact standalone lemma to package if the final proof is split
  one more time: let `α` be the affine-combination weights on the upper cell with
  `α(extra) > 0`, let `λ` be the uniform source-cell weights extended by `0` on the extra upper
  vertex, and prove there exists `t ∈ Ioo (0 : ℝ) 1` such that
  `β := (1 - t) • λ + t • α` is pointwise nonnegative while `β(extra)` stays positive. The
  explicit choice `t = c / (2 * (c + ∑ i, |α i|))`, where `c` is the uniform source weight, is
  sufficient mathematically; the current blocker is Lean's subtype-sum / `centerMass` bookkeeping
  rather than any new geometric uncertainty.
- First prove the barycenter-specialized version if that is the easiest entry point.
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
