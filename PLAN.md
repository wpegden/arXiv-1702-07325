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
- Current structural blocker:
  the present `SimplexTriangulation` wrapper does not yet expose the induced simplicial
  subdivision of the prefix faces, especially the boundary edge `[e_1,e_2]`, and it also does
  not formalize the perturbation/genericity argument that makes the barycenter-chain preimage a
  finite 1-dimensional cell complex. The start-successor existence claim has now been recovered
  directly from boundary-edge geometry, and the residual local graph obligations have been reduced
  further to proving the concrete fields of `Section5BoundarySegmentGenericity` from actual simplex
  intersections with the barycenter chain. A later cleanup may still derive the remaining
  `Section5OneComplexGeometry` fields from the same input, but that is no longer the main blocker
  for the target-facet theorem.
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
