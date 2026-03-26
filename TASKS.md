# Tasks

<!-- SUPERVISOR_TASKS:START -->
## Supervisor Tasks
- [ ] Prove the target statements presented in `PaperTheorems.lean`.
- [ ] Keep reusable proof infrastructure in separate support files when that yields a cleaner project structure.
- [ ] Maintain `TASKS.md` and `PLAN.md` as the proof frontier moves.
- [ ] Keep sorrys within the configured policy.
- [ ] Do not introduce unapproved axioms.
<!-- SUPERVISOR_TASKS:END -->

## Worker Tasks
- [x] Strengthen `repo/Arxiv170207325/SimplexModel.lean` with the first proof-facing lemmas on supports, coordinate faces, barycenter coordinates, and cyclic permutation.
- [x] Decide whether `SimplexTriangulation` should gain explicit cover/gluing fields before the proof phase begins in earnest.
- [x] Begin the first proof-facing support file for the interior target-hitting theorem from Section 5.
- [x] Extend `repo/Arxiv170207325/InteriorTarget.lean` from face-preservation lemmas to the first facet-image and interior-point reduction lemmas.
- [x] Decide the next support-file split for the Section 5 existence proof: `Section5Triangulation.lean` for discrete incidence/adjacency work and `Section5Path.lean` for the path-following geometry.
- [x] Create `repo/Arxiv170207325/Section5Triangulation.lean` with the first facet/subface adjacency and graph-interface lemmas.
- [x] Create `repo/Arxiv170207325/Section5Path.lean` with the first barycenter-chain and endpoint/path invariants.
- [x] Extend `repo/Arxiv170207325/Section5Triangulation.lean` from basic subface/adjacency definitions to the incidence and degree lemmas used in the Section 5 graph argument.
- [x] Extend `repo/Arxiv170207325/Section5Path.lean` from prefix-face barycenters and chain segments to the actual graph/path structure and the endpoint lemma that yields a target-containing facet.
- [x] Prove the first abstract path-existence lemma: in a finite `Section5Adjacent` graph, the start-degree and local degree assumptions imply another degree-one endpoint, and an endpoint rule then yields a target-containing facet.
- [x] Define the actual finite Section 5 node set from triangulation-face candidates, prove every `IsSection5GraphNode` lies in it, and specialize the abstract endpoint theorem to that concrete node set.
- [x] Define the actual start connected component inside the concrete Section 5 node graph and record its basic reachability/preconnectedness API.
- [x] Lift the abstract endpoint theorem from the full node set to the explicit start component, and package the paper's generic Section 5 input on that component in a reusable support-layer structure.
- [x] Connect `Section5StartComponentGenericity` to the concrete start-component endpoint theorem by proving `Section5StartComponentGenericity.exists_targetFacet`.
- [x] Introduce `Section5SegmentGeometry` as the paper-facing generic segment-intersection package and prove that it implies `Section5StartComponentGenericity` and therefore a target-containing facet.
- [x] Isolate the Section 5 start-boundary geometry into a dedicated support layer and prove that any face-respecting map sends the singleton start cell `e₁` to the first barycenter `b₁`.
- [x] Package the Section 5 endpoint conclusion so that face preservation, a concrete unique start successor, and the remaining local-degree data directly yield a target-containing facet.
- [x] Prove that `section5StartNode` is automatically a real Section 5 graph node for any face-respecting map by showing the triangulation actually contains the original start vertex `e₁`.
- [x] Repackage the start-boundary input canonically from `IsFaceRespecting`: isolate `Section5CanonicalBoundarySuccessorData`, prove the start-adjacency criterion no longer needs an extra hit hypothesis, and derive the start-degree-one/target-facet wrappers from that package.
- [x] Prove that the level-1 Section 5 cell containing `e₁` is automatically unique whenever it exists: formalize the `[e₁,e₂]` boundary ordering argument, show two distinct start edges would force a forbidden extra facet vertex on the same boundary segment, and package the resulting `exists -> exists!` upgrade for `Section5CanonicalBoundarySuccessorData`.
- [ ] Resolve the current Section 5 modeling gap: either strengthen the triangulation support layer to expose the induced boundary subdivisions of the prefix faces, or formalize the perturbation/genericity argument that turns the barycenter-chain preimage into a finite 1-dimensional cell complex.
- [x] Prove the existence half of `Section5CanonicalBoundarySuccessorData` for the genuine boundary-edge regime `2 ≤ n`: extract a non-start triangulation vertex on `[e₁,e₂]`, use a maximal-boundary-vertex argument to force `e₁` into the support of a nearby covered point, and package the resulting level-1 start edge in the canonical start component.
- [x] Isolate the remaining low-dimensional bookkeeping around the new start-successor theorem by proving direct `n = 1` target-facet lemmas, so the nontrivial Section 5 path work can now focus on `2 ≤ n`.
- [x] Repackage the remaining Section 5 local-degree work into a direct 1-dimensional-cell-complex interface on the actual start component: define `Section5OneComplexGeometry`, prove it yields the `≤ 2` degree bound and non-start endpoint rule, and bridge it to `Section5SegmentGeometry` and the canonical target-facet theorem.
- [x] Prove the first concrete one-complex fragment on the real start component: any level-0 node is the start node, so any lower neighbor of a level-1 node is uniquely the start vertex.
- [x] Add the prefix-face affine-span infrastructure for the next uniqueness step: define the finite set `prefixVertexPoints`, prove every point of `coordinateFace (prefixRooms n k)` lies in its convex hull and affine span, and specialize that fact to Section 5 graph-node vertices.
- [x] Use the `prefixVertexPoints` affine-span lemmas together with facet affine independence to bound the number of lower-face vertices inside a higher-level Section 5 cell, and use that bound to prove concrete lower-continuation uniqueness on the real start component.
- [x] Introduce `Section5BoundarySegmentGenericity` as the exact support-layer formalization of the manuscript's remaining generic segment-intersection input, and prove it directly implies the `≤ 2` degree bound, the non-start endpoint rule, `Section5SegmentGeometry`, and the canonical target-facet theorem.
- [x] Add the final `IsFaceRespecting`-level Section 5 wrapper: the trivial `n = 1` case and the `2 ≤ n` canonical-start case are now combined into `IsFaceRespecting.exists_barycenter_targetFacet_of_boundarySegmentGenericity`, so the remaining obstruction is exactly the proof of `Section5BoundarySegmentGenericity`.
- [x] Make the lower-side boundary-neighbor combinatorics explicit in `Section5Path.lean`: prove `(section5LowerNeighbors v).card ≤ 1`, disjointness of lower and upper neighbor finsets, and the resulting cardinality decomposition reducing `boundaryNeighbors_card_le_two` to an upper-neighbor bound.
- [x] Collapse the remaining Section 5 wrapper gap to the true upper-side geometric hypotheses by proving `IsFaceRespecting.exists_barycenter_targetFacet_of_upperCardLeOneAndEndpointRule`.
- [x] Add a step-level Section 5 bridge closer to the manuscript: prove upper-neighbor cardinality from uniqueness of `Section5Step` continuations, build `Section5OneComplexGeometry` from step-level lower/upper/endpoint hypotheses, and expose the resulting canonical target-facet theorem.
- [x] Name the manuscript-level perturbation input explicitly as `Section5PerturbationGenericity` and connect it immediately to the canonical target-facet theorem, so the remaining frontier is the geometric proof of that structure rather than more graph translation.
- [x] Correct `IsPiecewiseAffineOn` so one affine chart agrees with `f` on the whole realization of each triangulation facet, and use that to prove the two-way bridge between `FacetImageContains` and actual points in a face realization; in particular, add `IsPiecewiseAffineOn.exists_point_in_cell_realization_of_graphNode` as the Section 5 entry point.
- [x] Formalize the support-shrinking half of the lower-step argument: generalize the nonzero-weight ambient-face lemma, show a point of a Section 5 cell lying in the lower prefix face already lies in the realization of `section5LowerPrefixVertices`, and prove that such a point mapping to `prefixBarycenter n k` makes the filtered lower subface hit `prefixBarycenter n k`.
- [x] Add the missing-room obstruction on the lower filtered subface: if `FacetImageContains f (section5LowerPrefixVertices u) b_k`, then every room in `prefixRooms n k` appears in the support of some lower-prefix vertex; also record that any actual lower-face point mapping to `b_k` has simplex support exactly `prefixRooms n k`.
- [x] Introduce the domain-side slice bridge promised by the paper’s genericity sentence: define `section5CellSlice`, package a minimal segment-hitting lower-boundary face as `Section5MinimalSliceFaceData`, and prove `Section5SimplexSliceGenericity -> Section5PerturbationGenericity -> Section5BoundarySegmentGenericity`.
- [x] Refine the slice bridge to the reviewer-facing local package: add `Section5MinimalSliceLowerBoundaryGeometry` and `Section5SimplexSliceBoundaryGeometry`, prove they collapse to `Section5MinimalSliceFaceData` / `Section5SimplexSliceGenericity`, and keep the whole bridge compiling through `Section5PerturbationGenericity` and `Section5BoundarySegmentGenericity`.
- [x] Reduce the lower-boundary geometry package to an explicit erased-face criterion on one minimal segment-hitting face: prove that if every vertex of a minimal `τ` outside `coordinateFace (prefixRooms n u.level)` can be erased while retaining a slice point on the opposite face, then all vertices of `τ` already lie in the lower prefix face; if moreover `τ.vertices.card = u.level`, this packages directly as `Section5MinimalSliceLowerBoundaryGeometry u f`.
- [x] Add the direct reroute away from minimal carrier faces: define `Section5LowerEntryFaceData` and `Section5EntryFaceGenericity`, and prove that such a lower entry face on `u.cell` yields a predecessor immediately via `exists_section5LowerStep_of_subface_card_eq_and_facetImageContains`, hence `Section5PerturbationGenericity` and `Section5BoundarySegmentGenericity`.
- [x] Package the canonical lower entry face directly on `u.cell`: prove that `(section5LowerPrefixVertices u).card = u.level` together with either `FacetImageContains f (section5LowerPrefixVertices u) (prefixBarycenter n u.level)` or an actual lower-prefix slice point immediately constructs `Section5LowerEntryFaceData u f`.
- [x] Prove that arbitrary lower-entry-face data is already canonical: `Section5Path.lean` now forces any `Section5LowerEntryFaceData u f` to have `face.vertices = section5LowerPrefixVertices u`, hence extracts the exact canonical obligations `(section5LowerPrefixVertices u).card = u.level` and `FacetImageContains f (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n) (prefixBarycenter n u.level)`.
- [x] Prove the barycenter-hit half of the canonical lower-entry problem is equivalent to a slice endpoint statement on `u.cell`: `FacetImageContains f (⟨section5LowerPrefixVertices u⟩ : SimplexFacet n) (prefixBarycenter n u.level)` now matches existence of `x ∈ section5CellSlice u f` lying in `coordinateFace (prefixRooms n u.level)`.
- [ ] Prove the manuscript’s actual lower-entry-face existence on `u.cell` in the sharpened canonical form. For each non-start cell `u`, show `(section5LowerPrefixVertices u).card = u.level` and produce a lower-prefix slice point `x ∈ section5CellSlice u f` with `x ∈ coordinateFace (prefixRooms n u.level)`; the barycenter-hit fact then follows immediately from the new slice/`FacetImageContains` equivalence. This now yields `Section5LowerEntryFaceData u f` directly and bypasses the blocked task of proving that a separately chosen minimal segment-hitting face contains the lower boundary face.
- [ ] Prove the actual `Section5BoundarySegmentGenericity` fields from the manuscript's perturbation / segment-intersection picture on the barycenter-chain preimage.
- [ ] If needed for cleanup rather than the main proof path, finish the remaining `Section5OneComplexGeometry` fields by deriving upper-continuation uniqueness and the no-upper-neighbor endpoint rule from the same geometric input.

## Completed
- [x] Read `repo/paper/arxiv-1702.07325.tex` from start to finish and mapped the proof structure.
- [x] Checked the mathematical arguments in all sections of the paper.
- [x] Recorded proof clarifications and formalization-relevant assumptions in `repo/PAPERNOTES.md`.
- [x] Drafted `repo/PLAN.md` with section-by-section dependencies, likely imports, and a Lean-oriented decomposition.
- [x] Added `repo/PaperDefinitions.lean`, `repo/PaperTheorems.lean`, and the initial simplex/support interface file.
- [x] Verified the new files with `lake build`, `lake env lean PaperDefinitions.lean`, and `lake env lean PaperTheorems.lean`.
- [x] Reworked the theorem-stating layer so `PaperDefinitions.lean` exposes the main paper definitions directly and `SimplexTriangulation` records cover/intersection data explicitly.
- [x] Added the first proof-facing simplex and interior-target support lemmas in `repo/Arxiv170207325/SimplexModel.lean` and `repo/Arxiv170207325/InteriorTarget.lean`.
