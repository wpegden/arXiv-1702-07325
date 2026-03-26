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
- [x] Prove that under face preservation the Section 5 start node is a genuine graph node by showing any triangulation facet covering `e₁` actually contains `e₁` as a vertex.
- [x] Add the first explicit boundary-edge infrastructure for `[e₁,e₂]`: identify the second boundary vertex, parametrize points of `coordinateFace (prefixRooms n 2)` along that edge, prove every facet has at most two such boundary vertices, and package level-1 cells containing `e₁` as the boundary-vertex pair of any containing facet.
- [x] Use `face_intersection` plus the boundary-edge convex-hull API to prove any two level-1 Section 5 cells through `e₁` coincide, and package the resulting uniqueness/start-degree-one statements under an existence hypothesis for the first boundary successor.
- [x] Finish the start-boundary step by proving existence of the actual first boundary edge through `e₁` in the induced subdivision of `[e₁,e₂]`, then remove the remaining existence hypothesis from the unique level-1 successor and start-degree-one wrappers.
- [x] Generalize the induced boundary-face API to arbitrary prefix faces `conv{e₁, ..., e_{k+1}}`, including induced face realizations for points already lying in those coordinate faces, so later degree proofs are not hard-coded to the `k = 1` boundary edge.
- [x] Prove the affine-dimension/cardinality bound for induced prefix faces inside any triangulation face, and use it to show lower-level predecessors in the Section 5 graph are unique once the upper cell is fixed.
- [x] Prove that every non-start node in the actual start component already has a lower neighbor by combining shortest-path geometry with lower-neighbor uniqueness, and package the reduction from the remaining local-degree proof to upper-neighbor uniqueness plus the no-upper-neighbor endpoint claim.
- [x] Use the new `repo/Arxiv170207325/PiecewiseAffine.lean` face-realization API to formulate the missing Section 5 perturbation/genericity input directly in terms of actual preimage points on prefix faces, rather than only convex-hull hits.
- [x] Add the first collapsed-segment support for the stuck Section 5 route: characterize `prefixBarycenterSegment` by `AffineMap.lineMap`, prove any linear map annihilating the segment direction is constant on that segment, prove intersection with the smaller ambient prefix face forces the lower endpoint, choose the explicit collapse map `prefixSegmentCollapseMap`, package `IsSection5GraphNode.exists_faceHitWitness_eq_under_prefixSegmentCollapse_of_piecewiseAffineOn`, `IsSection5GraphNode.cell_eq_prefixFace_of_incidentFacet`, and `IsSection5GraphNode.exists_point_in_incidentPrefixFace_zeroFiber_of_piecewiseAffineOn`, then sharpen the ambient/facet-local geometry by proving `prefixRooms_succ_eq_insert_last`, `prefixSegmentCollapseMap_lastVertex`, `mem_segment_prefixBarycenter_lastVertex_iff_prefixSegmentCollapse_eq_zero_of_mem_ambientFace`, `eq_prefixBarycenter_of_prefixSegmentCollapse_eq_zero_of_mem_lowerAmbientFace`, `SimplexFacet.map_mem_ambientCoordinateFace_of_mem_section5PrefixFace_realization`, the resulting pointwise segment/lower-barycenter corollaries on induced prefix faces, and the domain-side affine-subspace model `prefixSegmentZeroFiber` together with the corresponding graph-node witness wrapper.
- [ ] Prove the remaining facet-local collapsed-fiber theorem behind `section5LocalOneComplexGeometry_of_uniqueUpperOrEndpoint`: for a start-component node `v`, use `prefixSegmentZeroFiber n v.level g` together with `IsSection5GraphNode.exists_point_in_incidentPrefixFace_mem_segmentZeroFiber_of_piecewiseAffineOn` to show that the zero fiber inside the incident prefix face is exactly the explicit slice from `b_k` to `e_{k+1}`, has at most one upper codimension-one continuation, and that the empty-upper-continuation case already implies `IsSection5Endpoint T f v.1.1`.
- [ ] Discharge `Section5SegmentGeometry` from actual Section 5 lemmas on the barycenter-chain preimage by combining the finished start-boundary entrance, the lower-neighbor reductions, and the remaining upper-continuation/endpoint geometry on the real start component.

## Completed
- [x] Read `repo/paper/arxiv-1702.07325.tex` from start to finish and mapped the proof structure.
- [x] Checked the mathematical arguments in all sections of the paper.
- [x] Recorded proof clarifications and formalization-relevant assumptions in `repo/PAPERNOTES.md`.
- [x] Drafted `repo/PLAN.md` with section-by-section dependencies, likely imports, and a Lean-oriented decomposition.
- [x] Added `repo/PaperDefinitions.lean`, `repo/PaperTheorems.lean`, and the initial simplex/support interface file.
- [x] Verified the new files with `lake build`, `lake env lean PaperDefinitions.lean`, and `lake env lean PaperTheorems.lean`.
- [x] Reworked the theorem-stating layer so `PaperDefinitions.lean` exposes the main paper definitions directly and `SimplexTriangulation` records cover/intersection data explicitly.
- [x] Added the first proof-facing simplex and interior-target support lemmas in `repo/Arxiv170207325/SimplexModel.lean` and `repo/Arxiv170207325/InteriorTarget.lean`.
