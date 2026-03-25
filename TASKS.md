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
- [ ] Resolve the current Section 5 modeling gap: either strengthen the triangulation support layer to expose the induced boundary subdivisions of the prefix faces, or formalize the perturbation/genericity argument that turns the barycenter-chain preimage into a finite 1-dimensional cell complex.
- [ ] Continue tying `section5StartNode` to the actual boundary-chain graph data all the way through degree one: identify its unique level-1 successor and show that its degree in the actual start component is exactly one.
- [ ] Prove the raw start-component hypotheses for `section5StartComponentGraph.exists_targetFacet_of_endpoint_rule`: the start vertex has one neighbor on the boundary chain, every node has at most two neighbors, and every non-start degree-one node is an endpoint hitting the barycenter.
- [ ] Discharge `Section5SegmentGeometry` from actual Section 5 lemmas on the barycenter-chain preimage: prove the unique boundary successor, the at-most-two-neighbor bound, and the non-start endpoint characterization on the real start component.

## Completed
- [x] Read `repo/paper/arxiv-1702.07325.tex` from start to finish and mapped the proof structure.
- [x] Checked the mathematical arguments in all sections of the paper.
- [x] Recorded proof clarifications and formalization-relevant assumptions in `repo/PAPERNOTES.md`.
- [x] Drafted `repo/PLAN.md` with section-by-section dependencies, likely imports, and a Lean-oriented decomposition.
- [x] Added `repo/PaperDefinitions.lean`, `repo/PaperTheorems.lean`, and the initial simplex/support interface file.
- [x] Verified the new files with `lake build`, `lake env lean PaperDefinitions.lean`, and `lake env lean PaperTheorems.lean`.
- [x] Reworked the theorem-stating layer so `PaperDefinitions.lean` exposes the main paper definitions directly and `SimplexTriangulation` records cover/intersection data explicitly.
- [x] Added the first proof-facing simplex and interior-target support lemmas in `repo/Arxiv170207325/SimplexModel.lean` and `repo/Arxiv170207325/InteriorTarget.lean`.
