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
- [ ] Tie `section5StartNode` to the actual boundary-chain graph data: show it is a graph node in the intended finite node set and prove its degree-one start property.
- [ ] Prove the Section 5 local degree hypotheses for `Section5Adjacent` from the paper's generic segment-intersection assumptions, then instantiate `section5SimpleGraph.exists_targetFacet_of_endpoint_rule` on the real Section 5 component.

## Completed
- [x] Read `repo/paper/arxiv-1702.07325.tex` from start to finish and mapped the proof structure.
- [x] Checked the mathematical arguments in all sections of the paper.
- [x] Recorded proof clarifications and formalization-relevant assumptions in `repo/PAPERNOTES.md`.
- [x] Drafted `repo/PLAN.md` with section-by-section dependencies, likely imports, and a Lean-oriented decomposition.
- [x] Added `repo/PaperDefinitions.lean`, `repo/PaperTheorems.lean`, and the initial simplex/support interface file.
- [x] Verified the new files with `lake build`, `lake env lean PaperDefinitions.lean`, and `lake env lean PaperTheorems.lean`.
- [x] Reworked the theorem-stating layer so `PaperDefinitions.lean` exposes the main paper definitions directly and `SimplexTriangulation` records cover/intersection data explicitly.
- [x] Added the first proof-facing simplex and interior-target support lemmas in `repo/Arxiv170207325/SimplexModel.lean` and `repo/Arxiv170207325/InteriorTarget.lean`.
