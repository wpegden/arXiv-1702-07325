# Tasks

<!-- SUPERVISOR_TASKS:START -->
## Supervisor Tasks
- [x] Use `repo/paper/arxiv-1702.07325.tex`, `PAPERNOTES.md`, and the current repo state to build `PLAN.md`.
- [x] Produce a comprehensive roadmap for definitions, theorem statements, and proof dependencies.
- [x] Identify what can come from mathlib versus what must be formalized here.
- [ ] Use `NEED_INPUT` for external-result or design-choice questions that need a human decision.
<!-- SUPERVISOR_TASKS:END -->

## Worker Tasks
- [ ] Create `repo/PaperDefinitions.lean` with the paper-facing simplex, triangulation, and labeling interfaces from `repo/PLAN.md`.
- [ ] Create `repo/PaperTheorems.lean` with the central target-hitting theorem, Sperner theorem, main secretive-roommate theorem, and Section 6 theorem statements.
- [ ] Start `repo/Arxiv170207325/SimplexModel.lean` with the ambient simplex API, barycenter lemmas, and cyclic permutation encoding.

## Completed
- [x] Read `repo/paper/arxiv-1702.07325.tex` from start to finish and mapped the proof structure.
- [x] Checked the mathematical arguments in all sections of the paper.
- [x] Recorded proof clarifications and formalization-relevant assumptions in `repo/PAPERNOTES.md`.
- [x] Drafted `repo/PLAN.md` with section-by-section dependencies, likely imports, and a Lean-oriented decomposition.
