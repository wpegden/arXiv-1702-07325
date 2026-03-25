# Tasks

<!-- SUPERVISOR_TASKS:START -->
## Supervisor Tasks
- [x] Create `PaperDefinitions.lean` with the definitions needed to state the paper results.
- [x] Create `PaperTheorems.lean` with theorem statements as close to the paper as Lean allows.
- [x] Keep the files easy for a human to compare against the paper.
- [x] Make both files syntactically valid Lean.
<!-- SUPERVISOR_TASKS:END -->

## Worker Tasks
- [ ] Strengthen `repo/Arxiv170207325/SimplexModel.lean` with the first proof-facing lemmas on supports, coordinate faces, and cyclic permutation.
- [ ] Decide whether `SimplexTriangulation` should gain explicit cover/gluing fields before the proof phase begins in earnest.
- [ ] Begin the first proof-facing support file for the interior target-hitting theorem from Section 5.

## Completed
- [x] Read `repo/paper/arxiv-1702.07325.tex` from start to finish and mapped the proof structure.
- [x] Checked the mathematical arguments in all sections of the paper.
- [x] Recorded proof clarifications and formalization-relevant assumptions in `repo/PAPERNOTES.md`.
- [x] Drafted `repo/PLAN.md` with section-by-section dependencies, likely imports, and a Lean-oriented decomposition.
- [x] Added `repo/PaperDefinitions.lean`, `repo/PaperTheorems.lean`, and the initial simplex/support interface file.
- [x] Verified the new files with `lake build`, `lake env lean PaperDefinitions.lean`, and `lake env lean PaperTheorems.lean`.
