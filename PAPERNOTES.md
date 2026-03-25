# Paper Notes

## Paper-Check Status
- Checked the full manuscript on 2026-03-25.
- No genuine contradiction or irreparable proof gap was found.
- The main issues are proof clarifications that should be made explicit before Lean formalization.

## Formalization-Critical Modeling Choices
- The phrase "roommates do not care about one-cent error margins" needs a precise mathematical replacement. The proofs use a local-constancy principle: after choosing a triangulation with sufficiently small mesh, the acceptable-room data is stable on each small simplex. For Lean it will be cleaner to formalize the paper directly in terms of Sperner-style labelings on a triangulation, with the rent/preference discussion recorded as motivation.
- At a rent division lying on a proper face of the simplex, the free rooms are exactly the rooms whose coordinates are zero, i.e. the vertices not belonging to that face. This complement convention is easy to lose track of and is responsible for the permutation trick in the main proof.

## Corrections And Clarifications
- Section 2, Sperner lemma, Proof 1: the trap-door argument is standard and correct, but the parity claim about inaccessible fully labeled simplices is compressed. The clean formulation is that every connected component of the door graph without a boundary door is a path or cycle, so inaccessible degree-1 rooms occur in pairs.
- Section 2, Sperner lemma, Proof 2: the surjectivity step is deferred to Section 5. For the formalization plan, treat the needed lemma as: a piecewise-linear self-map of a simplex that preserves every face setwise hits the barycenter.
- Section 3, three-roommates, Proof 1: the nine pair-labels are partitioned into three cyclic classes. A fully labeled small triangle forces Larry and Moe each to use at least two room labels on that triangle, and also forces every room label to appear for at least one of them. This is the exact combinatorial statement needed later; it is worth isolating as a finite case check rather than leaving it as "simple to check."
- Section 3, three-roommates, Proof 2: the boundary-degree-one claim is valid once the original vertices are chosen so that both visible roommates pick the same free room at each vertex, and the three rooms are chosen once each around the boundary. Then each boundary edge maps to the corresponding adjacent edge path, so the image winds once around the triangle.
- Section 4, general case, lines 283-301: the permutation/Sperner argument is mathematically sound but too terse. For a boundary vertex supported on a proper face with vertex set `I`, choose `i in I` with `pi(i) notin I`; such an `i` exists because `pi` is an `n`-cycle, so no proper nonempty subset is `pi`-stable. Room `pi(i)` is free on that face, so we may assign that room. After composing with `f^-1`, the encoded label is `i`, which lies in the supporting face. This is the real reason `f^-1` applied to `lambda_j` gives a Sperner labeling.
- Section 4, Hall step: from the proved statement "any `k` visible roommates jointly see at least `k+1` room labels on `tau`", deleting the secretive roommate's chosen room leaves at least `k` available labels for every `k`-subset. That is the exact Hall condition for the remaining bipartite graph.
- Section 5, algorithmic section: the argument is conceptually correct but written at a sketch level. The genericity assumption should be read as a perturbation of the barycenter chain so that the preimage of the chain under `lambda` is a finite 1-dimensional cell complex. Then the component containing `e1` has one endpoint at `e1`; its other endpoint must be an `(n-1)`-simplex whose image contains the barycenter. This is the repair to keep in mind if the text needs to be formalized more rigorously.
- Section 5, start of the path-following argument: besides the perturbation-to-a-1-complex claim, the sentence about "the edge of `T` that contains `e_1` and subdivides `[e_1,e_2]`" implicitly uses that the triangulation restricts to an honest 1-dimensional simplicial subdivision of the boundary face `[e_1,e_2]`. In Lean this is a separate structural requirement: the current finite triangulation wrapper does not by itself expose the induced boundary subdivision or the resulting uniqueness of the first edge at `e_1`.
- Section 6, first generalization theorem: when `y` is assumed not to lie in the convex hull of any `n` lattice points, the simplex `tau` containing `x` must actually be a facet. Otherwise `lambda(tau)` would lie in the convex hull of at most `n` lattice points, contradicting `lambda(x) = y`.
- Section 6, second generalization theorem: the weight choice `alpha_j = (k_j + 1/m - 1)/(n+1)` is valid because `k_j >= 1` gives `alpha_j > 0` and `sum_j alpha_j = 1` follows from `sum_j k_j = n + m`. The final counting step uses integrality: the number of positive `beta_ij` is an integer strictly greater than `k_j - 1`, hence at least `k_j`.

## Open Questions
- None at the end of the paper-check pass.
