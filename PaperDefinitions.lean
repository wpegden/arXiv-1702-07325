import Arxiv170207325.PaperDefinitionsCore

/-!
# Paper Definitions

This root-level file is the stable paper-facing entrypoint requested by the supervisor.
The actual Lean definitions live in `Arxiv170207325.PaperDefinitionsCore` so that they can be
imported cleanly by the namespaced support files and by `PaperTheorems.lean`.

The imported core file currently contains the paper-facing definitions
`RentSimplex`, `SimplexFacet`, `SimplexTriangulation`, `IsSpernerLabeling`,
`FacetSupportsSecretiveAssignment`, `FacetCapturesMultiplicityTarget`, and the
auxiliary simplex/face/labeling interfaces used by the theorem statements.
-/
