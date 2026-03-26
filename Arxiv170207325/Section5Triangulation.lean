import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Finset.Insert
import PaperDefinitions

noncomputable section

namespace Arxiv170207325

/-- The vertices of a simplex facet all lie in the ambient simplex. -/
theorem SimplexFacet.pointSet_subset_scaledSimplex {n : ℕ} (τ : SimplexFacet n) :
    τ.pointSet ⊆ scaledSimplex 1 n := by
  rintro x ⟨v, hv, rfl⟩
  simpa [RentSimplex, scaledSimplex] using v.2

/-- The common vertex set of two facets. -/
def SimplexFacet.commonVertices {n : ℕ} (τ₁ τ₂ : SimplexFacet n) : Finset (RentSimplex n) :=
  τ₁.vertices ∩ τ₂.vertices

@[simp]
theorem mem_commonVertices_iff {n : ℕ} {τ₁ τ₂ : SimplexFacet n} {v : RentSimplex n} :
    v ∈ τ₁.commonVertices τ₂ ↔ v ∈ τ₁.vertices ∧ v ∈ τ₂.vertices := by
  simp [SimplexFacet.commonVertices]

/-- One simplex is a subface of another when its vertices are a subset of the larger simplex's
vertices. -/
def SimplexFacet.IsSubfaceOf {n : ℕ} (σ τ : SimplexFacet n) : Prop :=
  σ.vertices ⊆ τ.vertices

@[simp]
theorem SimplexFacet.isSubfaceOf_refl {n : ℕ} (τ : SimplexFacet n) : τ.IsSubfaceOf τ :=
  Finset.Subset.refl _

theorem SimplexFacet.isSubfaceOf_trans {n : ℕ} {ρ σ τ : SimplexFacet n}
    (hρσ : ρ.IsSubfaceOf σ) (hστ : σ.IsSubfaceOf τ) : ρ.IsSubfaceOf τ :=
  hρσ.trans hστ

/-- The common face spanned by the shared vertices of two facets. -/
def SimplexFacet.commonFace {n : ℕ} (τ₁ τ₂ : SimplexFacet n) : SimplexFacet n where
  vertices := τ₁.commonVertices τ₂

theorem SimplexFacet.commonFace_isSubfaceLeft {n : ℕ} (τ₁ τ₂ : SimplexFacet n) :
    (τ₁.commonFace τ₂).IsSubfaceOf τ₁ := by
  intro v hv
  exact (mem_commonVertices_iff.mp hv).1

theorem SimplexFacet.commonFace_isSubfaceRight {n : ℕ} (τ₁ τ₂ : SimplexFacet n) :
    (τ₁.commonFace τ₂).IsSubfaceOf τ₂ := by
  intro v hv
  exact (mem_commonVertices_iff.mp hv).2

theorem SimplexFacet.commonVertices_subset_left {n : ℕ} (τ₁ τ₂ : SimplexFacet n) :
    τ₁.commonVertices τ₂ ⊆ τ₁.vertices :=
  (τ₁.commonFace_isSubfaceLeft τ₂)

theorem SimplexFacet.commonVertices_subset_right {n : ℕ} (τ₁ τ₂ : SimplexFacet n) :
  τ₁.commonVertices τ₂ ⊆ τ₂.vertices :=
  (τ₁.commonFace_isSubfaceRight τ₂)

theorem SimplexFacet.stdSimplexVertex_mem_vertices_of_mem_realization {n : ℕ}
    (τ : SimplexFacet n) (i : RoomIndex n)
    (hx : ((stdSimplex.vertex (S := ℝ) i : RentSimplex n) : RentCoordinates n) ∈ τ.realization) :
    stdSimplex.vertex (S := ℝ) i ∈ τ.vertices := by
  have hproj :
      ConvexOn ℝ (Set.univ : Set (RentCoordinates n)) (LinearMap.proj (R := ℝ) i) :=
    (LinearMap.proj (R := ℝ) i).convexOn convex_univ
  have hx' :
      ((stdSimplex.vertex (S := ℝ) i : RentSimplex n) : RentCoordinates n) ∈
        convexHull ℝ τ.pointSet := by
    simpa [SimplexFacet.realization] using hx
  obtain ⟨y, hyτ, hyge⟩ := hproj.exists_ge_of_mem_convexHull
    (t := τ.pointSet) (by intro y _; simp) hx'
  rcases hyτ with ⟨v, hv, rfl⟩
  have hcoord : (1 : ℝ) ≤ v i := by
    simpa using hyge
  have hEqCoord : v i = 1 := le_antisymm (stdSimplex.le_one v i) hcoord
  simpa [eq_stdSimplex_vertex_of_apply_eq_one hEqCoord] using hv

theorem SimplexTriangulation.mem_subset_of_vertex_mem_convexHull {n : ℕ}
    {T : SimplexTriangulation n} {τ : SimplexFacet n} (hτ : τ ∈ T.facets)
    {S : Finset (RentSimplex n)} (hS : S ⊆ τ.vertices) {v : RentSimplex n} (hv : v ∈ τ.vertices)
    (hx :
      ((v : RentSimplex n) : RentCoordinates n) ∈
        convexHull ℝ (((↑) : RentSimplex n → RentCoordinates n) '' (S : Set (RentSimplex n)))) :
    v ∈ S := by
  classical
  let p : τ.vertices → RentCoordinates n := fun x => ((x : RentSimplex n) : RentCoordinates n)
  let s : Set τ.vertices := {x | (x : RentSimplex n) ∈ S}
  let i : τ.vertices := ⟨v, hv⟩
  have hAffine : AffineIndependent ℝ p := T.facet_affineIndependent τ hτ
  have hs_image :
      p '' s = (((↑) : RentSimplex n → RentCoordinates n) '' (S : Set (RentSimplex n))) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x : RentSimplex n), hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hS hx⟩, by simpa [s], rfl⟩
  have hi_mem :
      p i ∈ affineSpan ℝ (p '' s) := by
    have hx' : p i ∈ convexHull ℝ (p '' s) := by
      rw [hs_image]
      simpa [p, i] using hx
    exact (convexHull_subset_affineSpan (𝕜 := ℝ) (p '' s)) hx'
  have hsum :
      ∑ j, Function.update (fun _ : τ.vertices => (0 : ℝ)) i 1 j = 1 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Function.update, hji]
    · simp
  by_contra hvS
  have hi_not : i ∉ s := by
    simp [s, i, hvS]
  have hi_eq :
      (Finset.univ.affineCombination ℝ p
        (Function.update (fun _ : τ.vertices => (0 : ℝ)) i 1)) = p i := by
    refine Finset.univ.affineCombination_of_eq_one_of_eq_zero
      (Function.update (fun _ : τ.vertices => (0 : ℝ)) i 1) p (by simp) (by simp) ?_
    intro j _ hji
    simp [Function.update, hji]
  have hzero := hAffine.eq_zero_of_affineCombination_mem_affineSpan hsum
    (by rwa [hi_eq]) (i := i) (by simp) hi_not
  simpa [i] using hzero

theorem SimplexTriangulation.mem_vertices_of_vertex_mem_realization {n : ℕ}
    {T : SimplexTriangulation n} {τ₁ τ₂ : SimplexFacet n}
    (hτ₁ : τ₁ ∈ T.facets) (hτ₂ : τ₂ ∈ T.facets) {v : RentSimplex n} (hv₂ : v ∈ τ₂.vertices)
    (hv₁ : ((v : RentSimplex n) : RentCoordinates n) ∈ τ₁.realization) :
    v ∈ τ₁.vertices := by
  have hv₂' :
      ((v : RentSimplex n) : RentCoordinates n) ∈ τ₂.realization := by
    rw [SimplexFacet.realization]
    exact subset_convexHull ℝ _ <| by
      exact Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n) hv₂
  have hv_inter :
      ((v : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ (τ₁.intersectionPointSet τ₂) := by
    rw [← T.face_intersection hτ₁ hτ₂]
    exact ⟨hv₁, hv₂'⟩
  have hv_common :
      v ∈ τ₁.commonVertices τ₂ := by
    refine T.mem_subset_of_vertex_mem_convexHull hτ₂ (S := τ₁.commonVertices τ₂)
      (SimplexFacet.commonVertices_subset_right τ₁ τ₂) hv₂ ?_
    simpa [SimplexFacet.intersectionPointSet, SimplexFacet.commonVertices] using hv_inter
  exact (mem_commonVertices_iff.mp hv_common).1

theorem SimplexFacet.realization_mono_of_isSubface {n : ℕ} {σ τ : SimplexFacet n}
    (hστ : σ.IsSubfaceOf τ) : σ.realization ⊆ τ.realization := by
  rw [SimplexFacet.realization, SimplexFacet.realization]
  refine convexHull_mono ?_
  rintro x ⟨v, hv, rfl⟩
  exact Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n) (hστ hv)

/-- Every geometric realization of a simplex facet lies in the ambient simplex. -/
theorem SimplexFacet.realization_subset_scaledSimplex {n : ℕ} (τ : SimplexFacet n) :
    τ.realization ⊆ scaledSimplex 1 n := by
  rw [SimplexFacet.realization]
  refine convexHull_min τ.pointSet_subset_scaledSimplex ?_
  simpa [RentSimplex, scaledSimplex] using (convex_stdSimplex ℝ (RoomIndex n))

theorem SimplexFacet.realization_eq_segment_of_vertices_eq_pair {n : ℕ} (τ : SimplexFacet n)
    {x y : RentSimplex n} (hτ : τ.vertices = {x, y}) :
    τ.realization =
      segment ℝ ((x : RentSimplex n) : RentCoordinates n) ((y : RentSimplex n) : RentCoordinates n) := by
  rw [SimplexFacet.realization, SimplexFacet.pointSet, hτ]
  have himage :
      (((↑) : RentSimplex n → RentCoordinates n) '' ↑({x, y} : Finset (RentSimplex n))) =
        ({((x : RentSimplex n) : RentCoordinates n), ((y : RentSimplex n) : RentCoordinates n)} :
          Set (RentCoordinates n)) := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      simp [Finset.coe_insert, Finset.coe_singleton] at ha
      rcases ha with rfl | rfl <;> simp
    · intro hz
      rcases hz with rfl | rfl
      · exact ⟨x, by simp [Finset.coe_insert, Finset.coe_singleton], rfl⟩
      · exact ⟨y, by simp [Finset.coe_insert, Finset.coe_singleton], rfl⟩
  rw [himage]
  exact convexHull_pair
    (((x : RentSimplex n) : RentCoordinates n))
    (((y : RentSimplex n) : RentCoordinates n))

/-- The codimension-one adjacency relation on triangulation facets used by the Section 5 graph. -/
def SimplexTriangulation.AdjacentFacets {n : ℕ} (T : SimplexTriangulation n)
    (τ₁ τ₂ : SimplexFacet n) : Prop :=
  τ₁ ∈ T.facets ∧ τ₂ ∈ T.facets ∧ τ₁ ≠ τ₂ ∧ (τ₁.commonVertices τ₂).card = n - 1

theorem SimplexTriangulation.adjacentFacets_left_mem {n : ℕ} {T : SimplexTriangulation n}
    {τ₁ τ₂ : SimplexFacet n} (h : T.AdjacentFacets τ₁ τ₂) : τ₁ ∈ T.facets :=
  h.1

theorem SimplexTriangulation.adjacentFacets_right_mem {n : ℕ} {T : SimplexTriangulation n}
    {τ₁ τ₂ : SimplexFacet n} (h : T.AdjacentFacets τ₁ τ₂) : τ₂ ∈ T.facets :=
  h.2.1

theorem SimplexTriangulation.adjacentFacets_ne {n : ℕ} {T : SimplexTriangulation n}
    {τ₁ τ₂ : SimplexFacet n} (h : T.AdjacentFacets τ₁ τ₂) : τ₁ ≠ τ₂ :=
  h.2.2.1

theorem SimplexTriangulation.adjacentFacets_commonVertices_card {n : ℕ}
    {T : SimplexTriangulation n} {τ₁ τ₂ : SimplexFacet n} (h : T.AdjacentFacets τ₁ τ₂) :
    (τ₁.commonVertices τ₂).card = n - 1 :=
  h.2.2.2

theorem SimplexTriangulation.adjacentFacets_symm {n : ℕ} {T : SimplexTriangulation n}
    {τ₁ τ₂ : SimplexFacet n} (h : T.AdjacentFacets τ₁ τ₂) : T.AdjacentFacets τ₂ τ₁ := by
  refine ⟨adjacentFacets_right_mem h, adjacentFacets_left_mem h, ?_, ?_⟩
  · exact (adjacentFacets_ne h).symm
  · rw [SimplexFacet.commonVertices, Finset.inter_comm]
    exact adjacentFacets_commonVertices_card h

theorem SimplexTriangulation.adjacentFacets_commonFace_left {n : ℕ}
    {T : SimplexTriangulation n} {τ₁ τ₂ : SimplexFacet n} (_h : T.AdjacentFacets τ₁ τ₂) :
    (τ₁.commonFace τ₂).IsSubfaceOf τ₁ :=
  τ₁.commonFace_isSubfaceLeft τ₂

theorem SimplexTriangulation.adjacentFacets_commonFace_right {n : ℕ}
    {T : SimplexTriangulation n} {τ₁ τ₂ : SimplexFacet n} (_h : T.AdjacentFacets τ₁ τ₂) :
    (τ₁.commonFace τ₂).IsSubfaceOf τ₂ :=
  τ₁.commonFace_isSubfaceRight τ₂

/-- A cell of the triangulation is any simplex that occurs as a subface of one of its facets. -/
def SimplexTriangulation.IsFace {n : ℕ} (T : SimplexTriangulation n) (σ : SimplexFacet n) : Prop :=
  ∃ τ ∈ T.facets, σ.IsSubfaceOf τ

theorem SimplexTriangulation.facet_isFace {n : ℕ} {T : SimplexTriangulation n}
    {τ : SimplexFacet n} (hτ : τ ∈ T.facets) : T.IsFace τ :=
  ⟨τ, hτ, SimplexFacet.isSubfaceOf_refl _⟩

theorem IsPiecewiseAffineOn.facetImageContains_of_mem_realization
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsPiecewiseAffineOn T f) {σ : SimplexFacet n} (hσ : T.IsFace σ)
    {x : RentSimplex n} (hx : ((x : RentSimplex n) : RentCoordinates n) ∈ σ.realization) :
    FacetImageContains f σ (f x) := by
  rcases hσ with ⟨τ, hτ, hστ⟩
  rcases hf τ hτ with ⟨g, hg⟩
  have hxτ : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization :=
    SimplexFacet.realization_mono_of_isSubface hστ hx
  have hfx : f x = g x := (hg x hxτ).symm
  have hg_mem : g x ∈ convexHull ℝ (g '' σ.pointSet) := by
    have hx' : ((x : RentSimplex n) : RentCoordinates n) ∈ convexHull ℝ σ.pointSet := by
      simpa [SimplexFacet.realization] using hx
    have hx'' : g x ∈ g '' convexHull ℝ σ.pointSet := ⟨x, hx', rfl⟩
    rwa [AffineMap.image_convexHull] at hx''
  have hg_pointSet :
      g '' σ.pointSet = ((fun v : RentSimplex n => f v) '' (σ.vertices : Set (RentSimplex n))) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨v, hv, rfl⟩
      refine ⟨v, hv, ?_⟩
      have hvσ : ((v : RentSimplex n) : RentCoordinates n) ∈ σ.realization := by
        rw [SimplexFacet.realization]
        exact subset_convexHull ℝ _ <| Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n) hv
      have hvτ : ((v : RentSimplex n) : RentCoordinates n) ∈ τ.realization :=
        SimplexFacet.realization_mono_of_isSubface hστ hvσ
      exact (hg v hvτ).symm
    · rintro ⟨v, hv, rfl⟩
      refine ⟨((v : RentSimplex n) : RentCoordinates n), ?_, ?_⟩
      · exact Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n) hv
      · symm
        have hvσ : ((v : RentSimplex n) : RentCoordinates n) ∈ σ.realization := by
          rw [SimplexFacet.realization]
          exact subset_convexHull ℝ _ <| Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n) hv
        have hvτ : ((v : RentSimplex n) : RentCoordinates n) ∈ τ.realization :=
          SimplexFacet.realization_mono_of_isSubface hστ hvσ
        exact (hg v hvτ).symm
  rw [FacetImageContains, FacetImageHull]
  rw [← hg_pointSet]
  simpa [hfx] using hg_mem

theorem IsPiecewiseAffineOn.exists_point_in_realization_of_facetImageContains
    {n : ℕ} [NeZero n] {T : SimplexTriangulation n} {f : SelfMapOnRentSimplex n}
    (hf : IsPiecewiseAffineOn T f) {σ : SimplexFacet n} (hσ : T.IsFace σ)
    {y : RentCoordinates n} (hy : FacetImageContains f σ y) :
    ∃ x : RentSimplex n, ((x : RentSimplex n) : RentCoordinates n) ∈ σ.realization ∧ f x = y := by
  classical
  rcases hσ with ⟨τ, hτ, hστ⟩
  rcases hf τ hτ with ⟨g, hg⟩
  let s : Finset (RentCoordinates n) := σ.vertices.image fun v : RentSimplex n => f v
  have hyconv : y ∈ convexHull ℝ (s : Set (RentCoordinates n)) := by
    simpa [FacetImageContains, FacetImageHull, s] using hy
  obtain ⟨w, hw_nonneg, hw_sum, hw_center⟩ := (Finset.mem_convexHull).mp hyconv
  have hpreimage : ∀ z ∈ s, ∃ v : RentSimplex n, v ∈ σ.vertices ∧ f v = z := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  let t : Finset {z // z ∈ s} := s.attach
  let weights : {z // z ∈ s} → ℝ := fun z => w z.1
  let pickVertex : {z // z ∈ s} → RentSimplex n := fun z =>
    Classical.choose (hpreimage z.1 z.2)
  let pickPoint : {z // z ∈ s} → RentCoordinates n := fun z =>
    ((pickVertex z : RentSimplex n) : RentCoordinates n)
  have hweights_nonneg : ∀ z ∈ t, 0 ≤ weights z := by
    intro z hz
    simpa [t, weights] using hw_nonneg z.1 z.2
  have hweights_sum : ∑ z ∈ t, weights z = 1 := by
    dsimp [t, weights]
    rw [Finset.sum_attach]
    exact hw_sum
  have hpick_mem_pointSet : ∀ z ∈ t, pickPoint z ∈ σ.pointSet := by
    intro z hz
    rcases Classical.choose_spec (hpreimage z.1 z.2) with ⟨hvσ, _⟩
    exact Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n) hvσ
  have hpick_realization :
      t.centerMass weights pickPoint ∈ σ.realization := by
    rw [SimplexFacet.realization]
    exact Finset.centerMass_mem_convexHull t hweights_nonneg (by
      rw [hweights_sum]
      norm_num) hpick_mem_pointSet
  have hpick_in_τ :
      ∀ z ∈ t, ((pickVertex z : RentSimplex n) : RentCoordinates n) ∈ τ.realization := by
    intro z hz
    rw [SimplexFacet.realization]
    rcases Classical.choose_spec (hpreimage z.1 z.2) with ⟨hvσ, _⟩
    exact subset_convexHull ℝ _ <|
      Set.mem_image_of_mem ((↑) : RentSimplex n → RentCoordinates n) (hστ hvσ)
  have hg_on_picks : ∀ z ∈ t, g (pickPoint z) = z.1 := by
    intro z hz
    rcases Classical.choose_spec (hpreimage z.1 z.2) with ⟨_, hvfz⟩
    have hτreal : ((pickVertex z : RentSimplex n) : RentCoordinates n) ∈ τ.realization :=
      hpick_in_τ z hz
    simpa [pickPoint, pickVertex] using (hg (pickVertex z) hτreal).trans hvfz
  have hg_centerMass : g (t.centerMass weights pickPoint) = y := by
    calc
      g (t.centerMass weights pickPoint)
          = t.centerMass weights (fun z => g (pickPoint z)) := by
              rw [← affineCombination_eq_centerMass (R := ℝ) (t := t)
                (p := pickPoint) (w := weights) hweights_sum]
              rw [t.map_affineCombination (k := ℝ) pickPoint weights hweights_sum g]
              rw [affineCombination_eq_centerMass (R := ℝ) (t := t)
                (p := g ∘ pickPoint) (w := weights) hweights_sum]
              rfl
      _ = t.centerMass weights (fun z => z.1) := by
            refine Finset.centerMass_congr_fun ?_
            intro z hz _hwz
            exact hg_on_picks z hz
      _ = y := by
            have hcenter_attach :
                t.centerMass weights (fun z => z.1) = s.centerMass w id := by
              dsimp [t, weights]
              rw [Finset.centerMass, Finset.centerMass]
              simp only [id_eq]
              rw [← s.sum_attach (f := fun z : RentCoordinates n => w z),
                ← s.sum_attach (f := fun z : RentCoordinates n => w z • z)]
            exact hcenter_attach.trans hw_center
  let x : RentSimplex n := ⟨t.centerMass weights pickPoint, by
    simpa [RentSimplex, scaledSimplex] using σ.realization_subset_scaledSimplex hpick_realization⟩
  have hx_realization : ((x : RentSimplex n) : RentCoordinates n) ∈ σ.realization :=
    hpick_realization
  have hxτ_realization : ((x : RentSimplex n) : RentCoordinates n) ∈ τ.realization :=
    SimplexFacet.realization_mono_of_isSubface hστ hx_realization
  refine ⟨x, hx_realization, ?_⟩
  calc
    f x = g x := (hg x hxτ_realization).symm
    _ = y := by simpa [x, t, weights, pickPoint] using hg_centerMass

/-- The facets of `T` incident to a cell `σ`. -/
def SimplexTriangulation.incidentFacets {n : ℕ} (T : SimplexTriangulation n)
    (σ : SimplexFacet n) : Finset (SimplexFacet n) := by
  classical
  exact T.facets.filter fun τ => σ.IsSubfaceOf τ

@[simp]
theorem SimplexTriangulation.mem_incidentFacets_iff {n : ℕ} {T : SimplexTriangulation n}
    {σ τ : SimplexFacet n} :
    τ ∈ T.incidentFacets σ ↔ τ ∈ T.facets ∧ σ.IsSubfaceOf τ := by
  classical
  simp [SimplexTriangulation.incidentFacets]

theorem SimplexTriangulation.incidentFacets_nonempty_of_isFace {n : ℕ}
    {T : SimplexTriangulation n} {σ : SimplexFacet n} (hσ : T.IsFace σ) :
    (T.incidentFacets σ).Nonempty := by
  rcases hσ with ⟨τ, hτ, hστ⟩
  exact ⟨τ, mem_incidentFacets_iff.mpr ⟨hτ, hστ⟩⟩

theorem SimplexTriangulation.mem_facets_of_isFace_of_card {n : ℕ}
    {T : SimplexTriangulation n} {σ : SimplexFacet n} (hσ : T.IsFace σ)
    (hcard : σ.vertices.card = n) : σ ∈ T.facets := by
  rcases hσ with ⟨τ, hτ, hστ⟩
  have hEqVerts : σ.vertices = τ.vertices := by
    refine Finset.eq_of_subset_of_card_le hστ ?_
    simp [hcard, T.facet_card τ hτ]
  have hEq : σ = τ := by
    cases σ
    cases τ
    cases hEqVerts
    rfl
  exact hEq ▸ hτ

theorem SimplexTriangulation.adjacentFacets_mem_incidentFacets_commonFace_left {n : ℕ}
    {T : SimplexTriangulation n} {τ₁ τ₂ : SimplexFacet n} (h : T.AdjacentFacets τ₁ τ₂) :
    τ₁ ∈ T.incidentFacets (τ₁.commonFace τ₂) := by
  exact mem_incidentFacets_iff.mpr ⟨adjacentFacets_left_mem h, adjacentFacets_commonFace_left h⟩

theorem SimplexTriangulation.adjacentFacets_mem_incidentFacets_commonFace_right {n : ℕ}
    {T : SimplexTriangulation n} {τ₁ τ₂ : SimplexFacet n} (h : T.AdjacentFacets τ₁ τ₂) :
    τ₂ ∈ T.incidentFacets (τ₁.commonFace τ₂) := by
  exact mem_incidentFacets_iff.mpr ⟨adjacentFacets_right_mem h, adjacentFacets_commonFace_right h⟩

theorem SimplexTriangulation.two_le_card_incidentFacets_commonFace {n : ℕ}
    {T : SimplexTriangulation n} {τ₁ τ₂ : SimplexFacet n} (h : T.AdjacentFacets τ₁ τ₂) :
    2 ≤ (T.incidentFacets (τ₁.commonFace τ₂)).card := by
  classical
  have hsubset :
      ({τ₁, τ₂} : Finset (SimplexFacet n)) ⊆ T.incidentFacets (τ₁.commonFace τ₂) := by
    intro τ hτ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
    rcases hτ with rfl | rfl
    · exact adjacentFacets_mem_incidentFacets_commonFace_left h
    · exact adjacentFacets_mem_incidentFacets_commonFace_right h
  calc
    2 = ({τ₁, τ₂} : Finset (SimplexFacet n)).card := by
          simp [adjacentFacets_ne h]
    _ ≤ (T.incidentFacets (τ₁.commonFace τ₂)).card := Finset.card_le_card hsubset

end Arxiv170207325
