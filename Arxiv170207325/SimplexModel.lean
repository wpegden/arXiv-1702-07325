import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic

open scoped BigOperators

noncomputable section

namespace Arxiv170207325

abbrev RoomIndex (n : ℕ) := Fin n

abbrev RentCoordinates (n : ℕ) := RoomIndex n → ℝ

abbrev RentSimplex (n : ℕ) := stdSimplex ℝ (RoomIndex n)

def coordSupport {n : ℕ} (x : RentCoordinates n) : Finset (RoomIndex n) :=
  Finset.univ.filter fun i => x i ≠ 0

def simplexSupport {n : ℕ} (x : RentSimplex n) : Finset (RoomIndex n) :=
  coordSupport x.1

def coordinateFace {n : ℕ} (I : Finset (RoomIndex n)) : Set (RentSimplex n) :=
  {x | simplexSupport x ⊆ I}

def freeCoordinates {n : ℕ} (x : RentSimplex n) : Finset (RoomIndex n) :=
  Finset.univ.filter fun i => x.1 i = 0

abbrev rentBarycenter (n : ℕ) [NeZero n] : RentSimplex n :=
  stdSimplex.barycenter

def cyclicSucc (n : ℕ) [NeZero n] (i : RoomIndex n) : RoomIndex n :=
  ⟨(i.1 + 1) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero <| NeZero.ne n)⟩

def cyclicPred (n : ℕ) [NeZero n] (i : RoomIndex n) : RoomIndex n :=
  ⟨(i.1 + (n - 1)) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero <| NeZero.ne n)⟩

@[simp]
theorem mem_coordSupport {n : ℕ} {x : RentCoordinates n} {i : RoomIndex n} :
    i ∈ coordSupport x ↔ x i ≠ 0 := by
  simp [coordSupport]

@[simp]
theorem mem_simplexSupport {n : ℕ} {x : RentSimplex n} {i : RoomIndex n} :
    i ∈ simplexSupport x ↔ x.1 i ≠ 0 := by
  simp [simplexSupport, coordSupport]

@[simp]
theorem mem_freeCoordinates {n : ℕ} {x : RentSimplex n} {i : RoomIndex n} :
    i ∈ freeCoordinates x ↔ x.1 i = 0 := by
  simp [freeCoordinates]

theorem coordSupport_subset_iff {n : ℕ} {x : RentCoordinates n} {I : Finset (RoomIndex n)} :
    coordSupport x ⊆ I ↔ ∀ i, i ∉ I → x i = 0 := by
  constructor
  · intro hx i hi
    by_contra hxi
    exact hi (hx (by simpa using hxi))
  · intro hx i hi
    by_contra hnot
    exact (show x i ≠ 0 by simpa using hi) (hx i hnot)

theorem simplexSupport_subset_iff {n : ℕ} {x : RentSimplex n} {I : Finset (RoomIndex n)} :
    simplexSupport x ⊆ I ↔ ∀ i, i ∉ I → x.1 i = 0 := by
  simpa [simplexSupport] using (coordSupport_subset_iff (x := x.1) (I := I))

@[simp]
theorem mem_coordinateFace_iff {n : ℕ} {x : RentSimplex n} {I : Finset (RoomIndex n)} :
    x ∈ coordinateFace I ↔ ∀ i, i ∉ I → x.1 i = 0 := by
  simpa [coordinateFace] using (simplexSupport_subset_iff (x := x) (I := I))

theorem coordinateFace_mono {n : ℕ} {I J : Finset (RoomIndex n)} (hIJ : I ⊆ J) :
    coordinateFace I ⊆ coordinateFace J := by
  intro x hx
  exact hx.trans hIJ

@[simp]
theorem coordinateFace_univ (n : ℕ) :
    coordinateFace (Finset.univ : Finset (RoomIndex n)) = Set.univ := by
  ext x
  simp [coordinateFace]

theorem freeCoordinates_eq_compl_simplexSupport {n : ℕ} (x : RentSimplex n) :
    freeCoordinates x = Finset.univ \ simplexSupport x := by
  ext i
  simp [freeCoordinates, simplexSupport, coordSupport]

@[simp]
theorem rentBarycenter_apply {n : ℕ} [NeZero n] (i : RoomIndex n) :
    (rentBarycenter n).1 i = (n : ℝ)⁻¹ := by
  convert (stdSimplex.barycenter_apply (𝕜 := ℝ) (X := RoomIndex n) i) using 1
  simp [RoomIndex]

theorem rentBarycenter_apply_pos {n : ℕ} [NeZero n] (i : RoomIndex n) :
    0 < (rentBarycenter n).1 i := by
  rw [rentBarycenter_apply]
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  exact inv_pos.mpr hn

theorem rentBarycenter_apply_ne_zero {n : ℕ} [NeZero n] (i : RoomIndex n) :
    (rentBarycenter n).1 i ≠ 0 := by
  exact (rentBarycenter_apply_pos i).ne'

theorem simplexSupport_rentBarycenter {n : ℕ} [NeZero n] :
    simplexSupport (rentBarycenter n) = Finset.univ := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne n)
  ext i
  simp [simplexSupport, coordSupport, hn0]

theorem eq_vertex_of_apply_eq_one {n : ℕ} {x : RentSimplex n} {i : RoomIndex n}
    (hi : x.1 i = 1) : x = stdSimplex.vertex (S := ℝ) i := by
  apply Subtype.ext
  funext j
  by_cases hij : j = i
  · subst hij
    simpa using hi
  · have hsum :
        Finset.sum (Finset.univ \ {i}) (fun k : RoomIndex n => x.1 k) = 0 := by
      have hxsum : Finset.sum Finset.univ (fun k : RoomIndex n => x.1 k) = 1 := x.2.2
      rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) (i := i)
        (f := fun k : RoomIndex n => x.1 k) (by simp)] at hxsum
      have hcancel :
          x.1 i + Finset.sum (Finset.univ \ {i}) (fun k : RoomIndex n => x.1 k) =
            x.1 i + 0 := by
        calc
          x.1 i + Finset.sum (Finset.univ \ {i}) (fun k : RoomIndex n => x.1 k) = 1 := hxsum
          _ = x.1 i := hi.symm
          _ = x.1 i + 0 := by simp
      exact add_left_cancel hcancel
    have hj_le :
        x.1 j ≤ Finset.sum (Finset.univ \ {i}) (fun k : RoomIndex n => x.1 k) := by
      refine Finset.single_le_sum ?_ ?_
      · intro k hk
        exact x.2.1 k
      · simp [hij]
    have hj_eq : x.1 j = 0 := by
      exact le_antisymm (by simpa [hsum] using hj_le) (x.2.1 j)
    simp [hij, hj_eq]

@[simp]
theorem rentBarycenter_mem_coordinateFace_iff {n : ℕ} [NeZero n] {I : Finset (RoomIndex n)} :
    rentBarycenter n ∈ coordinateFace I ↔ I = Finset.univ := by
  simp [coordinateFace, simplexSupport_rentBarycenter]

@[simp]
theorem cyclicSucc_val {n : ℕ} [NeZero n] (i : RoomIndex n) :
    (cyclicSucc n i).1 = (i.1 + 1) % n :=
  rfl

@[simp]
theorem cyclicPred_val {n : ℕ} [NeZero n] (i : RoomIndex n) :
    (cyclicPred n i).1 = (i.1 + (n - 1)) % n :=
  rfl

@[simp]
theorem cyclicPred_cyclicSucc {n : ℕ} [NeZero n] (i : RoomIndex n) :
    cyclicPred n (cyclicSucc n i) = i := by
  apply Fin.ext
  rw [cyclicPred_val, cyclicSucc_val]
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnm1 : n - 1 < n := Nat.sub_lt hn zero_lt_one
  by_cases hlast : i.1 + 1 = n
  · have hval : i.1 = n - 1 := by
      omega
    have hs : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
    rw [hval, hs]
    rw [Nat.add_mod]
    simp [Nat.mod_eq_of_lt hnm1]
  · have hlt : i.1 + 1 < n := lt_of_le_of_ne (Nat.succ_le_of_lt i.2) hlast
    have hsum : i.1 + 1 + (n - 1) = i.1 + n := by
      omega
    have hinner : (i.1 + n) % n = i.1 := by
      rw [Nat.add_mod]
      simp [Nat.mod_eq_of_lt i.2]
    rw [Nat.mod_eq_of_lt hlt, hsum, hinner]

@[simp]
theorem cyclicSucc_cyclicPred {n : ℕ} [NeZero n] (i : RoomIndex n) :
    cyclicSucc n (cyclicPred n i) = i := by
  apply Fin.ext
  rw [cyclicSucc_val, cyclicPred_val]
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnm1 : n - 1 < n := Nat.sub_lt hn zero_lt_one
  by_cases hzero : i.1 = 0
  · have hinner : (0 + (n - 1)) % n = n - 1 := by
      rw [Nat.zero_add]
      exact Nat.mod_eq_of_lt hnm1
    rw [hzero, hinner, Nat.sub_add_cancel (Nat.succ_le_of_lt hn)]
    simp
  · have hpos : 0 < i.1 := Nat.pos_of_ne_zero hzero
    have hrepr : i.1 + (n - 1) = (i.1 - 1) + n := by
      omega
    have hpredlt : i.1 - 1 < n := by
      omega
    have hinner : ((i.1 - 1) + n) % n = i.1 - 1 := by
      rw [Nat.add_mod]
      simp [Nat.mod_eq_of_lt hpredlt]
    rw [hrepr, hinner, Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)]
    exact Nat.mod_eq_of_lt i.2

theorem cyclicSucc_injective (n : ℕ) [NeZero n] : Function.Injective (cyclicSucc n) := by
  intro i j hij
  simpa [cyclicPred_cyclicSucc] using congrArg (cyclicPred n) hij

theorem cyclicPred_injective (n : ℕ) [NeZero n] : Function.Injective (cyclicPred n) := by
  intro i j hij
  simpa [cyclicSucc_cyclicPred] using congrArg (cyclicSucc n) hij

theorem cyclicSucc_bijective (n : ℕ) [NeZero n] : Function.Bijective (cyclicSucc n) := by
  refine ⟨cyclicSucc_injective n, ?_⟩
  intro i
  exact ⟨cyclicPred n i, cyclicSucc_cyclicPred i⟩

theorem cyclicPred_bijective (n : ℕ) [NeZero n] : Function.Bijective (cyclicPred n) := by
  refine ⟨cyclicPred_injective n, ?_⟩
  intro i
  exact ⟨cyclicSucc n i, cyclicPred_cyclicSucc i⟩

end Arxiv170207325
