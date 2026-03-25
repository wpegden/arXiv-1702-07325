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

@[simp]
theorem cyclicSucc_val {n : ℕ} [NeZero n] (i : RoomIndex n) :
    (cyclicSucc n i).1 = (i.1 + 1) % n :=
  rfl

@[simp]
theorem cyclicPred_val {n : ℕ} [NeZero n] (i : RoomIndex n) :
    (cyclicPred n i).1 = (i.1 + (n - 1)) % n :=
  rfl

end Arxiv170207325
