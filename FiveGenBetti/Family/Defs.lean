/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Interface

/-! The extremal family `⟨m, m+1, m+k, m+2k−1, m+2k⟩`, `m = 2kq + 1`, and its `4k + 2` relations
(`H`: `2k+2` ordinary-homogeneous binomials; `N`: `2k` binomials of semigroup degree `(q+2)m + r`).
Index `N` by `Fin k ⊕ Fin k` to avoid natural subtraction by `2k`; at `q = k − 1` the exponent
`q + 1 + r − k` is `r`, never `q − k + 1 + r` (off by one). -/

@[expose] public section

namespace FiveGenBetti.Family

/-- The generators, internal copy of `Challenge.familyGens`. -/
def gens (k q : ℕ) (i : Fin 5) : ℕ :=
  let m := 2 * k * q + 1
  match i.val with
  | 0 => m
  | 1 => m + 1
  | 2 => m + k
  | 3 => m + (2 * k - 1)
  | _ => m + 2 * k

@[simp] theorem gens_zero (k q : ℕ) : gens k q 0 = 2 * k * q + 1 := rfl
@[simp] theorem gens_one (k q : ℕ) : gens k q 1 = 2 * k * q + 1 + 1 := rfl
@[simp] theorem gens_two (k q : ℕ) : gens k q 2 = 2 * k * q + 1 + k := rfl
@[simp] theorem gens_three (k q : ℕ) : gens k q 3 = 2 * k * q + 1 + (2 * k - 1) := rfl
@[simp] theorem gens_four (k q : ℕ) : gens k q 4 = 2 * k * q + 1 + 2 * k := rfl

/-- Index type of the `H`-relations: the four initial ones and two families of `k − 1`. -/
abbrev HIndex (k : ℕ) := Fin 4 ⊕ (Fin (k - 1) ⊕ Fin (k - 1))

/-- Index type of the `N`-relations. -/
abbrev NIndex (k : ℕ) := Fin k ⊕ Fin k

theorem gens_pos (k q : ℕ) (i : Fin 5) :
    0 < gens k q i := by
  fin_cases i <;> simp [gens]

theorem gens_strictMono (k q : ℕ) (hk : 3 ≤ k) : StrictMono (gens k q) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> simp [gens] <;> omega

theorem gens_gcd (k q : ℕ) : Finset.univ.gcd (gens k q) = 1 := by
  have h0 : Finset.univ.gcd (gens k q) ∣ gens k q 0 := Finset.gcd_dvd (Finset.mem_univ _)
  have h1 : Finset.univ.gcd (gens k q) ∣ gens k q 1 := Finset.gcd_dvd (Finset.mem_univ _)
  have h := Nat.dvd_sub h1 h0
  simp only [gens_one, gens_zero, Nat.add_sub_cancel_left] at h
  exact Nat.dvd_one.mp h

end FiveGenBetti.Family
