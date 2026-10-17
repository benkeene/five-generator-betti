/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Family.Relations
public import FiveGenBetti.Graded.Projection

/-! Stream B (plan 2026-10-16 §3 B5): nonredundancy of the displayed `4k + 2` relations, including
the boundary `q = k - 1`. Not indispensability (false for this family). -/

@[expose] public section

namespace FiveGenBetti.Family

variable (K : Type*) [Field K] (k q : ℕ)

theorem psi_H (hk : 3 ≤ k) (i : HIndex k) :
    psi K k (relation K k q (.inl i)) = 0 := by
  sorry

theorem psi_N
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (i : NIndex k) :
    psi K k (relation K k q (.inr i)) =
      MvPolynomial.X 0 ^ (q+1) *
        MvPolynomial.X 1 ^ nOffset k i *
        (MvPolynomial.X 1 ^ (2*k*q+1) - MvPolynomial.X 0) := by
  sorry

theorem psi_N_ne_zero
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (i : NIndex k) :
    psi K k (relation K k q (.inr i)) ≠ 0 := by
  sorry

theorem H_nonredundant (hk : 3 ≤ k) (i : HIndex k) :
    relation K k q (.inl i) ∉
      Ideal.span
        ((fun j : HIndex k => relation K k q (.inl j)) ''
          {j | j ≠ i}) := by
  sorry

theorem N_nonredundant
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (i : NIndex k) :
    relation K k q (.inr i) ∉
      Ideal.span (relation K k q '' {j | j ≠ .inr i}) := by
  sorry

theorem H_degree_lt_D
    (hk : 3 ≤ k) (hq : k ≤ q) (i : HIndex k) :
    relationDegree k q (.inl i) <
      (q+2)*(2*k*q+1) := by
  sorry

theorem H_boundary_collisions
    (hk : 3 ≤ k) (i : HIndex k)
    (hd :
      (k+1)*(2*k*(k-1)+1) ≤
        relationDegree k (k-1) (.inl i)) :
    relationDegree k (k-1) (.inl i) =
        (k+1)*(2*k*(k-1)+1) ∨
    relationDegree k (k-1) (.inl i) =
        (k+1)*(2*k*(k-1)+1) + (k-1) := by
  sorry

theorem H_degree_lt_D_add_m
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (i : HIndex k) :
    relationDegree k q (.inl i) <
      (q+3)*(2*k*q+1) := by
  sorry

theorem relation_nonredundant
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (i : RelIndex k) :
    relation K k q i ∉
      Ideal.span (relation K k q '' {j | j ≠ i}) := by
  sorry

end FiveGenBetti.Family
