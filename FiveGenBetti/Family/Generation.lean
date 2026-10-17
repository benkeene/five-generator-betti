/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Family.Relations
public import FiveGenBetti.Family.NormalForms
public import FiveGenBetti.Algebra

/-! Stream B (plan 2026-10-16 §3 B3, B4): staged reduction of every monomial to `a^ℓ · (normal
form)` modulo `J`, and `J = I`. -/

@[expose] public section

namespace FiveGenBetti.Family

variable (K : Type*) [Field K] (k q : ℕ)

theorem residual_step
    (hk : 3 ≤ k) (hq : k-1 ≤ q)
    (z : Fin 5 → ℕ) (hz : z 0 = 0) :
    (∃ u : NormalForm k q,
      mono K z - normalMono K u ∈ familyIdeal K k q ∧
      weight (gens k q) z =
        weight (gens k q) (normalExp u)) ∨
    (∃ (ell : ℕ) (z' : Fin 5 → ℕ),
      0 < ell ∧
      mono K z - MvPolynomial.X 0 ^ ell * mono K z' ∈
        familyIdeal K k q ∧
      weight (gens k q) z =
        ell*(2*k*q+1) + weight (gens k q) z') := by
  sorry

theorem monomial_normal_form
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (z : Fin 5 → ℕ) :
    ∃ (ell : ℕ) (u : NormalForm k q),
      mono K z - MvPolynomial.X 0 ^ ell * normalMono K u ∈
        familyIdeal K k q ∧
      weight (gens k q) z =
        ell*(2*k*q+1) + weight (gens k q) (normalExp u) := by
  sorry

theorem familyIdeal_eq_toricKer
    (hk : 3 ≤ k) (hq : k-1 ≤ q) :
    familyIdeal K k q = toricKer K (gens k q) := by
  sorry

end FiveGenBetti.Family
