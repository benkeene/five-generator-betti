/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Interface

/-! Stream A (plan 2026-10-16 §1, §2 A2): weighted homogeneous coefficient selection. -/

@[expose] public section

namespace FiveGenBetti

theorem homogeneousComponent_mul_right
    (K : Type*) [Field K] {e : ℕ}
    (w : Fin e → ℕ) (g f : MvPolynomial (Fin e) K) (d n : ℕ)
    (hf : MvPolynomial.IsWeightedHomogeneous w f d) :
    MvPolynomial.weightedHomogeneousComponent w n (g * f) =
      if d ≤ n then
        MvPolynomial.weightedHomogeneousComponent w (n - d) g * f
      else 0 := by
  sorry

theorem homogeneous_mem_span_range
    (K : Type*) [Field K] {e : ℕ}
    {ι : Type} [Fintype ι]
    (w : Fin e → ℕ)
    (f : ι → MvPolynomial (Fin e) K) (d : ι → ℕ)
    (hf : ∀ i, MvPolynomial.IsWeightedHomogeneous w (f i) (d i))
    (p : MvPolynomial (Fin e) K) (n : ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous w p n)
    (hmem : p ∈ Ideal.span (Set.range f)) :
    ∃ a : ι → MvPolynomial (Fin e) K,
      (∑ i, a i * f i = p) ∧
      (∀ i, MvPolynomial.IsWeightedHomogeneous w (a i) (n - d i)) ∧
      (∀ i, n < d i → a i = 0) := by
  sorry

theorem weighted_component_eq_zero_of_small
    (K : Type*) [Field K] {e : ℕ}
    (w : Fin e → ℕ) (m : ℕ)
    (hm : 0 < m) (hw : ∀ i, m ≤ w i)
    (p : MvPolynomial (Fin e) K) (n : ℕ)
    (hn : 0 < n) (hnm : n < m) :
    MvPolynomial.weightedHomogeneousComponent w n p = 0 := by
  sorry

end FiveGenBetti
