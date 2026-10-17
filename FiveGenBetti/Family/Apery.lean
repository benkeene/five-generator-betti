/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Family.Generation

/-! Stream B (plan 2026-10-16 §3 B4): the Apéry set is exactly the set of normal-form weights. -/

@[expose] public section

namespace FiveGenBetti.Family

variable (K : Type*) [Field K] (k q : ℕ)

theorem normalWeight_isApery
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (u : NormalForm k q) :
    IsApery k q (weight (gens k q) (normalExp u)) := by
  refine ⟨⟨normalExp u, rfl⟩, ?_⟩
  rintro ⟨t, ⟨z, rfl⟩, ht⟩
  obtain ⟨ell, v, -, hv⟩ := monomial_normal_form ℚ k q hk hq z
  have h : 0 * (2*k*q+1) + weight (gens k q) (normalExp u) =
      (ell + 1) * (2*k*q+1) + weight (gens k q) (normalExp v) := by
    rw [ht, hv]; ring
  have := (normal_repr_injective k q hk hq h).1
  omega

theorem apery_iff_normalWeight
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (d : ℕ) :
    IsApery k q d ↔
      ∃ u : NormalForm k q,
        weight (gens k q) (normalExp u) = d := by
  constructor
  · rintro ⟨⟨z, rfl⟩, hnot⟩
    obtain ⟨ell, u, -, hu⟩ := monomial_normal_form ℚ k q hk hq z
    refine ⟨u, ?_⟩
    rcases Nat.eq_zero_or_pos ell with rfl | hell
    · simpa using hu.symm
    · exfalso
      apply hnot
      refine ⟨(ell - 1) * (2*k*q+1) + weight (gens k q) (normalExp u),
        ⟨exp5 (ell - 1) 0 0 0 0 + normalExp u, ?_⟩, ?_⟩
      · rw [weight_add, weight_gens_exp5]; ring
      · rw [hu]
        obtain ⟨l, rfl⟩ : ∃ l, ell = l + 1 := ⟨ell - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
  · rintro ⟨u, rfl⟩
    exact normalWeight_isApery k q hk hq u

end FiveGenBetti.Family
