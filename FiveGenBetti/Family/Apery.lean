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
  sorry

theorem apery_iff_normalWeight
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (d : ℕ) :
    IsApery k q d ↔
      ∃ u : NormalForm k q,
        weight (gens k q) (normalExp u) = d := by
  sorry

end FiveGenBetti.Family
