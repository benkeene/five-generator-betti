/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Defs

/-! Theorem W, the finite-width conjecture, stated with internal names and admitted. This module is
outside the import closure of `Solution.lean` and of the version-1 comparator configuration;
`comparator.all-targets.json` lists it and must fail until it is proved. -/

@[expose] public section

namespace FiveGenBetti.Targets

def MinimallyGenerates (n : Fin 5 → ℕ) : Prop :=
  ∀ i : Fin 5, n i ∉ AddSubmonoid.closure (n '' {j | j ≠ i})

theorem beta1_five_le_two_width_add_two (K : Type*) [Field K] (n : Fin 5 → ℕ)
    (hpos : 0 < n 0) (hmono : StrictMono n) (hgcd : Finset.univ.gcd n = 1)
    (hmin : MinimallyGenerates n) (hwlo : 4 ≤ n 4 - n 0) (hwhi : n 4 - n 0 ≤ 40) :
    (toricKer K n).spanRank ≤ (2 * (n 4 - n 0) + 2 : ℕ) := by
  sorry

end FiveGenBetti.Targets
