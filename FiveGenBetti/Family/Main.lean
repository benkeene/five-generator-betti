/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Family.Defs

/-! Theorem F, assembled from (to be written, in this order): `Relations` (membership of `H`, `N` in
the toric ideal), `NormalForms` (the `2kq + 1` monomial normal forms and their offset bijection),
`Generation` (every monomial reduces to `a^ℓ · normal form`, hence `J = I`), `Apery`,
`Minimality` (nonredundancy of the displayed list; `N₀` is *not* indispensable), and the graded
lower bound `spanRank_eq_card_of_weightedHomogeneous_irredundant` (`GradedGenerators`). -/

@[expose] public section

namespace FiveGenBetti.Family

theorem spanRank_eq (K : Type*) [Field K] (k q : ℕ) (hk : 3 ≤ k) (hq : k - 1 ≤ q) :
    (toricKer K (gens k q)).spanRank = (4 * k + 2 : ℕ) := by
  sorry

end FiveGenBetti.Family
