/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Family.Generation
public import FiveGenBetti.Family.Minimality
public import FiveGenBetti.GradedGenerators

/-! Theorem F (plan 2026-10-16 §4): `J = I` (`Generation`), positivity, homogeneity and
nonredundancy of the `4k + 2` relations (`Relations`, `Minimality`), and the graded cardinality
theorem `spanRank_eq_card_of_weightedHomogeneous_irredundant` (`GradedGenerators`). -/

@[expose] public section

namespace FiveGenBetti.Family

theorem spanRank_eq
    (K : Type*) [Field K] (k q : ℕ)
    (hk : 3 ≤ k) (hq : k-1 ≤ q) :
    (toricKer K (gens k q)).spanRank = (4*k+2 : ℕ) := by
  have h :=
    spanRank_eq_card_of_weightedHomogeneous_irredundant
      K (gens k q) (gens_pos k q)
      (relation K k q) (relationDegree k q)
      (relationDegree_pos k q hk hq)
      (relation_weightedHomogeneous K k q hk hq)
      (relation_nonredundant K k q hk hq)
  change
    (familyIdeal K k q).spanRank =
      (Fintype.card (RelIndex k) : Cardinal) at h
  rw [familyIdeal_eq_toricKer K k q hk hq, relIndex_card k hk] at h
  exact h

end FiveGenBetti.Family
