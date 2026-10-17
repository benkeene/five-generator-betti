/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Family.Lemmas
public import FiveGenBetti.Algebra

/-! Stream B (plan 2026-10-16 §3 B1): relation count, weight arithmetic, weighted homogeneity,
positivity of degrees, and membership in the toric ideal. -/

@[expose] public section

namespace FiveGenBetti.Family

variable (K : Type*) [Field K] (k q : ℕ)

theorem relIndex_card (hk : 3 ≤ k) :
    Fintype.card (RelIndex k) = 4*k+2 := by
  simp only [RelIndex, HIndex, NIndex, Fintype.card_sum, Fintype.card_fin]
  omega

theorem h_weight (hk : 3 ≤ k) (i : HIndex k) :
    weight (gens k q) (hExp k i).1 =
      weight (gens k q) (hExp k i).2 := by
  rcases i with i | i | i
  · fin_cases i <;> simp only [hExp, weight_gens_exp5] <;> zify [show 1 ≤ 2 * k by omega, show 1 ≤ k by omega] <;> ring
  · obtain ⟨v, hv⟩ := i
    simp only [hExp, weight_gens_exp5]
    zify [show 1 ≤ 2 * k by omega, show 1 ≤ k by omega, show v ≤ k - 1 by omega]
    ring
  · obtain ⟨v, hv⟩ := i
    simp only [hExp, weight_gens_exp5]
    zify [show 1 ≤ 2 * k by omega, show 1 ≤ k by omega, show 2 ≤ k by omega, show v ≤ k - 1 by omega,
      show v ≤ k - 2 by omega]
    ring

theorem n_weight
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (i : NIndex k) :
    weight (gens k q) (nExp k q i).1 =
        (q+2)*(2*k*q+1) + nOffset k i ∧
    weight (gens k q) (nExp k q i).2 =
        (q+2)*(2*k*q+1) + nOffset k i := by
  rcases i with ⟨r, hr⟩ | ⟨r, hr⟩
  · simp only [nExp, nOffset, weight_gens_exp5]
    zify [show 1 ≤ 2 * k by omega, show 1 ≤ k by omega, show r ≤ k - 1 by omega, show k ≤ q + 1 + r by omega,
      show r ≤ q + 2 by omega]
    constructor <;> ring
  · simp only [nExp, nOffset, weight_gens_exp5]
    zify [show 1 ≤ 2 * k by omega, show 1 ≤ k by omega, show r ≤ k - 1 by omega, show k ≤ q + 2 + r by omega,
      show r ≤ q + 1 by omega]
    constructor <;> ring

theorem relExp_weight
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (i : RelIndex k) :
    weight (gens k q) (relExp k q i).1 = weight (gens k q) (relExp k q i).2 := by
  rcases i with i | i
  · exact h_weight k q hk i
  · obtain ⟨h1, h2⟩ := n_weight k q hk hq i
    exact h1.trans h2.symm

theorem relation_weightedHomogeneous
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (i : RelIndex k) :
    MvPolynomial.IsWeightedHomogeneous
      (gens k q) (relation K k q i) (relationDegree k q i) := by
  unfold relation relationDegree
  refine (isWeightedHomogeneous_mono K _ _).sub ?_
  rw [relExp_weight k q hk hq i]
  exact isWeightedHomogeneous_mono K _ _

theorem relationDegree_pos
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (i : RelIndex k) :
    0 < relationDegree k q i := by
  have hk0 : 0 < k := by omega
  rcases i with i | i
  · rcases i with i | i | i
    · fin_cases i <;> simp only [relationDegree, relExp, hExp, weight_gens_exp5] <;> positivity
    · simp only [relationDegree, relExp, hExp, weight_gens_exp5]; positivity
    · simp only [relationDegree, relExp, hExp, weight_gens_exp5]; positivity
  · simp only [relationDegree, relExp, (n_weight k q hk hq i).1]
    positivity

theorem relation_mem_toricKer
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (i : RelIndex k) :
    relation K k q i ∈ toricKer K (gens k q) :=
  mono_sub_mem_toricKer' K _ (relExp_weight k q hk hq i)

end FiveGenBetti.Family
