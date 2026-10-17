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
  classical
  induction g using MvPolynomial.induction_on' with
  | monomial s c =>
    have hmf : MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.monomial s c * f)
        (Finsupp.weight w s + d) :=
      (MvPolynomial.isWeightedHomogeneous_monomial w s c rfl).mul hf
    have hs := MvPolynomial.isWeightedHomogeneous_monomial w s c
      (rfl : Finsupp.weight w s = Finsupp.weight w s)
    by_cases h1 : Finsupp.weight w s + d = n
    · subst h1
      rw [hmf.weightedHomogeneousComponent_same]
      simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel,
        hs.weightedHomogeneousComponent_same]
    · rw [hmf.weightedHomogeneousComponent_ne _ (Ne.symm h1)]
      split_ifs with h2
      · rw [hs.weightedHomogeneousComponent_ne _ (by omega), zero_mul]
      · rfl
  | add p q hp hq =>
    rw [add_mul, map_add, hp, hq]
    split_ifs
    · rw [map_add, add_mul]
    · rw [add_zero]

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
  classical
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hmem
  refine ⟨fun i => if d i ≤ n then
      MvPolynomial.weightedHomogeneousComponent w (n - d i) (c i) else 0, ?_, ?_, ?_⟩
  · have := congrArg (MvPolynomial.weightedHomogeneousComponent w n) hc
    rw [hp.weightedHomogeneousComponent_same, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [homogeneousComponent_mul_right K w (c i) (f i) (d i) n (hf i)]
    by_cases h : d i ≤ n
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte, zero_mul]
  · intro i
    dsimp only
    split_ifs
    · exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _
    · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _
  · intro i hi
    simp only [Nat.not_le.2 hi, ↓reduceIte]

theorem weighted_component_eq_zero_of_small
    (K : Type*) [Field K] {e : ℕ}
    (w : Fin e → ℕ) (m : ℕ)
    (hm : 0 < m) (hw : ∀ i, m ≤ w i)
    (p : MvPolynomial (Fin e) K) (n : ℕ)
    (hn : 0 < n) (hnm : n < m) :
    MvPolynomial.weightedHomogeneousComponent w n p = 0 := by
  refine MvPolynomial.weightedHomogeneousComponent_eq_zero' n p fun s _ hs => ?_
  by_cases h0 : s = 0
  · subst h0
    simp at hs
    omega
  · obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h0
    have := Finsupp.le_weight_of_ne_zero' w (s := i) (f := s) hi
    have := hw i
    omega

end FiveGenBetti
