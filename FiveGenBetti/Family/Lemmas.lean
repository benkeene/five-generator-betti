/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Family.Data

/-! Stream B helper lemmas: weights of `exp5` vectors, monomials of exponent vectors, their
weighted homogeneity and toric evaluation. -/

@[expose] public section

namespace FiveGenBetti.Family

theorem exp5_apply_zero (a b c d e : ℕ) : exp5 a b c d e 0 = a := rfl
theorem exp5_apply_one (a b c d e : ℕ) : exp5 a b c d e 1 = b := rfl
theorem exp5_apply_two (a b c d e : ℕ) : exp5 a b c d e 2 = c := rfl
theorem exp5_apply_three (a b c d e : ℕ) : exp5 a b c d e 3 = d := rfl
theorem exp5_apply_four (a b c d e : ℕ) : exp5 a b c d e 4 = e := rfl

theorem weight_eq_five (n z : Fin 5 → ℕ) :
    weight n z = z 0 * n 0 + z 1 * n 1 + z 2 * n 2 + z 3 * n 3 + z 4 * n 4 := by
  simp [weight, Fin.sum_univ_five]

theorem weight_exp5 (n : Fin 5 → ℕ) (a b c d e : ℕ) :
    weight n (exp5 a b c d e) = a * n 0 + b * n 1 + c * n 2 + d * n 3 + e * n 4 := by
  rw [weight_eq_five]; rfl

theorem weight_gens_exp5 (k q a b c d e : ℕ) :
    weight (gens k q) (exp5 a b c d e) =
      a * (2*k*q+1) + b * (2*k*q+1+1) + c * (2*k*q+1+k) + d * (2*k*q+1+(2*k-1)) +
        e * (2*k*q+1+2*k) := by
  rw [weight_exp5]; rfl

theorem sum_exp5 (a b c d e : ℕ) : ∑ i, exp5 a b c d e i = a + b + c + d + e := by
  simp [Fin.sum_univ_five]; rfl

theorem weight_add {e : ℕ} (n z z' : Fin e → ℕ) :
    weight n (z + z') = weight n z + weight n z' := by
  simp [weight, add_mul, Finset.sum_add_distrib]

theorem finsuppWeight_equivFunOnFinite {e : ℕ} (n z : Fin e → ℕ) :
    Finsupp.weight n (Finsupp.equivFunOnFinite.symm z) = weight n z := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [weight]

theorem isWeightedHomogeneous_mono (K : Type*) [Field K] {e : ℕ} (n z : Fin e → ℕ) :
    MvPolynomial.IsWeightedHomogeneous n (mono K z) (weight n z) :=
  MvPolynomial.isWeightedHomogeneous_monomial _ _ _ (finsuppWeight_equivFunOnFinite n z)

theorem mono_add (K : Type*) [Field K] {e : ℕ} (z z' : Fin e → ℕ) :
    mono K (z + z') = mono K z * mono K z' := by
  have h : Finsupp.equivFunOnFinite.symm (z + z') =
      Finsupp.equivFunOnFinite.symm z + Finsupp.equivFunOnFinite.symm z' := by
    ext i; simp
  simp only [mono, MvPolynomial.monomial_mul_monomial, mul_one, h]

theorem aeval_mono (K : Type*) [Field K] {e : ℕ} (n z : Fin e → ℕ) :
    MvPolynomial.aeval (fun i => (Polynomial.X : Polynomial K) ^ n i) (mono K z) =
      Polynomial.X ^ weight n z := by
  rw [mono, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp only [map_one, one_mul, Finsupp.coe_equivFunOnFinite_symm, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  simp [weight, mul_comm]

theorem mono_sub_mem_toricKer' (K : Type*) [Field K] {e : ℕ} (n : Fin e → ℕ)
    {z z' : Fin e → ℕ} (h : weight n z = weight n z') :
    mono K z - mono K z' ∈ toricKer K n := by
  change _ ∈ RingHom.ker _
  rw [RingHom.mem_ker]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub]
  rw [aeval_mono, aeval_mono, h, sub_self]

end FiveGenBetti.Family
