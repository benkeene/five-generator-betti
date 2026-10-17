/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Interface

/-! Stream A (plan 2026-10-16 §1, §2 A1): toric evaluation, the coefficient-sum identity, and the
containment `toricKer ≤ J` from equal-weight binomial membership. -/

@[expose] public section

namespace FiveGenBetti

section Helpers

noncomputable def toricMap (K : Type*) [Field K] {e : ℕ}
    (n : Fin e → ℕ) :
    MvPolynomial (Fin e) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval
    (fun i => (Polynomial.X : Polynomial K) ^ n i)

variable {e : ℕ} {K : Type*} [Field K]

lemma mono_coe (s : Fin e →₀ ℕ) :
    mono K ⇑s = MvPolynomial.monomial s 1 := by
  simp [mono]

lemma toricMap_monomial
    (n : Fin e → ℕ) (s : Fin e →₀ ℕ) (c : K) :
    toricMap K n (MvPolynomial.monomial s c) =
      Polynomial.C c * Polynomial.X ^ weight n s := by
  sorry

lemma toricMap_mono (n z : Fin e → ℕ) :
    toricMap K n (mono K z) =
      Polynomial.X ^ weight n z := by
  sorry

lemma mem_toricKer (n : Fin e → ℕ)
    {f : MvPolynomial (Fin e) K} :
    f ∈ toricKer K n ↔ toricMap K n f = 0 :=
  RingHom.mem_ker

lemma mono_sub_mem_toricKer (n : Fin e → ℕ)
    {z z' : Fin e → ℕ}
    (h : weight n z = weight n z') :
    mono K z - mono K z' ∈ toricKer K n := by
  sorry

lemma coeff_sum_eq_zero (n : Fin e → ℕ)
    {f : MvPolynomial (Fin e) K}
    (hf : f ∈ toricKer K n) (d : ℕ) :
    ∑ s ∈ f.support.filter
      (fun s : Fin e →₀ ℕ => weight n s = d),
      f.coeff s = 0 := by
  sorry

end Helpers

theorem toricKer_le_ideal_of_mono_sub_mem
    {e : ℕ} {K : Type*} [Field K]
    (n : Fin e → ℕ)
    (J : Ideal (MvPolynomial (Fin e) K))
    (hJ : ∀ z z' : Fin e → ℕ,
      weight n z = weight n z' →
      mono K z - mono K z' ∈ J) :
    toricKer K n ≤ J := by
  sorry

end FiveGenBetti
