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
  rw [toricMap, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum, Polynomial.algebraMap_eq]
  congr 2
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma toricMap_mono (n z : Fin e → ℕ) :
    toricMap K n (mono K z) =
      Polynomial.X ^ weight n z := by
  rw [mono, toricMap_monomial]
  simp [weight]

lemma mem_toricKer (n : Fin e → ℕ)
    {f : MvPolynomial (Fin e) K} :
    f ∈ toricKer K n ↔ toricMap K n f = 0 :=
  RingHom.mem_ker

lemma mono_sub_mem_toricKer (n : Fin e → ℕ)
    {z z' : Fin e → ℕ}
    (h : weight n z = weight n z') :
    mono K z - mono K z' ∈ toricKer K n := by
  rw [mem_toricKer, map_sub, toricMap_mono, toricMap_mono, h, sub_self]

lemma coeff_sum_eq_zero (n : Fin e → ℕ)
    {f : MvPolynomial (Fin e) K}
    (hf : f ∈ toricKer K n) (d : ℕ) :
    ∑ s ∈ f.support.filter
      (fun s : Fin e →₀ ℕ => weight n s = d),
      f.coeff s = 0 := by
  have hφ := (mem_toricKer n).1 hf
  rw [f.as_sum, map_sum] at hφ
  have := congrArg (fun p : Polynomial K => p.coeff d) hφ
  simp only [toricMap_monomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at this
  rw [Finset.sum_filter]
  simpa [eq_comm] using this

open Classical in
/-- A chosen exponent vector of weight `d` (junk `0` when none exists). -/
private noncomputable def degreeRoot
    (n : Fin e → ℕ) (d : ℕ) : Fin e → ℕ :=
  if h : ∃ z, weight n z = d then h.choose else 0

private lemma weight_degreeRoot (n z : Fin e → ℕ) :
    weight n (degreeRoot n (weight n z)) = weight n z := by
  have h : ∃ y, weight n y = weight n z := ⟨z, rfl⟩
  rw [degreeRoot]
  simp only [h, ↓reduceDIte]
  exact h.choose_spec

private lemma toricKer_le_ideal_aux (n : Fin e → ℕ)
    (J : Ideal (MvPolynomial (Fin e) K))
    (hJ : ∀ z z' : Fin e → ℕ,
      weight n z = weight n z' →
      mono K z - mono K z' ∈ J) :
    toricKer K n ≤ J := by
  intro f hf
  have hsplit : f = ∑ s ∈ f.support, MvPolynomial.C (f.coeff s) *
        (mono K s - mono K (degreeRoot n (weight n s))) +
      ∑ s ∈ f.support, MvPolynomial.C (f.coeff s) * mono K (degreeRoot n (weight n s)) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← mul_add, sub_add_cancel, mono_coe, MvPolynomial.C_mul_monomial, mul_one]
    exact f.as_sum
  have hzero : ∑ s ∈ f.support,
      MvPolynomial.C (f.coeff s) * mono K (degreeRoot n (weight n s)) = 0 := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun s : Fin e →₀ ℕ => weight n s)
      (t := f.support.image (fun s : Fin e →₀ ℕ => weight n s))
      (fun s hs => Finset.mem_image_of_mem _ hs)]
    refine Finset.sum_eq_zero fun d _ => ?_
    have : ∀ s ∈ f.support.filter (fun s : Fin e →₀ ℕ => weight n s = d),
        MvPolynomial.C (f.coeff s) * mono K (degreeRoot n (weight n s)) =
          MvPolynomial.C (f.coeff s) * mono K (degreeRoot n d) := by
      intro s hs; rw [(Finset.mem_filter.1 hs).2]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← map_sum, coeff_sum_eq_zero n hf d,
      map_zero, zero_mul]
  rw [hsplit, hzero, add_zero]
  exact J.sum_mem fun s _ => J.mul_mem_left _ (hJ _ _ (weight_degreeRoot n s).symm)

end Helpers

theorem toricKer_le_ideal_of_mono_sub_mem
    {e : ℕ} {K : Type*} [Field K]
    (n : Fin e → ℕ)
    (J : Ideal (MvPolynomial (Fin e) K))
    (hJ : ∀ z z' : Fin e → ℕ,
      weight n z = weight n z' →
      mono K z - mono K z' ∈ J) :
    toricKer K n ≤ J :=
  toricKer_le_ideal_aux n J hJ

end FiveGenBetti
