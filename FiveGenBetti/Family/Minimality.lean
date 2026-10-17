/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Family.Relations
public import FiveGenBetti.Graded.Projection

/-! Stream B (plan 2026-10-16 §3 B5): nonredundancy of the displayed `4k + 2` relations, including
the boundary `q = k - 1`. Not indispensability (false for this family). -/

@[expose] public section

namespace FiveGenBetti.Family

variable (K : Type*) [Field K] (k q : ℕ)

private theorem psi_mono_b5 (z : Fin 5 → ℕ) :
    psi K k (mono K z) =
      MvPolynomial.X 0 ^ (∑ i, z i) *
        MvPolynomial.X 1 ^ weight (offset k) z := by
  rw [psi, mono, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [map_one, one_mul, Finsupp.coe_equivFunOnFinite_symm,
    mul_pow, ← pow_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.prod_pow_eq_pow_sum]
  simp [weight, mul_comm]

theorem psi_H (hk : 3 ≤ k) (i : HIndex k) :
    psi K k (relation K k q (.inl i)) = 0 := by
  have hs : (∑ j, (hExp k i).1 j) = ∑ j, (hExp k i).2 j := by
    rcases i with i | i | i
    · fin_cases i <;> simp only [hExp, sum_exp5] <;> omega
    · simp only [hExp, sum_exp5]; have := i.isLt; omega
    · simp only [hExp, sum_exp5]; have := i.isLt; omega
  have hw : weight (offset k) (hExp k i).1 = weight (offset k) (hExp k i).2 := by
    rcases i with i | i | i
    · fin_cases i <;>
        simp only [hExp, weight_exp5, offset, exp5_apply_zero, exp5_apply_one,
          exp5_apply_two, exp5_apply_three, exp5_apply_four] <;>
        zify [show 1 ≤ 2 * k by omega, show 1 ≤ k by omega] <;> ring
    · obtain ⟨v, hv⟩ := i
      simp only [hExp, weight_exp5, offset, exp5_apply_zero, exp5_apply_one,
        exp5_apply_two, exp5_apply_three, exp5_apply_four]
      zify [show 1 ≤ 2 * k by omega, show 1 ≤ k by omega,
        show v ≤ k - 1 by omega]
      ring
    · obtain ⟨v, hv⟩ := i
      simp only [hExp, weight_exp5, offset, exp5_apply_zero, exp5_apply_one,
        exp5_apply_two, exp5_apply_three, exp5_apply_four]
      zify [show 1 ≤ 2 * k by omega, show 1 ≤ k by omega, show 2 ≤ k by omega,
        show v ≤ k - 1 by omega, show v ≤ k - 2 by omega]
      ring
  simp only [relation, map_sub, psi_mono_b5, relExp, hs, hw, sub_self]

theorem psi_N
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (i : NIndex k) :
    psi K k (relation K k q (.inr i)) =
      MvPolynomial.X 0 ^ (q+1) *
        MvPolynomial.X 1 ^ nOffset k i *
        (MvPolynomial.X 1 ^ (2*k*q+1) - MvPolynomial.X 0) := by
  have hs : (∑ j, (nExp k q i).1 j) = q + 1 ∧
      (∑ j, (nExp k q i).2 j) = q + 2 := by
    rcases i with ⟨r, hr⟩ | ⟨r, hr⟩ <;>
      simp only [nExp, sum_exp5] <;> constructor <;> omega
  have hw : weight (offset k) (nExp k q i).1 = (2 * k * q + 1) + nOffset k i ∧
      weight (offset k) (nExp k q i).2 = nOffset k i := by
    rcases i with ⟨r, hr⟩ | ⟨r, hr⟩
    · simp only [nExp, nOffset, weight_exp5, offset, exp5_apply_zero, exp5_apply_one,
        exp5_apply_two, exp5_apply_three, exp5_apply_four]
      zify [show 1 ≤ 2 * k by omega, show 1 ≤ k by omega,
        show r ≤ k - 1 by omega, show k ≤ q + 1 + r by omega,
        show r ≤ q + 2 by omega]
      constructor <;> ring
    · simp only [nExp, nOffset, weight_exp5, offset, exp5_apply_zero, exp5_apply_one,
        exp5_apply_two, exp5_apply_three, exp5_apply_four]
      zify [show 1 ≤ 2 * k by omega, show 1 ≤ k by omega,
        show r ≤ k - 1 by omega, show k ≤ q + 2 + r by omega,
        show r ≤ q + 1 by omega]
      constructor <;> ring
  simp only [relation, map_sub, psi_mono_b5, relExp, hs.1, hs.2, hw.1, hw.2]
  simp only [pow_add, pow_one]
  ring

theorem psi_N_ne_zero
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (i : NIndex k) :
    psi K k (relation K k q (.inr i)) ≠ 0 := by
  rw [psi_N K k q hk hq i]
  refine mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ (MvPolynomial.X_ne_zero 0))
      (pow_ne_zero _ (MvPolynomial.X_ne_zero 1))) ?_
  intro h
  have he := congrArg
    (MvPolynomial.aeval (fun j : Fin 2 => if j = 0 then (1 : K) else 0)) h
  simp at he

private theorem b5h_first_antichain (hk : 3 ≤ k) (i j : HIndex k)
    (hi : i ≠ .inl 1) (h : (hExp k j).1 ≤ (hExp k i).1) : j = i := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp only [hExp, exp5, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h0 h1 h2 h3 h4
  all_goals simp_all [Fin.ext_iff]
  all_goals omega

private theorem b5h_second_not_le_first (hk : 3 ≤ k) (i j : HIndex k)
    (hi : i ≠ .inl 1) : ¬ (hExp k j).2 ≤ (hExp k i).1 := by
  intro h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp only [hExp, exp5, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h0 h1 h2 h3 h4
  all_goals simp_all [Fin.ext_iff]
  all_goals omega

private theorem b5h_first_not_le_ae (hk : 3 ≤ k) (j : HIndex k) :
    ¬ (hExp k j).1 ≤ exp5 1 0 0 0 1 := by
  intro h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  rcases j with j | (j | j)
  all_goals try fin_cases j
  all_goals simp only [hExp, exp5, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h0 h1 h2 h3 h4
  all_goals omega

private theorem b5h_second_le_ae (_hk : 3 ≤ k) (j : HIndex k)
    (h : (hExp k j).2 ≤ exp5 1 0 0 0 1) : j = .inl 1 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  rcases j with j | (j | j)
  all_goals try fin_cases j
  all_goals simp only [hExp, exp5, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h0 h1 h2 h3 h4
  all_goals simp_all

private theorem b5h_coeff_mul_mono_zero
    (p : MvPolynomial (Fin 5) K) (u z : Fin 5 → ℕ) (h : ¬ u ≤ z) :
    (p * mono K u).coeff (Finsupp.equivFunOnFinite.symm z) = 0 := by
  classical
  rw [mono, MvPolynomial.coeff_mul_monomial']
  have hn : ¬ Finsupp.equivFunOnFinite.symm u ≤ Finsupp.equivFunOnFinite.symm z := by
    intro hh
    apply h
    intro l
    simpa using hh l
  simp [hn]

private theorem b5h_coeff_mono_eq
    (u z : Fin 5 → ℕ) :
    (mono K u).coeff (Finsupp.equivFunOnFinite.symm z) =
      if u = z then 1 else 0 := by
  classical
  simp [mono, MvPolynomial.coeff_monomial]

private theorem b5h_ordinary_homogeneous (hk : 3 ≤ k) (i : HIndex k) :
    MvPolynomial.IsWeightedHomogeneous (fun _ : Fin 5 => 1)
      (relation K k q (.inl i)) (weight (fun _ : Fin 5 => 1) (hExp k i).1) := by
  have hw : weight (fun _ : Fin 5 => 1) (hExp k i).2 =
      weight (fun _ : Fin 5 => 1) (hExp k i).1 := by
    rcases i with i | (i | i)
    · fin_cases i <;> simp [hExp, weight_exp5] <;> omega
    · simp only [hExp, weight_exp5, mul_one]
      omega
    · simp only [hExp, weight_exp5, mul_one]
      omega
  change MvPolynomial.IsWeightedHomogeneous _
    (mono K (hExp k i).1 - mono K (hExp k i).2) _
  apply (isWeightedHomogeneous_mono K _ _).sub
  simpa only [hw] using
    (isWeightedHomogeneous_mono K (fun _ : Fin 5 => 1) (hExp k i).2)

private theorem b5h_exclusion
    (hk : 3 ≤ k) (i : HIndex k) (z : Fin 5 → ℕ)
    (hne : (relation K k q (.inl i)).coeff (Finsupp.equivFunOnFinite.symm z) ≠ 0)
    (hleft : ∀ j : HIndex k, j ≠ i → ¬ (hExp k j).1 ≤ z)
    (hright : ∀ j : HIndex k, j ≠ i → ¬ (hExp k j).2 ≤ z) :
    relation K k q (.inl i) ∉ Ideal.span
      ((fun j : HIndex k => relation K k q (.inl j)) '' {j | j ≠ i}) := by
  classical
  intro hmem
  let f : {j : HIndex k // j ≠ i} → MvPolynomial (Fin 5) K :=
    fun j => relation K k q (.inl j.val)
  have hset : ((fun j : HIndex k => relation K k q (.inl j)) '' {j | j ≠ i}) =
      Set.range f := by
    ext p
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j.val, j.property, rfl⟩
  rw [hset] at hmem
  obtain ⟨c, hc, _, _⟩ := homogeneous_mem_span_range K (fun _ : Fin 5 => 1)
    f (fun j => weight (fun _ : Fin 5 => 1) (hExp k j.val).1)
    (fun j => b5h_ordinary_homogeneous K k q hk j.val)
    (relation K k q (.inl i)) (weight (fun _ : Fin 5 => 1) (hExp k i).1)
    (b5h_ordinary_homogeneous K k q hk i) hmem
  apply hne
  rw [← hc, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro j hj
  change (c j * (mono K (hExp k j.val).1 -
    mono K (hExp k j.val).2)).coeff _ = 0
  rw [mul_sub, MvPolynomial.coeff_sub,
    b5h_coeff_mul_mono_zero K _ _ _ (hleft j.val j.property),
    b5h_coeff_mul_mono_zero K _ _ _ (hright j.val j.property), sub_self]

theorem H_nonredundant (hk : 3 ≤ k) (i : HIndex k) :
    relation K k q (.inl i) ∉
      Ideal.span
        ((fun j : HIndex k => relation K k q (.inl j)) ''
          {j | j ≠ i}) := by
  classical
  by_cases hi : i = .inl 1
  · subst i
    apply b5h_exclusion K k q hk (.inl 1) (exp5 1 0 0 0 1)
    · have hne : (hExp k (.inl 1)).1 ≠ exp5 1 0 0 0 1 := by
        intro h
        exact b5h_first_not_le_ae k hk (.inl 1) (le_of_eq h)
      simp only [relation, relExp, MvPolynomial.coeff_sub, b5h_coeff_mono_eq,
        ite_eq_right hne]
      change (0 - if exp5 1 0 0 0 1 = exp5 1 0 0 0 1 then 1 else 0 : K) ≠ 0
      simp
    · intro j hj
      exact b5h_first_not_le_ae k hk j
    · intro j hj h
      exact hj (b5h_second_le_ae k hk j h)
  · apply b5h_exclusion K k q hk i (hExp k i).1
    · have hne : (hExp k i).2 ≠ (hExp k i).1 := by
        intro h
        exact b5h_second_not_le_first k hk i i hi (le_of_eq h)
      simp [relation, relExp, b5h_coeff_mono_eq, hne]
    · intro j hj h
      exact hj (b5h_first_antichain k hk i j hi h)
    · intro j hj
      exact b5h_second_not_le_first k hk i j hi

private theorem b5_nOffset_injective (k : ℕ) : Function.Injective (nOffset k) := by
  intro i j h
  rcases i with i | i <;> rcases j with j | j <;> simp only [nOffset] at h
  · exact congrArg Sum.inl (Fin.ext h)
  · have := i.isLt
    omega
  · have := j.isLt
    omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

private theorem b5_nOffset_lt (hk : 3 ≤ k) (hq : k - 1 ≤ q) (i : NIndex k) :
    nOffset k i < 2 * k * q + 1 := by
  have hq1 : 1 ≤ q := by omega
  have hp := Nat.mul_le_mul_left (2 * k) hq1
  rcases i with i | i <;> simp only [nOffset] <;> have := i.isLt <;> omega

private theorem b5_small_homogeneous_zero
    (p : MvPolynomial (Fin 5) K) (n : ℕ)
    (hn : 0 < n) (hnm : n < 2 * k * q + 1)
    (hp : MvPolynomial.IsWeightedHomogeneous (gens k q) p n) : p = 0 := by
  rw [← hp.weightedHomogeneousComponent_same]
  apply weighted_component_eq_zero_of_small K (gens k q) (2 * k * q + 1)
  · omega
  · intro i
    fin_cases i <;> simp [gens]
  · exact hn
  · exact hnm

private theorem b5_N_coefficient_zero
    (hk : 3 ≤ k) (hq : k - 1 ≤ q)
    (n : ℕ) (hn : n < (q + 3) * (2 * k * q + 1))
    (j : NIndex k) (p : MvPolynomial (Fin 5) K)
    (hp : MvPolynomial.IsWeightedHomogeneous (gens k q) p
      (n - relationDegree k q (.inr j)))
    (hz : n < relationDegree k q (.inr j) → p = 0)
    (hne : n ≠ relationDegree k q (.inr j)) : p = 0 := by
  by_cases hlt : n < relationDegree k q (.inr j)
  · exact hz hlt
  apply b5_small_homogeneous_zero K k q p (n - relationDegree k q (.inr j))
  · omega
  · have hd : relationDegree k q (.inr j) =
        (q + 2) * (2 * k * q + 1) + nOffset k j :=
      (n_weight k q hk hq j).1
    have hn' : n < (q + 2) * (2 * k * q + 1) + (2 * k * q + 1) := by nlinarith
    omega
  · exact hp

theorem N_nonredundant
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (i : NIndex k) :
    relation K k q (.inr i) ∉
      Ideal.span (relation K k q '' {j | j ≠ .inr i}) := by
  classical
  intro hmem
  rw [Set.image_eq_range] at hmem
  obtain ⟨a, ha, hh, hz⟩ := homogeneous_mem_span_range K
    (gens k q)
    (fun j : {j : RelIndex k // j ≠ .inr i} => relation K k q j.val)
    (fun j => relationDegree k q j.val)
    (fun j => relation_weightedHomogeneous K k q hk hq j.val)
    (relation K k q (.inr i)) (relationDegree k q (.inr i))
    (relation_weightedHomogeneous K k q hk hq (.inr i)) hmem
  have hd : relationDegree k q (.inr i) =
      (q + 2) * (2 * k * q + 1) + nOffset k i :=
    (n_weight k q hk hq i).1
  have hn : relationDegree k q (.inr i) < (q + 3) * (2 * k * q + 1) := by
    have := b5_nOffset_lt k q hk hq i
    rw [hd]
    nlinarith
  have he := congrArg (psi K k) ha
  rw [map_sum] at he
  have hs : (∑ j : {j : RelIndex k // j ≠ .inr i},
      psi K k (a j * relation K k q j.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rcases j with ⟨j, hj⟩
    rcases j with j | j
    · simp only [map_mul, psi_H K k q hk j, mul_zero]
    · have hne : relationDegree k q (.inr i) ≠ relationDegree k q (.inr j) := by
        intro heq
        have hdj := (n_weight k q hk hq j).1
        change relationDegree k q (.inr j) = _ at hdj
        rw [hd, hdj] at heq
        have hij := b5_nOffset_injective k (Nat.add_left_cancel heq)
        exact hj (congrArg Sum.inr hij.symm)
      have hzj := b5_N_coefficient_zero K k q hk hq _ hn j
        (a ⟨.inr j, hj⟩) (hh _) (hz ⟨.inr j, hj⟩) hne
      rw [hzj, zero_mul, map_zero]
  exact psi_N_ne_zero K k q hk hq i (he.symm.trans hs)

private theorem b5_h_degree_upper (k q : ℕ) (hk : 3 ≤ k) (i : HIndex k) :
    relationDegree k q (.inl i) ≤ k * (2*k*q+1) + k * (2*k-1) := by
  have hm : 2 * (2*k*q+1) ≤ k * (2*k*q+1) := Nat.mul_le_mul_right _ (by omega)
  rcases i with i | i | i
  · fin_cases i <;> simp only [relationDegree, relExp, hExp, weight_gens_exp5]
    all_goals zify [show 1 ≤ 2*k by omega]
    all_goals zify at hk hm
    all_goals nlinarith
  · obtain ⟨v, hv⟩ := i
    simp only [relationDegree, relExp, hExp, weight_gens_exp5]
    zify [show 1 ≤ 2*k by omega, show 1 ≤ k by omega, show v ≤ k-1 by omega]
    have hv' : v + 1 ≤ k := by omega
    zify at hk hv'
    nlinarith
  · obtain ⟨v, hv⟩ := i
    simp only [relationDegree, relExp, hExp, weight_gens_exp5]
    zify [show 1 ≤ 2*k by omega, show 1 ≤ k by omega, show v ≤ k-1 by omega]
    have hv' : v + 2 ≤ k := by omega
    zify at hk hv'
    nlinarith

private theorem b5_h_degree_lt_k_add_two (k q : ℕ) (hk : 3 ≤ k)
    (hq : k-1 ≤ q) (i : HIndex k) :
    relationDegree k q (.inl i) < (k+2)*(2*k*q+1) := by
  have hq' : k ≤ q + 1 := by omega
  have hmul := Nat.mul_le_mul_left k hq'
  have hsq := Nat.mul_le_mul_left k hk
  have ht : k * (2*k-1) < 2 * (2*k*q+1) := by
    zify [show 1 ≤ 2*k by omega] at *
    nlinarith
  calc
    relationDegree k q (.inl i) ≤ k*(2*k*q+1) + k*(2*k-1) :=
      b5_h_degree_upper k q hk i
    _ < k*(2*k*q+1) + 2*(2*k*q+1) := Nat.add_lt_add_left ht _
    _ = (k+2)*(2*k*q+1) := by ring

theorem H_degree_lt_D
    (hk : 3 ≤ k) (hq : k ≤ q) (i : HIndex k) :
    relationDegree k q (.inl i) <
      (q+2)*(2*k*q+1) := by
  exact (b5_h_degree_lt_k_add_two k q hk (by omega) i).trans_le
    (Nat.mul_le_mul_right _ (by omega))

theorem H_boundary_collisions
    (hk : 3 ≤ k) (i : HIndex k)
    (hd :
      (k+1)*(2*k*(k-1)+1) ≤
        relationDegree k (k-1) (.inl i)) :
    relationDegree k (k-1) (.inl i) =
        (k+1)*(2*k*(k-1)+1) ∨
    relationDegree k (k-1) (.inl i) =
        (k+1)*(2*k*(k-1)+1) + (k-1) := by
  have hm : 2*k < 2*k*(k-1)+1 := by
    have hs := Nat.mul_le_mul_left k hk
    zify [show 1 ≤ k by omega] at *
    nlinarith
  have hm3 : 3*(2*k*(k-1)+1) ≤ (k+1)*(2*k*(k-1)+1) :=
    Nat.mul_le_mul_right _ (by omega)
  rcases i with i | i | i
  · fin_cases i
    all_goals simp only [relationDegree, relExp, hExp, weight_gens_exp5] at hd ⊢
    all_goals zify [show 1 ≤ k by omega, show 1 ≤ 2*k by omega] at hd hm hm3 ⊢
    · exfalso; nlinarith
    · exfalso; nlinarith
    · exfalso; nlinarith
    · right; ring
  · obtain ⟨v, hv⟩ := i
    have hv' : v ≤ k-2 := by omega
    have hmul := Nat.mul_le_mul_right (2*k-1) hv'
    simp only [relationDegree, relExp, hExp, weight_gens_exp5] at hd ⊢
    exfalso
    zify [show 1 ≤ k by omega, show 2 ≤ k by omega, show 1 ≤ 2*k by omega,
      show v ≤ k-1 by omega] at hd hm hmul
    nlinarith
  · obtain ⟨v, hv⟩ := i
    have hv' : v ≤ k-2 := by omega
    have hmul := Nat.mul_le_mul_right (2*k-1) hv'
    simp only [relationDegree, relExp, hExp, weight_gens_exp5] at hd ⊢
    left
    zify [show 1 ≤ k by omega, show 2 ≤ k by omega, show 1 ≤ 2*k by omega,
      show v ≤ k-1 by omega] at hd hmul ⊢
    nlinarith

theorem H_degree_lt_D_add_m
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (i : HIndex k) :
    relationDegree k q (.inl i) <
      (q+3)*(2*k*q+1) := by
  exact (b5_h_degree_lt_k_add_two k q hk hq i).trans_le
    (Nat.mul_le_mul_right _ (by omega))

theorem relation_nonredundant
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (i : RelIndex k) :
    relation K k q i ∉
      Ideal.span (relation K k q '' {j | j ≠ i}) := by
  classical
  rcases i with i | i
  · intro hmem
    rw [Set.image_eq_range] at hmem
    obtain ⟨a, ha, hh, hz⟩ := homogeneous_mem_span_range K
      (gens k q)
      (fun j : {j : RelIndex k // j ≠ .inl i} => relation K k q j.val)
      (fun j => relationDegree k q j.val)
      (fun j => relation_weightedHomogeneous K k q hk hq j.val)
      (relation K k q (.inl i)) (relationDegree k q (.inl i))
      (relation_weightedHomogeneous K k q hk hq (.inl i)) hmem
    have hn := H_degree_lt_D_add_m k q hk hq i
    have hcoeff : ∀ j : NIndex k, a ⟨.inr j, by simp⟩ = 0 := by
      intro j
      by_cases hd : relationDegree k q (.inl i) = relationDegree k q (.inr j)
      · let u : {j : RelIndex k // j ≠ .inl i} := ⟨.inr j, by simp⟩
        have he := congrArg (psi K k) ha
        rw [map_sum, psi_H K k q hk i] at he
        have hsum : (∑ v : {j : RelIndex k // j ≠ .inl i},
            psi K k (a v * relation K k q v.val)) =
            psi K k (a u * relation K k q (.inr j)) := by
          apply Finset.sum_eq_single u
          · intro v _ hv
            rcases v with ⟨v, hv'⟩
            rcases v with v | v
            · simp only [map_mul, psi_H K k q hk v, mul_zero]
            · have hne : relationDegree k q (.inl i) ≠
                  relationDegree k q (.inr v) := by
                intro heq
                have hjd := (n_weight k q hk hq j).1
                have hvd := (n_weight k q hk hq v).1
                change relationDegree k q (.inr j) = _ at hjd
                change relationDegree k q (.inr v) = _ at hvd
                have heq' : nOffset k j = nOffset k v := by omega
                have hjv := b5_nOffset_injective k heq'
                apply hv
                apply Subtype.ext
                exact congrArg Sum.inr hjv.symm
              have hv0 := b5_N_coefficient_zero K k q hk hq _ hn v
                (a ⟨.inr v, hv'⟩) (hh _) (hz ⟨.inr v, hv'⟩) hne
              rw [hv0, zero_mul, map_zero]
          · simp
        rw [hsum, map_mul] at he
        have hau : psi K k (a u) = 0 :=
          (mul_eq_zero.mp he).resolve_right (psi_N_ne_zero K k q hk hq j)
        have hhom : MvPolynomial.IsWeightedHomogeneous (gens k q) (a u) 0 := by
          have hu := hh u
          simpa only [u, hd, Nat.sub_self] using hu
        have hC : a u = MvPolynomial.C ((a u).coeff 0) := by
          calc
            a u = MvPolynomial.weightedHomogeneousComponent (gens k q) 0 (a u) :=
              hhom.weightedHomogeneousComponent_same.symm
            _ = MvPolynomial.C ((a u).coeff 0) :=
              MvPolynomial.weightedHomogeneousComponent_zero _
                (fun v => Nat.ne_of_gt (gens_pos k q v))
        rw [hC] at hau
        have hc : (a u).coeff 0 = 0 := by
          simpa [psi] using hau
        simpa only [u, hc, map_zero] using hC
      · exact b5_N_coefficient_zero K k q hk hq _ hn j
          (a ⟨.inr j, by simp⟩) (hh _) (hz ⟨.inr j, by simp⟩) hd
    apply H_nonredundant K k q hk i
    rw [← ha]
    apply Ideal.sum_mem
    intro j _
    rcases j with ⟨j, hj⟩
    rcases j with j | j
    · apply Ideal.mul_mem_left
      apply Ideal.subset_span
      refine ⟨j, ?_, rfl⟩
      intro hji
      exact hj (congrArg Sum.inl hji)
    · rw [hcoeff j, zero_mul]
      exact Ideal.zero_mem _
  · exact N_nonredundant K k q hk hq i

end FiveGenBetti.Family
