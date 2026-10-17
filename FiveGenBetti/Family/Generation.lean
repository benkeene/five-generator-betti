/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Family.Relations
public import FiveGenBetti.Family.NormalForms
public import FiveGenBetti.Algebra

/-! Stream B (plan 2026-10-16 §3 B3, B4): staged reduction of every monomial to `a^ℓ · (normal
form)` modulo `J`, and `J = I`. -/

@[expose] public section

namespace FiveGenBetti.Family

variable (K : Type*) [Field K] (k q : ℕ)

/-- The conclusion of the staged reduction for one monomial: either it is congruent to a normal
form of the same weight, or to `a^ℓ · z'` with `ℓ > 0` (weight bookkeeping included). -/
def Reaches (z : Fin 5 → ℕ) : Prop :=
  (∃ u : NormalForm k q,
      mono K z - normalMono K u ∈ familyIdeal K k q ∧
      weight (gens k q) z = weight (gens k q) (normalExp u)) ∨
    (∃ (ell : ℕ) (z' : Fin 5 → ℕ),
      0 < ell ∧
      mono K z - MvPolynomial.X 0 ^ ell * mono K z' ∈ familyIdeal K k q ∧
      weight (gens k q) z = ell*(2*k*q+1) + weight (gens k q) z')

theorem relation_mem_familyIdeal (i : RelIndex k) :
    relation K k q i ∈ familyIdeal K k q :=
  Ideal.subset_span ⟨i, rfl⟩

theorem reaches_trans {z y : Fin 5 → ℕ}
    (h : mono K z - mono K y ∈ familyIdeal K k q)
    (hw : weight (gens k q) z = weight (gens k q) y)
    (hy : Reaches K k q y) : Reaches K k q z := by
  rcases hy with ⟨u, hu, hwu⟩ | ⟨ell, z', hell, hz', hwz'⟩
  · refine Or.inl ⟨u, ?_, hw.trans hwu⟩
    have := add_mem h hu
    rwa [sub_add_sub_cancel] at this
  · refine Or.inr ⟨ell, z', hell, ?_, hw.trans hwz'⟩
    have := add_mem h hz'
    rwa [sub_add_sub_cancel] at this

theorem reaches_step (hk : 3 ≤ k) (hq : k-1 ≤ q) (i : RelIndex k) (w z y : Fin 5 → ℕ)
    (hz : z = (relExp k q i).1 + w) (hy : y = (relExp k q i).2 + w)
    (hY : Reaches K k q y) : Reaches K k q z := by
  subst hz hy
  refine reaches_trans K k q ?_ ?_ hY
  · rw [mono_add, mono_add, ← sub_mul]
    exact Ideal.mul_mem_right _ _ (relation_mem_familyIdeal K k q i)
  · rw [weight_add, weight_add, relExp_weight k q hk hq i]

theorem reaches_a (A b c d e : ℕ) (hA : 0 < A) : Reaches K k q (exp5 A b c d e) := by
  refine Or.inr ⟨A, exp5 0 b c d e, hA, ?_, ?_⟩
  · rw [X0_pow_mul_mono, sub_self]; exact zero_mem _
  · rw [weight_gens_exp5, weight_gens_exp5]; ring

theorem reaches_normal (u : NormalForm k q) (z : Fin 5 → ℕ) (hz : z = normalExp u) :
    Reaches K k q z := by
  subst hz
  exact Or.inl ⟨u, by rw [normalMono, sub_self]; exact zero_mem _, rfl⟩

/-- Rewrite with a relation, given as an index; the two vector identities are closed by
coordinatewise `omega`. -/
macro "exp5_tac" : tactic =>
  `(tactic| (simp only [relExp_H0, relExp_H1, relExp_H2, relExp_H3, relExp_HF, relExp_HG,
      relExp_NU, relExp_NV, exp5_add]; refine exp5_congr ?_ ?_ ?_ ?_ ?_ <;> omega))

/-- `bd → ae`. -/
theorem reaches_bd (hk : 3 ≤ k) (hq : k-1 ≤ q) (A b c d e : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) :
    Reaches K k q (exp5 A b c d e) :=
  reaches_step K k q hk hq (.inl (.inl 1)) (exp5 A (b-1) c (d-1) e) _
    (exp5 (A+1) (b-1) c (d-1) (e+1))
    (by exp5_tac) (by exp5_tac) (reaches_a K k q _ _ _ _ _ (by omega))

/-- `c² → bd → ae`. -/
theorem reaches_cc (hk : 3 ≤ k) (hq : k-1 ≤ q) (A b c d e : ℕ) (hc : 2 ≤ c) :
    Reaches K k q (exp5 A b c d e) :=
  reaches_step K k q hk hq (.inl (.inl 0)) (exp5 A b (c-2) d e) _ (exp5 A (b+1) (c-2) (d+1) e)
    (by exp5_tac) (by exp5_tac) (reaches_bd K k q hk hq _ _ _ _ _ (by omega) (by omega))

/-- `c dᴰ eʲ`. -/
theorem reaches_cde (hk : 3 ≤ k) (hq : k-1 ≤ q) (D j : ℕ) :
    Reaches K k q (exp5 0 0 1 D j) := by
  by_cases hD : k ≤ D
  · -- `dᵏ → c eᵏ⁻¹` creates `c²`
    exact reaches_step K k q hk hq (.inl (.inl 3)) (exp5 0 0 1 (D-k) j) _
      (exp5 0 0 2 (D-k) (j+(k-1))) (by exp5_tac) (by exp5_tac)
      (reaches_cc K k q hk hq _ _ _ _ _ le_rfl)
  by_cases hN : D + j + 1 ≤ q
  · exact reaches_normal K k q (.inr (.inr (.inr ⟨(⟨D, by omega⟩, ⟨j, by omega⟩), hN⟩))) _ rfl
  · -- first N branch, `r = k - 1 - D`
    exact reaches_step K k q hk hq (.inr (.inl ⟨k-1-D, by omega⟩)) (exp5 0 0 0 0 (j-(q-D))) _
      (exp5 (q+2-(k-1-D)) (k-1-D) 0 0 (j-(q-D))) (by exp5_tac) (by exp5_tac)
      (reaches_a K k q _ _ _ _ _ (by omega))

/-- `dᴰ eʲ`. -/
theorem reaches_de (hk : 3 ≤ k) (hq : k-1 ≤ q) (D j : ℕ) :
    Reaches K k q (exp5 0 0 0 D j) := by
  by_cases hD : k ≤ D
  · exact reaches_step K k q hk hq (.inl (.inl 3)) (exp5 0 0 0 (D-k) j) _
      (exp5 0 0 1 (D-k) (j+(k-1))) (by exp5_tac) (by exp5_tac)
      (reaches_cde K k q hk hq _ _)
  by_cases hN : D + j ≤ q
  · exact reaches_normal K k q (.inr (.inr (.inl ⟨(⟨D, by omega⟩, ⟨j, by omega⟩), hN⟩))) _ rfl
  · -- second N branch, `s = k - 1 - D`
    exact reaches_step K k q hk hq (.inr (.inr ⟨k-1-D, by omega⟩)) (exp5 0 0 0 0 (j-(q+1-D))) _
      (exp5 (q+1-(k-1-D)) (k-1-D) 1 0 (j-(q+1-D))) (by exp5_tac) (by exp5_tac)
      (reaches_a K k q _ _ _ _ _ (by omega))

/-- `bᴮ c eʲ`, `1 ≤ B < k`. -/
theorem reaches_bce (hk : 3 ≤ k) (hq : k-1 ≤ q) (B j : ℕ) (hB : 1 ≤ B) (hBk : B < k) :
    Reaches K k q (exp5 0 B 1 0 j) := by
  by_cases hN : B + j + 2 ≤ k
  · exact reaches_normal K k q (.inr (.inl ⟨(⟨B, by omega⟩, ⟨j, by omega⟩), ⟨hB, hN⟩⟩)) _ rfl
  · exact reaches_step K k q hk hq (.inl (.inr (.inl ⟨k-1-B, by omega⟩)))
      (exp5 0 0 0 0 (j-(k-1-B))) _ (exp5 B 0 0 (k-B) (j-(k-1-B))) (by exp5_tac) (by exp5_tac)
      (reaches_a K k q _ _ _ _ _ (by omega))

/-- `bᴮ eʲ`, `1 ≤ B < k`; at `B = 1` the rewrite `b eᵏ⁻¹ → c dᵏ⁻¹` introduces no `a`. -/
theorem reaches_be (hk : 3 ≤ k) (hq : k-1 ≤ q) (B j : ℕ) (hB : 1 ≤ B) (hBk : B < k) :
    Reaches K k q (exp5 0 B 0 0 j) := by
  by_cases hN : B + j + 1 ≤ k
  · exact reaches_normal K k q (.inl ⟨(⟨B, by omega⟩, ⟨j, by omega⟩), ⟨hB, hN⟩⟩) _ rfl
  · refine reaches_step K k q hk hq (.inl (.inr (.inr ⟨k-1-B, by omega⟩)))
      (exp5 0 0 0 0 (j-(k-B))) _ (exp5 (B-1) 0 1 (k-B) (j-(k-B))) (by exp5_tac) (by exp5_tac) ?_
    rcases Nat.lt_or_ge 1 B with h2 | h1
    · exact reaches_a K k q _ _ _ _ _ (by omega)
    · obtain rfl : B = 1 := by omega
      exact reaches_cde K k q hk hq _ _

theorem reaches_all (hk : 3 ≤ k) (hq : k-1 ≤ q) (z : Fin 5 → ℕ) : Reaches K k q z := by
  rw [eta5 z]
  generalize z 0 = A, z 1 = b, z 2 = c, z 3 = d, z 4 = e
  rcases Nat.eq_zero_or_pos A with rfl | hA
  swap; · exact reaches_a K k q _ _ _ _ _ hA
  by_cases hc : 2 ≤ c
  · exact reaches_cc K k q hk hq _ _ _ _ _ hc
  by_cases hbd : 1 ≤ b ∧ 1 ≤ d
  · exact reaches_bd K k q hk hq _ _ _ _ _ hbd.1 hbd.2
  by_cases hb : k ≤ b
  · -- `bᵏ → aᵏ⁻¹ c`
    exact reaches_step K k q hk hq (.inl (.inl 2)) (exp5 0 (b-k) c d e) _
      (exp5 (k-1) (b-k) (c+1) d e) (by exp5_tac) (by exp5_tac)
      (reaches_a K k q _ _ _ _ _ (by omega))
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  · rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
    · exact reaches_de K k q hk hq _ _
    · exact reaches_cde K k q hk hq _ _
  · obtain rfl : d = 0 := by omega
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
    · exact reaches_be K k q hk hq _ _ hb1 (by omega)
    · exact reaches_bce K k q hk hq _ _ hb1 (by omega)

theorem residual_step
    (hk : 3 ≤ k) (hq : k-1 ≤ q)
    (z : Fin 5 → ℕ) (hz : z 0 = 0) :
    (∃ u : NormalForm k q,
      mono K z - normalMono K u ∈ familyIdeal K k q ∧
      weight (gens k q) z =
        weight (gens k q) (normalExp u)) ∨
    (∃ (ell : ℕ) (z' : Fin 5 → ℕ),
      0 < ell ∧
      mono K z - MvPolynomial.X 0 ^ ell * mono K z' ∈
        familyIdeal K k q ∧
      weight (gens k q) z =
        ell*(2*k*q+1) + weight (gens k q) z') := by
  clear hz
  exact reaches_all K k q hk hq z

theorem monomial_normal_form
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (z : Fin 5 → ℕ) :
    ∃ (ell : ℕ) (u : NormalForm k q),
      mono K z - MvPolynomial.X 0 ^ ell * normalMono K u ∈
        familyIdeal K k q ∧
      weight (gens k q) z =
        ell*(2*k*q+1) + weight (gens k q) (normalExp u) := by
  induction hw : weight (gens k q) z using Nat.strong_induction_on generalizing z with
  | _ W ih =>
  subst hw
  rcases reaches_all K k q hk hq z with ⟨u, hu, hwu⟩ | ⟨ell, z', hell, hz', hwz'⟩
  · exact ⟨0, u, by simpa using hu, by simpa using hwu⟩
  · have hlt : weight (gens k q) z' < weight (gens k q) z := by
      rw [hwz']
      have : 0 < ell * (2*k*q+1) := Nat.mul_pos hell (by omega)
      omega
    obtain ⟨ell', u, hu, hwu⟩ := ih _ hlt z' rfl
    refine ⟨ell + ell', u, ?_, by rw [hwz', hwu]; ring⟩
    have := add_mem hz' (Ideal.mul_mem_left _ (MvPolynomial.X 0 ^ ell) hu)
    convert this using 1
    ring

theorem familyIdeal_eq_toricKer
    (hk : 3 ≤ k) (hq : k-1 ≤ q) :
    familyIdeal K k q = toricKer K (gens k q) := by
  apply le_antisymm
  · rw [familyIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact relation_mem_toricKer K k q hk hq i
  · apply toricKer_le_ideal_of_mono_sub_mem
    intro z z' hzz'
    obtain ⟨ell, u, hu, hwu⟩ := monomial_normal_form K k q hk hq z
    obtain ⟨ell', u', hu', hwu'⟩ := monomial_normal_form K k q hk hq z'
    obtain ⟨rfl, rfl⟩ := normal_repr_injective k q hk hq (hwu.symm.trans (hzz'.trans hwu'))
    have := sub_mem hu hu'
    rwa [sub_sub_sub_cancel_right] at this

end FiveGenBetti.Family
