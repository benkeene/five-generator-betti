/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Family.Lemmas

/-! Stream B (plan 2026-10-16 §3 B2): the offset bijection `NormalForm k q ≃ Fin (2kq+1)` and
uniqueness of normalized representations `ℓ m + ν(u)`. -/

@[expose] public section

namespace FiveGenBetti.Family

variable (K : Type*) [Field K] (k q : ℕ)

/-- Euclidean uniqueness, in the form used throughout: `n a + ρ = n b + σ` with `ρ, σ < n`. -/
theorem mul_add_eq_mul_add {n a b ρ σ : ℕ} (hρ : ρ < n) (hσ : σ < n)
    (h : n * a + ρ = n * b + σ) : a = b ∧ ρ = σ := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · exfalso
    have h1 : n * (a + 1) ≤ n * b := Nat.mul_le_mul_left _ hab
    have h2 : n * (a + 1) = n * a + n := by ring
    omega
  · omega
  · exfalso
    have h1 : n * (b + 1) ≤ n * a := Nat.mul_le_mul_left _ hab
    have h2 : n * (b + 1) = n * b + n := by ring
    omega

/-- Block index `h` of a normal offset `2kh + ρ` (plan §3 B2 residue table). -/
def nfH {k q : ℕ} : NormalForm k q → ℕ
  | .inl p => p.val.2.val
  | .inr (.inl p) => p.val.2.val
  | .inr (.inr (.inl p)) =>
      if p.val.1.val = 0 then p.val.2.val else p.val.1.val + p.val.2.val - 1
  | .inr (.inr (.inr p)) =>
      if p.val.1.val = 0 then p.val.2.val else p.val.1.val + p.val.2.val

/-- Residue `ρ` of a normal offset `2kh + ρ` (plan §3 B2 residue table). -/
def nfR {k q : ℕ} : NormalForm k q → ℕ
  | .inl p => p.val.1.val
  | .inr (.inl p) => k + p.val.1.val
  | .inr (.inr (.inl p)) =>
      if p.val.1.val = 0 then 0 else 2*k - p.val.1.val
  | .inr (.inr (.inr p)) =>
      if p.val.1.val = 0 then k else k - p.val.1.val

theorem normalOffset_decomp (u : NormalForm k q) :
    normalOffset u = 2*k*nfH u + nfR u := by
  rcases u with ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hp⟩ | ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hp⟩ |
      ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hp⟩ | ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hp⟩ <;>
    dsimp only at hp <;>
    simp only [normalOffset, normalExp, nfH, nfR, weight_exp5, exp5_apply_zero,
      exp5_apply_one, exp5_apply_two, exp5_apply_three, exp5_apply_four]
  · ring
  · ring
  · split_ifs with h0
    · subst h0; ring
    · zify [show 1 ≤ 2 * k by omega, show i ≤ 2 * k by omega, show 1 ≤ i + j by omega]
      ring
  · split_ifs with h0
    · subst h0; ring
    · zify [show 1 ≤ 2 * k by omega, show i ≤ k by omega]
      ring

theorem nf_bounds (hk : 3 ≤ k) (hq : k-1 ≤ q) (u : NormalForm k q) :
    nfR u < 2*k ∧ nfH u ≤ q ∧ (nfH u + 1 ≤ q ∨ nfR u = 0) := by
  rcases u with ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hp⟩ | ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hp⟩ |
      ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hp⟩ | ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hp⟩ <;>
    dsimp only at hp <;> simp only [nfH, nfR] <;> (try split_ifs) <;> omega

theorem normalOffset_lt
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (u : NormalForm k q) :
    normalOffset u < 2*k*q+1 := by
  rw [normalOffset_decomp]
  obtain ⟨hR, hH, hH'⟩ := nf_bounds k q hk hq u
  rcases hH' with hH' | hH'
  · have h1 : 2*k*(nfH u + 1) ≤ 2*k*q := Nat.mul_le_mul_left _ hH'
    have h2 : 2*k*(nfH u + 1) = 2*k*nfH u + 2*k := by ring
    omega
  · have h1 : 2*k*nfH u ≤ 2*k*q := Nat.mul_le_mul_left _ hH
    omega

theorem normalOffset_injective
    (hk : 3 ≤ k) (hq : k-1 ≤ q) :
    Function.Injective (@normalOffset k q) := by
  intro u v h
  rw [normalOffset_decomp, normalOffset_decomp] at h
  obtain ⟨hHu, -, -⟩ := nf_bounds k q hk hq u
  obtain ⟨hHv, -, -⟩ := nf_bounds k q hk hq v
  obtain ⟨hH, hR⟩ := mul_add_eq_mul_add hHu hHv h
  rcases u with ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hp⟩ | ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hp⟩ |
      ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hp⟩ | ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hp⟩ <;>
  rcases v with ⟨⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩, hp'⟩ | ⟨⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩, hp'⟩ |
      ⟨⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩, hp'⟩ | ⟨⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩, hp'⟩ <;>
    dsimp only at hp hp' <;> simp only [nfH, nfR] at hH hR <;> (try split_ifs at hH hR) <;>
    first
    | omega
    | (obtain rfl : i = i' := by omega
       obtain rfl : j = j' := by omega
       rfl)

theorem normalOffset_surjective
    (hk : 3 ≤ k) (hq : k-1 ≤ q)
    (r : Fin (2*k*q+1)) :
    ∃ u : NormalForm k q, normalOffset u = r.val := by
  obtain ⟨r, hr⟩ := r
  obtain ⟨h, ρ, rfl, hρ⟩ : ∃ h ρ, r = 2*k*h + ρ ∧ ρ < 2*k :=
    ⟨r / (2*k), r % (2*k), (Nat.div_add_mod r (2*k)).symm, Nat.mod_lt _ (by omega)⟩
  have hhq : h < q ∨ (h = q ∧ ρ = 0) := by
    rcases Nat.lt_or_ge h q with h1 | h1
    · exact Or.inl h1
    · right
      rcases Nat.lt_or_ge q h with h2 | h2
      · exfalso
        have h3 : 2*k*(q+1) ≤ 2*k*h := Nat.mul_le_mul_left _ h2
        have h4 : 2*k*(q+1) = 2*k*q + 2*k := by ring
        omega
      · obtain rfl : h = q := by omega
        omega
  have key : ∀ u : NormalForm k q, nfH u = h → nfR u = ρ →
      normalOffset u = (⟨2*k*h + ρ, hr⟩ : Fin (2*k*q+1)).val := by
    intro u h1 h2
    rw [normalOffset_decomp, h1, h2]
  have hk0 : k ≠ 0 := by omega
  by_cases h0 : ρ = 0
  · subst h0
    refine ⟨.inr (.inr (.inl ⟨(⟨0, by omega⟩, ⟨h, by omega⟩), by dsimp only; omega⟩)),
      key _ ?_ ?_⟩ <;> simp [nfH, nfR]
  by_cases hkk : ρ = k
  · subst hkk
    refine ⟨.inr (.inr (.inr ⟨(⟨0, by omega⟩, ⟨h, by omega⟩), by dsimp only; omega⟩)),
      key _ ?_ ?_⟩ <;> simp [nfH, nfR]
  by_cases hlow : ρ < k
  · by_cases hB : h + ρ + 1 ≤ k
    · exact ⟨.inl ⟨(⟨ρ, by omega⟩, ⟨h, by omega⟩), by dsimp only; omega⟩,
        key _ rfl rfl⟩
    · refine ⟨.inr (.inr (.inr ⟨(⟨k - ρ, by omega⟩, ⟨h - (k - ρ), by omega⟩),
        by dsimp only; omega⟩)), key _ ?_ ?_⟩
      · simp only [nfH, show k - ρ ≠ 0 by omega, ite_false]; omega
      · simp only [nfR, show k - ρ ≠ 0 by omega, ite_false]; omega
  · by_cases hBC : h + ρ + 2 ≤ 2*k
    · exact ⟨.inr (.inl ⟨(⟨ρ - k, by omega⟩, ⟨h, by omega⟩), by dsimp only; omega⟩),
        key _ rfl (by simp only [nfR]; omega)⟩
    · refine ⟨.inr (.inr (.inl ⟨(⟨2*k - ρ, by omega⟩, ⟨h + 1 - (2*k - ρ), by omega⟩),
        by dsimp only; omega⟩)), key _ ?_ ?_⟩
      · simp only [nfH, show 2*k - ρ ≠ 0 by omega, ite_false]; omega
      · simp only [nfR, show 2*k - ρ ≠ 0 by omega, ite_false]; omega

noncomputable def normalOffsetEquiv
    (hk : 3 ≤ k) (hq : k-1 ≤ q) :
    NormalForm k q ≃ Fin (2*k*q+1) := by
  exact Equiv.ofBijective
    (fun u => ⟨normalOffset u, normalOffset_lt k q hk hq u⟩)
    ⟨fun _ _ h =>
        normalOffset_injective k q hk hq (congrArg Fin.val h),
      fun r => by
        obtain ⟨u, hu⟩ := normalOffset_surjective k q hk hq r
        exact ⟨u, Fin.ext hu⟩⟩

theorem card_normalForm
    (hk : 3 ≤ k) (hq : k-1 ≤ q) :
    Fintype.card (NormalForm k q) = 2*k*q+1 := by
  simpa using Fintype.card_congr (normalOffsetEquiv k q hk hq)

theorem normalWeight (u : NormalForm k q) :
    weight (gens k q) (normalExp u) =
      (2*k*q+1) * (∑ i, normalExp u i) + normalOffset u := by
  rw [weight_eq_five, normalOffset, weight_eq_five, Fin.sum_univ_five]
  simp only [gens_zero, gens_one, gens_two, gens_three, gens_four, exp5_apply_zero,
    exp5_apply_one, exp5_apply_two, exp5_apply_three, exp5_apply_four]
  ring

theorem normal_repr_injective
    (hk : 3 ≤ k) (hq : k-1 ≤ q)
    {ell ell' : ℕ} {u v : NormalForm k q}
    (h :
      ell*(2*k*q+1) + weight (gens k q) (normalExp u) =
        ell'*(2*k*q+1) + weight (gens k q) (normalExp v)) :
    ell = ell' ∧ u = v := by
  rw [normalWeight, normalWeight] at h
  have h' : (2*k*q+1) * (ell + ∑ i, normalExp u i) + normalOffset u =
      (2*k*q+1) * (ell' + ∑ i, normalExp v i) + normalOffset v := by
    rw [mul_add, mul_add]; linarith
  obtain ⟨h1, h2⟩ := mul_add_eq_mul_add (normalOffset_lt k q hk hq u)
    (normalOffset_lt k q hk hq v) h'
  obtain rfl := normalOffset_injective k q hk hq h2
  exact ⟨by omega, rfl⟩

end FiveGenBetti.Family
