/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Family.Defs

/-! The family is minimally five-generated: no generator lies in the additive closure of the other
four. Every generator is at least `m = 2kq + 1`, so a nonzero element of the closure is either a
single generator or at least `2m`, and `m + 2k < 2m` once `q ≥ 1`. This is the content of
`Challenge.MinimallyGenerates (familyGens k q)`; Theorem F does not depend on it. -/

@[expose] public section

namespace FiveGenBetti.Family

theorem gens_le (k q : ℕ) (hk : 3 ≤ k) (i : Fin 5) : gens k q i ≤ 2 * k * q + 1 + 2 * k := by
  fin_cases i <;> simp [gens] <;> omega

theorem le_gens (k q : ℕ) (i : Fin 5) : 2 * k * q + 1 ≤ gens k q i := by
  fin_cases i <;> simp [gens]

/-- No generator of the family is a sum of the others. -/
theorem gens_minimallyGenerates (k q : ℕ) (hk : 3 ≤ k) (hq : k - 1 ≤ q) (i : Fin 5) :
    gens k q i ∉ AddSubmonoid.closure (gens k q '' {j | j ≠ i}) := by
  intro hmem
  -- Every element of the closure is `0`, a generator other than `gens k q i`, or at least `2m`.
  have key : ∀ x ∈ AddSubmonoid.closure (gens k q '' {j | j ≠ i}),
      x = 0 ∨ (∃ j, j ≠ i ∧ x = gens k q j) ∨ 2 * (2 * k * q + 1) ≤ x := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact Or.inr (Or.inl ⟨j, hj, rfl⟩)
    | zero => exact Or.inl rfl
    | add x y _ _ ihx ihy =>
      have hm : ∀ z, (z = 0 ∨ (∃ j, j ≠ i ∧ z = gens k q j) ∨ 2 * (2 * k * q + 1) ≤ z) →
          z = 0 ∨ 2 * k * q + 1 ≤ z := by
        rintro z (rfl | ⟨j, _, rfl⟩ | h)
        · exact Or.inl rfl
        · exact Or.inr (le_gens k q j)
        · exact Or.inr (by omega)
      rcases hm x ihx with rfl | hx
      · simpa using ihy
      · rcases hm y ihy with rfl | hy
        · simpa using ihx
        · exact Or.inr (Or.inr (by omega))
  rcases key _ hmem with h0 | ⟨j, hj, hji⟩ | h2
  · exact absurd h0 (Nat.pos_iff_ne_zero.mp (gens_pos k q i))
  · exact hj ((gens_strictMono k q hk).injective hji).symm
  · have h1 : gens k q i ≤ 2 * k * q + 1 + 2 * k := gens_le k q hk i
    have hq1 : 1 ≤ q := by omega
    have h3 : 2 * k ≤ 2 * k * q := Nat.le_mul_of_pos_right (2 * k) hq1
    omega

end FiveGenBetti.Family
