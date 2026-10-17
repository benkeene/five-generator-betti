/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Family.Data

/-! Stream B (plan 2026-10-16 §3 B2): the offset bijection `NormalForm k q ≃ Fin (2kq+1)` and
uniqueness of normalized representations `ℓ m + ν(u)`. -/

@[expose] public section

namespace FiveGenBetti.Family

variable (K : Type*) [Field K] (k q : ℕ)

theorem normalOffset_lt
    (hk : 3 ≤ k) (hq : k-1 ≤ q) (u : NormalForm k q) :
    normalOffset u < 2*k*q+1 := by
  sorry

theorem normalOffset_injective
    (hk : 3 ≤ k) (hq : k-1 ≤ q) :
    Function.Injective (@normalOffset k q) := by
  sorry

theorem normalOffset_surjective
    (hk : 3 ≤ k) (hq : k-1 ≤ q)
    (r : Fin (2*k*q+1)) :
    ∃ u : NormalForm k q, normalOffset u = r.val := by
  sorry

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
  sorry

theorem normal_repr_injective
    (hk : 3 ≤ k) (hq : k-1 ≤ q)
    {ell ell' : ℕ} {u v : NormalForm k q}
    (h :
      ell*(2*k*q+1) + weight (gens k q) (normalExp u) =
        ell'*(2*k*q+1) + weight (gens k q) (normalExp v)) :
    ell = ell' ∧ u = v := by
  sorry

end FiveGenBetti.Family
