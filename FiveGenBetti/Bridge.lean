/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Fiber
public import FiveGenBetti.Algebra

/-! Stream A (plan 2026-10-16 §2 A5): the upper bridge `spanRank (toric ideal) ≤ betaFiber`.
Auxiliary to Theorem F (not on its dependency chain). -/

@[expose] public section

namespace FiveGenBetti

lemma X_mul_mono {e : ℕ} {K : Type*} [Field K]
    (i : Fin e) (u : Fin e → ℕ) :
    (MvPolynomial.X i : MvPolynomial (Fin e) K) * mono K u =
      mono K (u + Pi.single i 1) := by
  sorry

namespace GenData

variable {e : ℕ} (G : GenData e) (K : Type*) [Field K]

theorem spanRank_toricKer_le_beta1 :
    (RingHom.ker
      (MvPolynomial.aeval (R := K)
        (fun i => (Polynomial.X : Polynomial K) ^ G.n i)).toRingHom).spanRank ≤
      (G.betaFiber : Cardinal) := by
  sorry

end GenData

end FiveGenBetti
