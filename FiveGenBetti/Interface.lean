/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Defs
public import Mathlib

/-! Frozen shared interface (plan 2026-10-16 §1): exponent vectors to monomials, and weights. -/

@[expose] public section

namespace FiveGenBetti

noncomputable def mono (K : Type*) [Field K] {e : ℕ}
    (z : Fin e → ℕ) : MvPolynomial (Fin e) K :=
  MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm z) 1

def weight {e : ℕ} (n z : Fin e → ℕ) : ℕ :=
  ∑ i, z i * n i

end FiveGenBetti
