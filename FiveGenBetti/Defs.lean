/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Data.Fintype.Pi

/-! Generic finite-generator infrastructure (embedding dimension `e`), generalizing
`SemigroupBetti/Defs.lean` and `Fiber.lean` of PALOMAR-2026-10-07-000005 (source commit
aa266b8a7db2794e49a0053978852ade100d23da; see docs/PORTING.md). Internal names (`toricKer`) are
distinct from the public names of `Challenge.lean`. -/

@[expose] public section

namespace FiveGenBetti

/-- The toric ideal, internal name (identical body to `Challenge.toricIdeal`). -/
noncomputable def toricKer (K : Type*) [Field K] {e : ℕ} (n : Fin e → ℕ) :
    Ideal (MvPolynomial (Fin e) K) :=
  RingHom.ker (MvPolynomial.aeval (fun i => (Polynomial.X : Polynomial K) ^ n i)).toRingHom

/-- Positive generator data in embedding dimension `e`: ordering, gcd and minimality live in
separate hypotheses, not in this structure. -/
structure GenData (e : ℕ) where
  n : Fin e → ℕ
  m : ℕ
  maxGen : ℕ
  m_pos : 0 < m
  lower : ∀ i, m ≤ n i
  upper : ∀ i, n i ≤ maxGen

namespace GenData

variable {e : ℕ} (G : GenData e)

/-- The degree of a factorization vector. -/
def nu (z : Fin e → ℕ) : ℕ := ∑ i, z i * G.n i

/-- All factorizations of `d` (a finite box filtered by degree). Not for computation. -/
def fiber (d : ℕ) : Finset (Fin e → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (d / G.m + 1)).filter (fun z => G.nu z = d)

/-- Degrees above `cutoff` contribute nothing to `β₁`. -/
def cutoff : ℕ := G.maxGen * ∑ i, G.n i

end GenData

end FiveGenBetti
