/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Family.Defs

/-! Real family data (plan 2026-10-16 §1, verbatim): relation exponents `H`/`N`, the relation
binomials and their ideal `J`, degrees, the normal-form index type and its offsets, the projection
`ψ`, and the Apéry predicate. -/

@[expose] public section

namespace FiveGenBetti.Family

def exp5 (a b c d e : ℕ) : Fin 5 → ℕ :=
  ![a, b, c, d, e]

def hExp (k : ℕ) :
    HIndex k → (Fin 5 → ℕ) × (Fin 5 → ℕ)
  | .inl i => match i.val with
    | 0 => (exp5 0 0 2 0 0, exp5 0 1 0 1 0)
    | 1 => (exp5 0 1 0 1 0, exp5 1 0 0 0 1)
    | 2 => (exp5 0 k 0 0 0, exp5 (k-1) 0 1 0 0)
    | _ => (exp5 0 0 0 k 0, exp5 0 0 1 0 (k-1))
  | .inr (.inl i) =>
      (exp5 0 (k-1-i.val) 1 0 i.val,
       exp5 (k-1-i.val) 0 0 (i.val+1) 0)
  | .inr (.inr i) =>
      (exp5 0 (k-1-i.val) 0 0 (i.val+1),
       exp5 (k-2-i.val) 0 1 (i.val+1) 0)

def nExp (k q : ℕ) :
    NIndex k → (Fin 5 → ℕ) × (Fin 5 → ℕ)
  | .inl r =>
      (exp5 0 0 1 (k-1-r.val) (q+1+r.val-k),
       exp5 (q+2-r.val) r.val 0 0 0)
  | .inr s =>
      (exp5 0 0 0 (k-1-s.val) (q+2+s.val-k),
       exp5 (q+1-s.val) s.val 1 0 0)

abbrev RelIndex (k : ℕ) :=
  HIndex k ⊕ NIndex k

def relExp (k q : ℕ) :
    RelIndex k → (Fin 5 → ℕ) × (Fin 5 → ℕ)
  | .inl i => hExp k i
  | .inr i => nExp k q i

noncomputable def relation
    (K : Type*) [Field K] (k q : ℕ) (i : RelIndex k) :
    MvPolynomial (Fin 5) K :=
  mono K (relExp k q i).1 - mono K (relExp k q i).2

noncomputable def familyIdeal
    (K : Type*) [Field K] (k q : ℕ) :
    Ideal (MvPolynomial (Fin 5) K) :=
  Ideal.span (Set.range (relation K k q))

def relationDegree (k q : ℕ) (i : RelIndex k) : ℕ :=
  weight (gens k q) (relExp k q i).1

def nOffset (k : ℕ) : NIndex k → ℕ
  | .inl r => r.val
  | .inr s => k + s.val

abbrev NormalB (k : ℕ) :=
  {p : Fin k × Fin k //
    1 ≤ p.1.val ∧ p.1.val + p.2.val + 1 ≤ k}

abbrev NormalBC (k : ℕ) :=
  {p : Fin k × Fin k //
    1 ≤ p.1.val ∧ p.1.val + p.2.val + 2 ≤ k}

abbrev NormalD (k q : ℕ) :=
  {p : Fin k × Fin (q+1) //
    p.1.val + p.2.val ≤ q}

abbrev NormalCD (k q : ℕ) :=
  {p : Fin k × Fin (q+1) //
    p.1.val + p.2.val + 1 ≤ q}

abbrev NormalForm (k q : ℕ) :=
  NormalB k ⊕
    (NormalBC k ⊕ (NormalD k q ⊕ NormalCD k q))

def normalExp {k q : ℕ} :
    NormalForm k q → (Fin 5 → ℕ)
  | .inl p =>
      exp5 0 p.val.1.val 0 0 p.val.2.val
  | .inr (.inl p) =>
      exp5 0 p.val.1.val 1 0 p.val.2.val
  | .inr (.inr (.inl p)) =>
      exp5 0 0 0 p.val.1.val p.val.2.val
  | .inr (.inr (.inr p)) =>
      exp5 0 0 1 p.val.1.val p.val.2.val

def normalOffset {k q : ℕ} (u : NormalForm k q) : ℕ :=
  weight (exp5 0 1 k (2*k-1) (2*k)) (normalExp u)

noncomputable def normalMono
    (K : Type*) [Field K] {k q : ℕ} (u : NormalForm k q) :
    MvPolynomial (Fin 5) K :=
  mono K (normalExp u)

def offset (k : ℕ) : Fin 5 → ℕ :=
  exp5 0 1 k (2*k-1) (2*k)

noncomputable def psi (K : Type*) [Field K] (k : ℕ) :
    MvPolynomial (Fin 5) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval
    (fun i => MvPolynomial.X 0 * MvPolynomial.X 1 ^ offset k i)

def attainable (k q d : ℕ) : Prop :=
  ∃ z : Fin 5 → ℕ, weight (gens k q) z = d

def IsApery (k q d : ℕ) : Prop :=
  attainable k q d ∧
    ¬ ∃ t, attainable k q t ∧ d = t + (2*k*q+1)

end FiveGenBetti.Family
