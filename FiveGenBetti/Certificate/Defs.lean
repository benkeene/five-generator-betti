/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Defs

/-! Packed predecessor-tree certificates for Apéry sets (two bits per residue naming the generator
that reaches it), the reconstruction `A_r = A_{p(r)} + n_{j(r)}`, closure inequalities, candidate
degrees, support graphs and the checked `β₁`. Parent residues are `(r + m - n_j % m) % m`, never
`r - n_j` before the modulus. Soundness lemmas (Apéry correctness, candidate completeness, graph
correspondence) live in `Soundness.lean` (to be written). -/

@[expose] public section

namespace FiveGenBetti.Certificate

/-- A certificate: for each nonzero residue the index (in `1..4`, stored as `Fin 4`) of the
generator that reaches it from its parent. -/
structure AperyCertificate (m : ℕ) where
  parent : Fin m → Fin 4

end FiveGenBetti.Certificate
