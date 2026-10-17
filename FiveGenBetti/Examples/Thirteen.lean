/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Certificate.Defs
public import FiveGenBetti.Family.Main
public import FiveGenBetti.Family.Apery

/-! `⟨13, 14, 16, 18, 19⟩`: the first instance to be kernel-checked (data, and the specialization
of Theorem F). Apéry set by residue
`[0,14,28,16,30,18,19,33,34,35,36,37,38]`; predecessor generator indices for residues `1..12`:
`[1,1,2,2,3,4,4,3,4,3,4,4]`; contributing degrees `32,42,44,47,49,52,53,54,55,56,57`; `β₁ = 14`;
degree `32` has components `{0,4} | {1,3} | {2}` (type 1+2+2) and degree `44` has
`{0,3} | {1,2}` with generator `4` unused (type 2+2+unused), so `σ = 8 > 5`: the four-generator
singleton bound does not extend. `thirteen_spanRank_eq_fourteen` specializes Theorem F at
`(k, q) = (3, 2)`; it depends on F and is not an independent check of it. -/

@[expose] public section

namespace FiveGenBetti.Examples

def thirteen : Fin 5 → ℕ := ![13, 14, 16, 18, 19]

def thirteenApery : Fin 13 → ℕ := ![0, 14, 28, 16, 30, 18, 19, 33, 34, 35, 36, 37, 38]

theorem thirteen_spanRank_eq_fourteen
    (K : Type*) [Field K] :
    (toricKer K thirteen).spanRank = (14 : ℕ) := by
  have hn : Family.gens 3 2 = thirteen := by
    funext i
    fin_cases i <;> rfl
  simpa only [hn] using
    Family.spanRank_eq K 3 2 (by decide) (by decide)

/-! Benchmarks at `(k, q) = (3, 2)` (plan §6), by kernel `decide`. -/

open Family in
theorem thirteen_relIndex_card : Fintype.card (RelIndex 3) = 14 := by decide

open Family in
theorem thirteen_normalForm_card : Fintype.card (NormalForm 3 2) = 13 := by decide

open Family in
theorem thirteen_relation_weights :
    ∀ i : RelIndex 3, weight (gens 3 2) (relExp 3 2 i).1 = weight (gens 3 2) (relExp 3 2 i).2 := by
  decide

open Family in
theorem thirteen_N_degrees :
    Finset.univ.image (fun i : NIndex 3 => relationDegree 3 2 (.inr i)) = Finset.Icc 52 57 := by
  decide

open Family in
theorem thirteen_normalOffsets :
    Finset.univ.image (@normalOffset 3 2) = Finset.range 13 := by
  decide

open Family in
theorem thirteen_normalWeights :
    Finset.univ.image (fun u : NormalForm 3 2 => weight (gens 3 2) (normalExp u)) =
      {0, 14, 28, 16, 30, 18, 19, 33, 34, 35, 36, 37, 38} := by
  decide

theorem thirteen_gens : Family.gens 3 2 = thirteen := by
  funext i
  fin_cases i <;> rfl

end FiveGenBetti.Examples
