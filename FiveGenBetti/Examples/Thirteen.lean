/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Certificate.Defs

/-! `⟨13, 14, 16, 18, 19⟩`: the first kernel-checked instance. Apéry set by residue
`[0,14,28,16,30,18,19,33,34,35,36,37,38]`; predecessor generator indices for residues `1..12`:
`[1,1,2,2,3,4,4,3,4,3,4,4]`; contributing degrees `32,42,44,47,49,52,53,54,55,56,57`; `β₁ = 14`;
degree `32` has components `{0,4} | {1,3} | {2}` (type 1+2+2) and degree `44` has
`{0,3} | {1,2}` with generator `4` unused (type 2+2+unused), so `σ = 8 > 5`: the four-generator
singleton bound does not extend. Target: `thirteen_spanRank_le_fourteen`, then equality after the
reverse bridge. -/

@[expose] public section

namespace FiveGenBetti.Examples

def thirteen : Fin 5 → ℕ := ![13, 14, 16, 18, 19]

def thirteenApery : Fin 13 → ℕ := ![0, 14, 28, 16, 30, 18, 19, 33, 34, 35, 36, 37, 38]

end FiveGenBetti.Examples
