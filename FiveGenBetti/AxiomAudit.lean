/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
module

import Solution

/-! Axiom audit from `Solution` (never `Challenge`): `lake env lean FiveGenBetti/AxiomAudit.lean`.
The three statements of record show only `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms FiveGenBetti.family_spanRank_eq
#print axioms FiveGenBetti.familyGens_minimallyGenerates
#print axioms FiveGenBetti.family_presentation
