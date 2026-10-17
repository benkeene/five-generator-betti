/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Interface

/-! Stream A (plan 2026-10-16 §2 A5): generic factorization graphs, component counts, the fiber
Betti sum `betaFiber`, and the cutoff. No ordering, gcd or minimality hypothesis. -/

@[expose] public section

namespace FiveGenBetti

variable {e : ℕ}

def SharesVar (z z' : Fin e → ℕ) : Prop :=
  ∃ i, 0 < z i ∧ 0 < z' i

instance : DecidableRel (@SharesVar e) := fun z z' =>
  inferInstanceAs (Decidable (∃ i, 0 < z i ∧ 0 < z' i))

lemma SharesVar.symm {z z' : Fin e → ℕ}
    (h : SharesVar z z') : SharesVar z' z := by
  obtain ⟨i, h1, h2⟩ := h
  exact ⟨i, h2, h1⟩

namespace GenData

variable (G : GenData e)

def nabla (d : ℕ) : SimpleGraph (G.fiber d) where
  Adj z z' := z ≠ z' ∧ SharesVar z.1 z'.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (d : ℕ) : DecidableRel (G.nabla d).Adj := fun z z' =>
  inferInstanceAs (Decidable (z ≠ z' ∧ SharesVar z.1 z'.1))

def ncomp (d : ℕ) : ℕ :=
  Fintype.card (G.nabla d).ConnectedComponent

def contributes (d : ℕ) : Prop :=
  2 ≤ G.ncomp d

instance (d : ℕ) : Decidable (G.contributes d) :=
  inferInstanceAs (Decidable (2 ≤ _))

def betaFiber : ℕ :=
  ∑ d ∈ Finset.range (G.cutoff + 1), (G.ncomp d - 1)

@[simp] lemma mem_fiber {d : ℕ} {z : Fin e → ℕ} :
    z ∈ G.fiber d ↔ G.nu z = d := by
  sorry

lemma reachable_of_coord_gt
    {d : ℕ} (z y : G.fiber d) {i : Fin e}
    (hzi : G.maxGen < z.1 i) :
    (G.nabla d).Reachable z y := by
  sorry

lemma coord_le_of_contributes
    {d : ℕ} (h : G.contributes d)
    (z : G.fiber d) (i : Fin e) :
    z.1 i ≤ G.maxGen := by
  sorry

lemma le_cutoff_of_contributes
    {d : ℕ} (h : G.contributes d) :
    d ≤ G.cutoff := by
  sorry

lemma ncomp_le_one_of_cutoff_lt
    {d : ℕ} (h : G.cutoff < d) :
    G.ncomp d ≤ 1 := by
  sorry

lemma betaFiber_eq_sum_of_le
    {L : ℕ} (hL : G.cutoff ≤ L) :
    G.betaFiber =
      ∑ d ∈ Finset.range (L + 1), (G.ncomp d - 1) := by
  sorry

end GenData

end FiveGenBetti
