/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Graded.Indecomposables

/-! Stream A (plan 2026-10-16 §1, §2 A4): an irredundant list of positive-degree
weighted-homogeneous generators has `spanRank` equal to its length (comparison with arbitrary
generating sets). -/

@[expose] public section

namespace FiveGenBetti

theorem card_le_card_of_span_eq
    (K : Type*) [Field K] {e : ℕ}
    {ι : Type} [Fintype ι]
    (f : ι → MvPolynomial (Fin e) K)
    (hli : LinearIndependent K (generatorClass K f))
    (s : Finset (MvPolynomial (Fin e) K))
    (hs :
      Ideal.span (s : Set (MvPolynomial (Fin e) K)) =
        Ideal.span (Set.range f)) :
    Fintype.card ι ≤ s.card := by
  sorry

theorem card_le_spanRank_of_independent_generatorClass
    (K : Type*) [Field K] {e : ℕ}
    {ι : Type} [Fintype ι]
    (f : ι → MvPolynomial (Fin e) K)
    (hli : LinearIndependent K (generatorClass K f)) :
    (Fintype.card ι : Cardinal) ≤
      (Ideal.span (Set.range f)).spanRank := by
  have hfg : (Ideal.span (Set.range f)).FG :=
    Submodule.fg_span (Set.finite_range f)
  obtain ⟨s, hc, hs⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  rw [Submodule.FG.spanRank_eq_spanFinrank hfg, ← hc]
  exact_mod_cast card_le_card_of_span_eq K f hli s hs

theorem spanRank_eq_card_of_weightedHomogeneous_irredundant
    (K : Type*) [Field K] {e : ℕ}
    {ι : Type} [Fintype ι]
    (w : Fin e → ℕ) (hw : ∀ i, 0 < w i)
    (f : ι → MvPolynomial (Fin e) K) (d : ι → ℕ)
    (hd : ∀ i, 0 < d i)
    (hf : ∀ i, MvPolynomial.IsWeightedHomogeneous w (f i) (d i))
    (hirr : ∀ i, f i ∉ Ideal.span (f '' {j | j ≠ i})) :
    (Ideal.span (Set.range f)).spanRank =
      (Fintype.card ι : Cardinal) := by
  sorry

end FiveGenBetti
