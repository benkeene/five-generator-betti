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
  classical
  set I := Ideal.span (Set.range f)
  let v : s → I := fun x => ⟨x.1, hs ▸ Ideal.subset_span x.2⟩
  have hgen : Ideal.span (Set.range (fun x => (v x).val)) = I := by
    have : Set.range (fun x => (v x).val) = (s : Set (MvPolynomial (Fin e) K)) := by
      ext y
      simp [v]
    rw [this, hs]
  have htop := span_indecomposablesMk_eq_top K I v hgen
  have hle := linearIndependent_le_span (generatorClass K f) hli _ htop
  rw [Cardinal.mk_fintype, Nat.cast_le] at hle
  refine hle.trans ((Fintype.card_range_le _).trans ?_)
  simp

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
  classical
  refine le_antisymm ?_ (card_le_spanRank_of_independent_generatorClass K f
    (linearIndependent_generatorClass K w hw f d hd hf hirr))
  have hfg : (Ideal.span (Set.range f)).FG :=
    Submodule.fg_span (Set.finite_range f)
  rw [Submodule.FG.spanRank_eq_spanFinrank hfg, Nat.cast_le]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range f)).trans ?_
  have : Set.range f = ((Finset.univ.image f : Finset _) : Set (MvPolynomial (Fin e) K)) := by
    simp
  rw [this, Set.ncard_coe_finset]
  exact Finset.card_image_le

end FiveGenBetti
