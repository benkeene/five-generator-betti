/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Fiber
public import FiveGenBetti.Algebra

/-! Stream A (plan 2026-10-16 §2 A5): the upper bridge `spanRank (toric ideal) ≤ betaFiber`.
Auxiliary to Theorem F (not on its dependency chain). -/

@[expose] public section

namespace FiveGenBetti

lemma X_mul_mono {e : ℕ} {K : Type*} [Field K]
    (i : Fin e) (u : Fin e → ℕ) :
    (MvPolynomial.X i : MvPolynomial (Fin e) K) * mono K u =
      mono K (u + Pi.single i 1) := by
  rw [mono, mono, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
  have : Finsupp.single i 1 + Finsupp.equivFunOnFinite.symm u =
      Finsupp.equivFunOnFinite.symm (u + Pi.single i 1) := by
    refine Finsupp.ext fun j => ?_
    by_cases h : j = i
    · subst h; simp [add_comm]
    · simp [h]
  rw [this]

namespace GenData

variable {e : ℕ} (G : GenData e) (K : Type*) [Field K]

open Finset

/-! ### Representatives, base components, and the generating binomials -/

/-- A chosen representative factorization of a component of `∇_d`. -/
noncomputable def rep {d : ℕ} (C : (G.nabla d).ConnectedComponent) : Fin e → ℕ :=
  (Quot.out C : G.fiber d).1

lemma nu_rep {d : ℕ} (C : (G.nabla d).ConnectedComponent) : G.nu (G.rep C) = d :=
  G.mem_fiber.1 (Quot.out C).2

lemma rep_mk {d : ℕ} (C : (G.nabla d).ConnectedComponent) :
    (G.nabla d).connectedComponentMk (⟨G.rep C, (Quot.out C).2⟩ : G.fiber d) = C :=
  Quot.out_eq C

open Classical in
/-- The chosen binomials of degree `d`: `X^{rep C} - X^{rep C₀}` for `C ≠ C₀`, where `C₀` is
a fixed base component (none if the fiber is empty). -/
noncomputable def genSet (d : ℕ) : Finset (MvPolynomial (Fin e) K) :=
  if h : Nonempty (G.nabla d).ConnectedComponent then
    (univ.erase (Classical.choice h)).image
      (fun C => mono K (G.rep C) - mono K (G.rep (Classical.choice h)))
  else ∅

open Classical in
/-- All chosen binomials, over the degrees `d ≤ cutoff`. -/
noncomputable def binomGens : Finset (MvPolynomial (Fin e) K) :=
  (range (G.cutoff + 1)).biUnion (G.genSet K)

lemma card_genSet_le (d : ℕ) : #(G.genSet K d) ≤ G.ncomp d - 1 := by
  classical
  unfold genSet
  split_ifs with h
  · refine (card_image_le).trans ?_
    rw [card_erase_of_mem (mem_univ _), card_univ, ncomp]
  · simp

lemma card_binomGens_le : #(G.binomGens K) ≤ G.betaFiber := by
  classical
  exact (card_biUnion_le).trans (sum_le_sum fun d _ => G.card_genSet_le K d)

lemma binomGens_subset_toricKer :
    (G.binomGens K : Set (MvPolynomial (Fin e) K)) ⊆ toricKer K G.n := by
  classical
  intro p hp
  simp only [binomGens, coe_biUnion, coe_range, Set.mem_iUnion, mem_coe] at hp
  obtain ⟨d, -, hp⟩ := hp
  unfold genSet at hp
  split_ifs at hp with h
  · obtain ⟨C, -, rfl⟩ := mem_image.1 hp
    apply mono_sub_mem_toricKer
    change G.nu (G.rep C) = G.nu (G.rep _)
    rw [G.nu_rep, G.nu_rep]
  · simp at hp

/-! ### Every equal-degree binomial lies in the span -/

/-- Edge step: if `z, z'` of degree `d` share a variable `i`, then
`X^z - X^{z'} = Xᵢ (X^{z-eᵢ} - X^{z'-eᵢ})`, and the inner binomial has degree `d - nᵢ < d`. -/
lemma sub_mem_of_sharesVar {J : Ideal (MvPolynomial (Fin e) K)} {d : ℕ}
    (IH : ∀ d' < d, ∀ z z' : Fin e → ℕ, G.nu z = d' → G.nu z' = d' →
      mono K z - mono K z' ∈ J)
    {z z' : Fin e → ℕ} (hz : G.nu z = d) (hz' : G.nu z' = d) (h : SharesVar z z') :
    mono K z - mono K z' ∈ J := by
  obtain ⟨i, hi, hi'⟩ := h
  have key : ∀ y : Fin e → ℕ, 0 < y i → y = (y - Pi.single i 1) + Pi.single i 1 := by
    intro y hy; ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [hj]
  have hdeg : ∀ y : Fin e → ℕ, 0 < y i → G.nu y = G.nu (y - Pi.single i 1) + G.n i := by
    intro y hy
    conv_lhs => rw [key y hy]
    rw [G.nu_add, G.nu_single, one_mul]
  rw [key z hi, key z' hi', ← X_mul_mono, ← X_mul_mono, ← mul_sub]
  refine J.mul_mem_left _ (IH (G.nu (z - Pi.single i 1)) ?_ _ _ rfl ?_)
  · have := hdeg z hi; have := G.n_pos i; omega
  · have := hdeg z hi; have := hdeg z' hi'; omega

/-- Path step. -/
lemma sub_mem_of_reachable {J : Ideal (MvPolynomial (Fin e) K)} {d : ℕ}
    (IH : ∀ d' < d, ∀ z z' : Fin e → ℕ, G.nu z = d' → G.nu z' = d' →
      mono K z - mono K z' ∈ J)
    {x y : G.fiber d} (h : (G.nabla d).Reachable x y) : mono K x.1 - mono K y.1 ∈ J := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons u v w hadj _ ih =>
    rw [← sub_add_sub_cancel _ (mono K v.1) _]
    exact add_mem (G.sub_mem_of_sharesVar K IH (G.mem_fiber.1 u.2) (G.mem_fiber.1 v.2) hadj.2) ih

/-- Base-component step: the chosen binomials link any two representatives at a degree
`d ≤ cutoff`. -/
lemma rep_sub_rep_mem {d : ℕ} (hd : d ≤ G.cutoff) (C C' : (G.nabla d).ConnectedComponent) :
    mono K (G.rep C) - mono K (G.rep C') ∈ Ideal.span (G.binomGens K : Set _) := by
  classical
  have h : Nonempty (G.nabla d).ConnectedComponent := ⟨C⟩
  have base : ∀ D : (G.nabla d).ConnectedComponent,
      mono K (G.rep D) - mono K (G.rep (Classical.choice h)) ∈
        Ideal.span (G.binomGens K : Set _) := by
    intro D
    by_cases hD : D = Classical.choice h
    · rw [hD, sub_self]; exact zero_mem _
    · apply Ideal.subset_span
      simp only [binomGens, coe_biUnion, coe_range, Set.mem_iUnion, mem_coe, Set.mem_Iio]
      refine ⟨d, by omega, ?_⟩
      unfold genSet
      simp only [h, ↓reduceDIte]
      exact mem_image.2 ⟨D, mem_erase.2 ⟨hD, mem_univ _⟩, rfl⟩
  rw [← sub_sub_sub_cancel_right _ _ (mono K (G.rep (Classical.choice h)))]
  exact sub_mem (base C) (base C')

/-- Every binomial `X^z - X^{z'}` with `ν z = ν z'` lies in the ideal spanned by the chosen
binomials. -/
lemma mono_sub_mem_span (d : ℕ) : ∀ z z' : Fin e → ℕ, G.nu z = d → G.nu z' = d →
    mono K z - mono K z' ∈ Ideal.span (G.binomGens K : Set _) := by
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro z z' hz hz'
  obtain ⟨x, hx⟩ : ∃ x : G.fiber d, x.1 = z := ⟨⟨z, G.mem_fiber.2 hz⟩, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : G.fiber d, y.1 = z' := ⟨⟨z', G.mem_fiber.2 hz'⟩, rfl⟩
  subst hx hy
  by_cases hr : (G.nabla d).Reachable x y
  · exact G.sub_mem_of_reachable K IH hr
  · set Cx := (G.nabla d).connectedComponentMk x
    set Cy := (G.nabla d).connectedComponentMk y
    have hne : Cx ≠ Cy := fun h => hr (SimpleGraph.ConnectedComponent.exact h)
    have hd : d ≤ G.cutoff := G.le_cutoff_of_contributes (by
      unfold contributes ncomp
      exact Fintype.one_lt_card_iff.2 ⟨Cx, Cy, hne⟩)
    have h1 : mono K x.1 - mono K (G.rep Cx) ∈ Ideal.span (G.binomGens K : Set _) :=
      G.sub_mem_of_reachable K IH (x := x) (y := ⟨G.rep Cx, (Quot.out Cx).2⟩)
        (SimpleGraph.ConnectedComponent.exact (G.rep_mk Cx).symm)
    have h2 : mono K (G.rep Cy) - mono K y.1 ∈ Ideal.span (G.binomGens K : Set _) :=
      G.sub_mem_of_reachable K IH (x := ⟨G.rep Cy, (Quot.out Cy).2⟩) (y := y)
        (SimpleGraph.ConnectedComponent.exact (G.rep_mk Cy))
    have h3 := G.rep_sub_rep_mem K hd Cx Cy
    have : mono K x.1 - mono K y.1 = (mono K x.1 - mono K (G.rep Cx)) +
        (mono K (G.rep Cx) - mono K (G.rep Cy)) + (mono K (G.rep Cy) - mono K y.1) := by ring
    rw [this]
    exact add_mem (add_mem h1 h3) h2

/-! ### The kernel is spanned by the chosen binomials -/

theorem toricKer_eq_span : toricKer K G.n = Ideal.span (G.binomGens K : Set _) :=
  le_antisymm
    (toricKer_le_ideal_of_mono_sub_mem G.n _ fun z z' h =>
      G.mono_sub_mem_span K (G.nu z) z z' rfl h.symm)
    (Ideal.span_le.2 (G.binomGens_subset_toricKer K))

theorem spanRank_toricKer_le_beta1 :
    (RingHom.ker
      (MvPolynomial.aeval (R := K)
        (fun i => (Polynomial.X : Polynomial K) ^ G.n i)).toRingHom).spanRank ≤
      (G.betaFiber : Cardinal) := by
  change (toricKer K G.n).spanRank ≤ _
  rw [G.toricKer_eq_span K]
  calc (Ideal.span (G.binomGens K : Set (MvPolynomial (Fin e) K))).spanRank
      ≤ Cardinal.mk (G.binomGens K : Set (MvPolynomial (Fin e) K)) :=
        Submodule.spanRank_span_le_card _
    _ = (#(G.binomGens K) : Cardinal) := Cardinal.mk_coe_finset
    _ ≤ (G.betaFiber : Cardinal) := Nat.cast_le.2 (G.card_binomGens_le K)

end GenData

end FiveGenBetti
