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

/-! ### Arithmetic of `nu` (ported from the vendored `Defs.lean`) -/

lemma n_pos (i : Fin e) : 0 < G.n i := lt_of_lt_of_le G.m_pos (G.lower i)

@[simp] lemma nu_zero : G.nu 0 = 0 := by simp [nu]

lemma nu_add (x y : Fin e → ℕ) : G.nu (x + y) = G.nu x + G.nu y := by
  simp [nu, add_mul, Finset.sum_add_distrib]

lemma nu_single (i : Fin e) (k : ℕ) : G.nu (Pi.single i k) = k * G.n i := by
  simp only [nu]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

lemma nu_sub {x y : Fin e → ℕ} (h : x ≤ y) : G.nu y = G.nu x + G.nu (y - x) := by
  rw [← nu_add]; congr 1; ext i; simp only [Pi.add_apply, Pi.sub_apply]
  have hi : x i ≤ y i := h i
  omega

lemma single_le_nu (z : Fin e → ℕ) (i : Fin e) : z i * G.n i ≤ G.nu z := by
  unfold nu
  exact Finset.single_le_sum (f := fun j => z j * G.n j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)

lemma m_mul_le_nu (z : Fin e → ℕ) (i : Fin e) : G.m * z i ≤ G.nu z := by
  calc G.m * z i ≤ z i * G.n i := by rw [mul_comm]; exact Nat.mul_le_mul_left _ (G.lower i)
    _ ≤ G.nu z := G.single_le_nu z i

lemma nu_pos_of_pos {z : Fin e → ℕ} {i : Fin e} (h : 0 < z i) : 0 < G.nu z :=
  lt_of_lt_of_le (Nat.mul_pos h (G.n_pos i)) (G.single_le_nu z i)

lemma le_div_m_of_nu_eq {z : Fin e → ℕ} {d : ℕ} (h : G.nu z = d) (i : Fin e) :
    z i ≤ d / G.m := by
  rw [Nat.le_div_iff_mul_le G.m_pos, mul_comm, ← h]; exact G.m_mul_le_nu z i

lemma nu_replace {u v x : Fin e → ℕ} (hux : u ≤ x) (huv : G.nu u = G.nu v) :
    G.nu (x - u + v) = G.nu x := by
  rw [G.nu_add, G.nu_sub hux, huv, add_comm]

@[simp] lemma mem_fiber {d : ℕ} {z : Fin e → ℕ} :
    z ∈ G.fiber d ↔ G.nu z = d := by
  simp only [fiber, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    and_iff_right_iff_imp]
  intro h i; exact Nat.lt_succ_of_le (G.le_div_m_of_nu_eq h i)

/-! ### Basic graph facts -/

lemma reachable_of_sharesVar {d : ℕ} {z y : G.fiber d} (h : SharesVar z.1 y.1) :
    (G.nabla d).Reachable z y := by
  by_cases hzy : z = y
  · subst hzy; rfl
  · exact SimpleGraph.Adj.reachable ⟨hzy, h⟩

lemma ncomp_le_one_of_reachable {d : ℕ} (h : ∀ z y : G.fiber d, (G.nabla d).Reachable z y) :
    G.ncomp d ≤ 1 := by
  unfold ncomp
  rw [Fintype.card_le_one_iff_subsingleton]
  exact ⟨SimpleGraph.ConnectedComponent.ind₂ fun v w =>
    SimpleGraph.ConnectedComponent.sound (h v w)⟩

lemma exists_not_reachable {d : ℕ} (h : 2 ≤ G.ncomp d) :
    ∃ z y : G.fiber d, ¬ (G.nabla d).Reachable z y := by
  by_contra hne
  push Not at hne
  have := G.ncomp_le_one_of_reachable hne
  omega

lemma reachable_of_bridge {d : ℕ} {z y : G.fiber d} (b : Fin e → ℕ) (hb : G.nu b = d)
    (hz : SharesVar b z.1) (hy : SharesVar b y.1) : (G.nabla d).Reachable z y := by
  let b' : G.fiber d := ⟨b, G.mem_fiber.2 hb⟩
  exact (G.reachable_of_sharesVar (z := b') hz).symm.trans (G.reachable_of_sharesVar hy)

/-! ### The finite cutoff -/

lemma reachable_of_coord_gt
    {d : ℕ} (z y : G.fiber d) {i : Fin e}
    (hzi : G.maxGen < z.1 i) :
    (G.nabla d).Reachable z y := by
  have hz := G.mem_fiber.1 z.2
  have hy := G.mem_fiber.1 y.2
  -- some coordinate `j` of `y` is positive
  obtain ⟨j, hj⟩ : ∃ j, 0 < y.1 j := by
    by_contra hc; push Not at hc
    have : y.1 = 0 := funext fun k => Nat.le_zero.1 (hc k)
    rw [this, nu_zero] at hy
    have := G.nu_pos_of_pos (z := z.1) (i := i) (by omega)
    omega
  by_cases hzj : 0 < z.1 j
  · exact G.reachable_of_sharesVar ⟨j, hzj, hj⟩
  have hij : i ≠ j := by rintro rfl; omega
  have hnj := G.upper j
  -- the bridge `b = z - nⱼ eᵢ + nᵢ eⱼ`
  have hle : Pi.single i (G.n j) ≤ z.1 := by
    intro k
    by_cases hk : k = i
    · subst hk; simp; omega
    · simp [hk]
  have heq : G.nu (Pi.single i (G.n j)) = G.nu (Pi.single j (G.n i)) := by
    rw [G.nu_single, G.nu_single, mul_comm]
  refine G.reachable_of_bridge (z.1 - Pi.single i (G.n j) + Pi.single j (G.n i))
    ((G.nu_replace hle heq).trans hz) ⟨i, ?_, by omega⟩ ⟨j, ?_, hj⟩
  · simp [hij]; omega
  · simp [hij.symm, G.n_pos i]

lemma coord_le_of_contributes
    {d : ℕ} (h : G.contributes d)
    (z : G.fiber d) (i : Fin e) :
    z.1 i ≤ G.maxGen := by
  by_contra hc
  push Not at hc
  obtain ⟨y, y', hyy'⟩ := G.exists_not_reachable h
  exact hyy' (((G.reachable_of_coord_gt z y hc).symm).trans (G.reachable_of_coord_gt z y' hc))

lemma le_cutoff_of_contributes
    {d : ℕ} (h : G.contributes d) :
    d ≤ G.cutoff := by
  obtain ⟨z, -, -⟩ := G.exists_not_reachable h
  rw [← G.mem_fiber.1 z.2, nu, cutoff, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (G.coord_le_of_contributes h z i)

lemma ncomp_le_one_of_cutoff_lt
    {d : ℕ} (h : G.cutoff < d) :
    G.ncomp d ≤ 1 := by
  by_contra hc
  push Not at hc
  have := G.le_cutoff_of_contributes (d := d) hc
  omega

lemma betaFiber_eq_sum_of_le
    {L : ℕ} (hL : G.cutoff ≤ L) :
    G.betaFiber =
      ∑ d ∈ Finset.range (L + 1), (G.ncomp d - 1) := by
  unfold betaFiber
  rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : G.cutoff + 1 ≤ L + 1))]
  intro d hd hd'
  simp only [Finset.mem_range] at hd hd'
  have := G.ncomp_le_one_of_cutoff_lt (d := d) (by omega)
  omega

end GenData

end FiveGenBetti
