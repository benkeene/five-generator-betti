/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/

module

public import FiveGenBetti.Graded.Projection

/-! Stream A (plan 2026-10-16 §2 A3): the `K`-vector space `I / 𝔪I` of indecomposables, spanning by
generator classes, and independence of the classes of an irredundant weighted-homogeneous list. -/

@[expose] public section

namespace FiveGenBetti

noncomputable def augmentationIdeal
    (K : Type*) [Field K] (e : ℕ) :
    Ideal (MvPolynomial (Fin e) K) :=
  Ideal.span (Set.range MvPolynomial.X)

noncomputable def decomposables
    (K : Type*) [Field K] {e : ℕ}
    (I : Ideal (MvPolynomial (Fin e) K)) : Submodule K I :=
  ((augmentationIdeal K e * I).restrictScalars K).comap
    (I.restrictScalars K).subtype

abbrev Indecomposables
    (K : Type*) [Field K] {e : ℕ}
    (I : Ideal (MvPolynomial (Fin e) K)) :=
  I ⧸ decomposables K I

noncomputable def indecomposablesMk
    (K : Type*) [Field K] {e : ℕ}
    (I : Ideal (MvPolynomial (Fin e) K)) :
    I →ₗ[K] Indecomposables K I :=
  (decomposables K I).mkQ

theorem mem_augmentationIdeal_iff
    (K : Type*) [Field K] {e : ℕ}
    (p : MvPolynomial (Fin e) K) :
    p ∈ augmentationIdeal K e ↔ p.coeff 0 = 0 := by
  rw [augmentationIdeal, ← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h
    by_contra h0
    obtain ⟨i, -, hi⟩ := h 0 (MvPolynomial.mem_support_iff.2 h0)
    exact hi rfl
  · intro h m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact MvPolynomial.mem_support_iff.1 hm h
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hm0
    exact ⟨i, Set.mem_univ _, hi⟩

theorem sub_C_coeff_zero_mem_augmentationIdeal
    (K : Type*) [Field K] {e : ℕ}
    (p : MvPolynomial (Fin e) K) :
    p - MvPolynomial.C (p.coeff 0) ∈ augmentationIdeal K e := by
  rw [mem_augmentationIdeal_iff]
  simp

theorem indecomposablesMk_eq_zero_iff
    (K : Type*) [Field K] {e : ℕ}
    (I : Ideal (MvPolynomial (Fin e) K)) (x : I) :
    indecomposablesMk K I x = 0 ↔ x.val ∈ augmentationIdeal K e * I := by
  rw [indecomposablesMk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

theorem indecomposablesMk_mul
    (K : Type*) [Field K] {e : ℕ}
    (I : Ideal (MvPolynomial (Fin e) K))
    (p : MvPolynomial (Fin e) K) (x : I) :
    indecomposablesMk K I
        ⟨p * x.val, I.mul_mem_left p x.property⟩ =
      p.coeff 0 • indecomposablesMk K I x := by
  rw [← map_smul, ← sub_eq_zero, ← map_sub, indecomposablesMk_eq_zero_iff]
  have : (⟨p * x.val, I.mul_mem_left p x.property⟩ - p.coeff 0 • x : I).val =
      (p - MvPolynomial.C (p.coeff 0)) * x.val := by
    simp [sub_mul, MvPolynomial.C_mul']
  rw [this]
  exact Ideal.mul_mem_mul (sub_C_coeff_zero_mem_augmentationIdeal K p) x.property

theorem span_indecomposablesMk_eq_top
    (K : Type*) [Field K] {e : ℕ}
    (I : Ideal (MvPolynomial (Fin e) K))
    {ι : Type*} (f : ι → I)
    (hgen :
      Ideal.span (Set.range (fun i => (f i).val)) = I) :
    Submodule.span K
      (Set.range (fun i => indecomposablesMk K I (f i))) = ⊤ := by
  set S := Submodule.span K (Set.range (fun i => indecomposablesMk K I (f i)))
  have key : ∀ y (hy : y ∈ Ideal.span (Set.range (fun i => (f i).val))),
      ∀ h : y ∈ I, indecomposablesMk K I ⟨y, h⟩ ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro h
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero =>
      intro h
      have : (⟨0, h⟩ : I) = 0 := rfl
      rw [this, map_zero]
      exact S.zero_mem
    | add x y hx hy ihx ihy =>
      intro h
      have hx' : x ∈ I := hgen ▸ hx
      have hy' : y ∈ I := hgen ▸ hy
      have : (⟨x + y, h⟩ : I) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
      rw [this, map_add]
      exact S.add_mem (ihx hx') (ihy hy')
    | smul a x hx ihx =>
      intro h
      have hx' : x ∈ I := hgen ▸ hx
      have := indecomposablesMk_mul K I a ⟨x, hx'⟩
      simp only at this
      rw [show (⟨a • x, h⟩ : I) = ⟨a * x, I.mul_mem_left a hx'⟩ from rfl, this]
      exact S.smul_mem _ (ihx hx')
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact key x.val (hgen.symm ▸ x.property) x.property

noncomputable def generatorClass
    (K : Type*) [Field K] {e : ℕ}
    {ι : Type} (f : ι → MvPolynomial (Fin e) K) (i : ι) :
    Indecomposables K (Ideal.span (Set.range f)) :=
  indecomposablesMk K _
    ⟨f i, Ideal.subset_span ⟨i, rfl⟩⟩

theorem linearIndependent_generatorClass
    (K : Type*) [Field K] {e : ℕ}
    {ι : Type} [Fintype ι]
    (w : Fin e → ℕ) (hw : ∀ i, 0 < w i)
    (f : ι → MvPolynomial (Fin e) K) (d : ι → ℕ)
    (hd : ∀ i, 0 < d i)
    (hf : ∀ i, MvPolynomial.IsWeightedHomogeneous w (f i) (d i))
    (hirr : ∀ i, f i ∉ Ideal.span (f '' {j | j ≠ i})) :
    LinearIndependent K (generatorClass K f) := by
  classical
  set I := Ideal.span (Set.range f)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- the dependence lies in `𝔪 I`
  have hmem : ∑ i, g i • f i ∈ augmentationIdeal K e * I := by
    have h0 : indecomposablesMk K I (∑ i, g i • (⟨f i, Ideal.subset_span ⟨i, rfl⟩⟩ : I)) = 0 := by
      rw [map_sum]
      simpa only [map_smul, generatorClass] using hg
    rw [indecomposablesMk_eq_zero_iff] at h0
    simpa using h0
  -- write it with coefficients in `𝔪`
  obtain ⟨a, ha, hsum⟩ :=
    (Submodule.mem_ideal_smul_span_iff_exists_sum (augmentationIdeal K e) f _).1 hmem
  rw [Finsupp.sum_fintype a (fun i c => c • f i) (fun i => zero_smul _ _)] at hsum
  have hzero : ∑ i, (MvPolynomial.C (g i) - a i) * f i = 0 := by
    simp only [smul_eq_mul] at hsum
    simp only [sub_mul, Finset.sum_sub_distrib, MvPolynomial.C_mul', hsum, sub_self]
  intro j
  by_contra hgj
  apply hirr j
  set J := Ideal.span (f '' {i | i ≠ j})
  -- project to degree `d j`
  have hproj := congrArg (MvPolynomial.weightedHomogeneousComponent w (d j)) hzero
  rw [map_sum, map_zero, ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    homogeneousComponent_mul_right K w _ _ _ _ (hf j)] at hproj
  simp only [le_refl, ↓reduceIte, Nat.sub_self] at hproj
  have hw' : ∀ i, w i ≠ 0 := fun i => (hw i).ne'
  rw [MvPolynomial.weightedHomogeneousComponent_zero _ hw'] at hproj
  have hc : (MvPolynomial.C (g j) - a j).coeff 0 = g j := by
    have := (mem_augmentationIdeal_iff K (a j)).1 (ha j)
    simp [this]
  rw [hc] at hproj
  have hrest : ∑ i ∈ Finset.univ.erase j,
      MvPolynomial.weightedHomogeneousComponent w (d j)
        ((MvPolynomial.C (g i) - a i) * f i) ∈ J := by
    refine J.sum_mem fun i hi => ?_
    rw [homogeneousComponent_mul_right K w _ _ _ _ (hf i)]
    split_ifs
    · exact J.mul_mem_left _ (Ideal.subset_span ⟨i, Finset.ne_of_mem_erase hi, rfl⟩)
    · exact J.zero_mem
  have hCj : MvPolynomial.C (g j) * f j ∈ J := by
    rw [eq_neg_of_add_eq_zero_left hproj]
    exact J.neg_mem hrest
  have := J.mul_mem_left (MvPolynomial.C (g j)⁻¹) hCj
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hgj, map_one, one_mul] at this

end FiveGenBetti
