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
  sorry

theorem indecomposablesMk_mul
    (K : Type*) [Field K] {e : ℕ}
    (I : Ideal (MvPolynomial (Fin e) K))
    (p : MvPolynomial (Fin e) K) (x : I) :
    indecomposablesMk K I
        ⟨p * x.val, I.mul_mem_left p x.property⟩ =
      p.coeff 0 • indecomposablesMk K I x := by
  sorry

theorem span_indecomposablesMk_eq_top
    (K : Type*) [Field K] {e : ℕ}
    (I : Ideal (MvPolynomial (Fin e) K))
    {ι : Type*} (f : ι → I)
    (hgen :
      Ideal.span (Set.range (fun i => (f i).val)) = I) :
    Submodule.span K
      (Set.range (fun i => indecomposablesMk K I (f i))) = ⊤ := by
  sorry

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
  sorry

end FiveGenBetti
