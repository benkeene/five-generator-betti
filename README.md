# five-generator-betti

Lean 4 / Mathlib formalization (in preparation) of two statements about minimally
five-generated numerical semigroups S = ⟨n₀ < n₁ < n₂ < n₃ < n₄⟩ of width w = n₄ − n₀:

1. The family S(m,k) = ⟨m, m+1, m+k, m+2k−1, m+2k⟩ with m = 2kq + 1, k ≥ 3, q ≥ k − 1 has
   β₁(K[S]) = 4k + 2 (an explicit minimal presentation with 2k+2 homogeneous and 2k
   inhomogeneous binomials).
2. β₁(K[S]) ≤ 2w + 2 for every minimally five-generated S with 4 ≤ w ≤ 40 (finite-width
   statement, to be supported by a certified sweep over the periodicity window m ≤ w² + w).

Status: PROOF_ATTEMPT for (1), conjecture for (2) (2026-10-16). Informal argument in `docs/`;
scaffolding plan in `docs/astra/`. Template and reusable library: `~/semigroup-betti`
(Palomar entry PALOMAR-2026-10-07-000005; four-generator case β₁ ≤ 2w).
