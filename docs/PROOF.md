# Informal proof of Theorem F (PROOF_ATTEMPT, 2026-10-16)

Source: `docs/astra/2026-10-16_workflow_betti.md` §2 and the scaffold plan (§8). Labels are the
intended Lean names. Review gate before `Family.Minimality` is formalized: adversary (minimality,
boundary q = k − 1) → response → reviewer → independent reconstruction. The objection log must
record the refuted indispensability claim and its correction to nonredundancy.

Variables a, b, c, d, e of weights m, m+1, m+k, m+2k−1, m+2k; m = 2kq + 1, k ≥ 3, q ≥ k − 1.

## Family.Relations
H (2k + 2): c² − bd, bd − ae, bᵏ − aᵏ⁻¹c, dᵏ − c eᵏ⁻¹, and for 0 ≤ i ≤ k − 2:
b^{k−1−i} c eⁱ − a^{k−1−i} d^{i+1}, b^{k−1−i} e^{i+1} − a^{k−2−i} c d^{i+1}.
N (2k): U_r − V_r with U_r = c d^{k−1−r} e^{q+1+r−k}, V_r = a^{q+2−r} bʳ (r < k) and
U_{k+s} = d^{k−1−s} e^{q+2+s−k}, V_{k+s} = a^{q+1−s} bˢ c (s < k); degree D + r, D = (q+2)m;
ordinary lengths q + 1 and q + 2. All exponents nonnegative at q = k − 1. Membership in I by
weight identities (`mono_sub_mem_toricKer`).

## Family.NormalForms
Four monomial families (A): bⁱeʲ (i ≥ 1, i + j ≤ k − 1); bⁱceʲ (i ≥ 1, i + j ≤ k − 2);
dᵗeʲ (t < k, t + j ≤ q); c dᵗ eʲ (t < k, t + j ≤ q − 1). Offsets i + 2kj, k + i + 2kj,
2k(t+j) − t, k + 2k(t+j) − t partition {0, …, 2kq} (split by residue mod 2k); hence exactly
m = 2kq + 1 normal forms (`normalOffsetEquiv`).

## Family.Generation
`monomial_normal_form`: every monomial ≡ a^ℓ · (normal form) mod J, by strong induction on
weighted degree whenever a reduction introduces a; reductions: c², bd, bᵏ introduce a; excess
bⁱceʲ and bⁱeʲ via the H families; b e^{k−1} → c d^{k−1}; dᵏ → c e^{k−1} (a second one gives c²);
excess dᵗeʲ, c dᵗ eʲ via U_{2k−1−t}, U_{k−1−t}. Distinct normal forms have distinct residues mod
m, so equal-weight monomials reduce to the same a^ℓ A; `toricKer_le_ideal_of_mono_sub_mem`
gives J = I.

## Family.Apery
Weights of (A) are exactly Ap(S; m); |Ap| = m; (J, a) = (I, a); the quotient
K[a..e]/(J, a) has dimension m (construct the basis before using finrank).

## Family.Minimality (nonredundancy, not indispensability)
* H: the two quadratics are independent; the 2k degree-k relations have pairwise disjoint
  supports modulo (a, c², bd).
* N: the N-degrees form an interval of width 2k − 1 < m; the monomial map
  ψ: (a,b,c,d,e) ↦ (s, st, stᵏ, st^{2k−1}, st^{2k}) kills H and ψ(N_r) = s^{q+1} tʳ (tᵐ − s) ≠ 0.
* q ≥ k: every H-degree is below D. q = k − 1: the only collisions are b e^{k−1} − c d^{k−1}
  at D and dᵏ − c e^{k−1} at D + k − 1; only a scalar multiple of the matching N_r can enter,
  and ψ forces it to vanish.
* Counterexample to indispensability: N₀ + e^{q−k+1}(b e^{k−1} − c d^{k−1}) = b eᵍ − a^{q+2}.

## GradedGenerators.spanRank_eq_card_of_weightedHomogeneous_irredundant
For positive weights, a weighted-homogeneous nonredundant generating set of I has cardinality
spanRank I: its classes span and are independent in I/𝔪I, and every generating set spans I/𝔪I.
(Do not apply a local-ring Nakayama theorem to the polynomial ring.)

## Decomposition (for W; `Decomposition.lean`)
Singleton components (support of size 1) total exactly 5 over contributing degrees; t_d ≤ 2;
β₁ + p = 5 + N, p ≤ 2; the bound β₁ ≤ 2w + 2 ⇔ N ≤ 2w − 3 + p; support types 2+2+unused (15),
2+3 (10), 1+2+2 (15). The four-generator `sigma_le_four` / `ncomp_sub_one_le` do not extend
(⟨13,14,16,18,19⟩ has σ = 8). Pair-component antichain lemma holds in every embedding dimension.
