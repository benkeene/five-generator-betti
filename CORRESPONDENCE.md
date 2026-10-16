# Correspondence: informal statements ↔ formal statements (scaffold, 2026-10-16)

Status: SCAFFOLD. Sections 11–12 are filled as checks are run.

## 1. Informal claims and status
* **F** (PROOF_ATTEMPT): for every field K, k ≥ 3, q ≥ k − 1, m = 2kq + 1, the toric ideal of
  ⟨m, m+1, m+k, m+2k−1, m+2k⟩ has minimal number of generators 4k + 2.
* **W** (conjecture): β₁ ≤ 2w + 2 for every minimally five-generated numerical semigroup of
  width 4 ≤ w ≤ 40. Out of version 1.
Claim packets: `~/aiseminar/agents/shared/` (to be created).

## 2. Statements of record
`Challenge.lean`: `FiveGenBetti.family_spanRank_eq`, `FiveGenBetti.beta1_five_le_two_width_add_two`.
`Solution.lean` restates the definitions and proves F via `FiveGenBetti.Family.spanRank_eq`.
W's admitted development statement is `FiveGenBetti.Targets.beta1_five_le_two_width_add_two`
(outside Solution's import closure; `comparator.all-targets.json` must fail until proved).

## 3. Generator indexing and natural subtraction
`familyGens k q` matches on `i.val`; the wildcard is index 4 (domain `Fin 5`); `m + (2*k - 1)` is
the intended `m + 2k − 1` under `3 ≤ k`. In the relations, exponents are written `q + 1 + r - k`
(never `q - k + 1 + r`, off by one at q = k − 1) and N is indexed by `Fin k ⊕ Fin k`.

## 4. Hypotheses of W
positivity, `StrictMono n` (so `n 0` is the multiplicity and `n 4 - n 0` does not truncate),
`Finset.univ.gcd n = 1` (numerical), `MinimallyGenerates n` (no generator in the additive
closure of the others; prove the equivalence with "no expression using the others", both ways).
For the family: strict monotonicity, gcd 1 (consecutive generators), minimality from n₄ < 2n₀.

## 5. Kernel ideal and fields
`toricIdeal K n = RingHom.ker (MvPolynomial.aeval (fun i => X ^ n i)).toRingHom`, `K : Type*`
any field, any characteristic.

## 6. spanRank
`Submodule.spanRank` is a cardinal; the natural-number right-hand sides are coerced.
Equality in F needs a lower bound on every generating set (graded lemma through I/mI,
`spanRank_eq_card_of_weightedHomogeneous_irredundant`), not just nonredundancy.

## 7. Bridges
Upper bridge μ(I) ≤ β_fiber: ported from the template. Lower bridge β_fiber ≤ μ(I): new
(component-charge map). Neither is formalized yet.

## 8. Family correspondence table
| informal | Lean (planned) |
|---|---|
| relations H (2k+2), N (2k) | `Family.Relations` |
| normal forms (A), offsets partition {0..2kq} | `Family.NormalForms` |
| every monomial ≡ a^ℓ · normal form mod J; J = I | `Family.Generation`, `toricKer_le_ideal_of_mono_sub_mem` |
| Apéry set = weights of (A), |Ap| = m | `Family.Apery` |
| nonredundancy of H ∪ N (ψ(N_r) = s^{q+1} t^r (t^m − s)); boundary q = k − 1 | `Family.Minimality` |
| spanRank = 4k + 2 | `Family.spanRank_eq` |

## 9. Certificate semantics
`AperyCertificate m`: parent generator index per residue; parent residue `(r + m − n_j % m) % m`;
reconstruction `A_0 = 0`, `A_r = A_{p(r)} + n_{j(r)}`; closure inequalities; candidate degrees
`{n_i + A_r}`; support graph on `{i : d − n_i ∈ S}` with edges `d − n_i − n_j ∈ S`, guards
`n i ≤ d`, `i ≠ j`, `n i + n j ≤ d`; the zero degree is excluded from the graph correspondence.

## 10. Exclusions
Formal periodicity, the complete width-40 replay, novelty.

## 11. Build and audit record
| date | command | commit | outcome |
|---|---|---|---|
| 2026-10-16 | `lake build` | scaffold | success, 1577 jobs, sorry warnings only |

## 12. Source provenance
Template PALOMAR-2026-10-07-000005 at commit aa266b8a7db2794e49a0053978852ade100d23da;
reused files listed in docs/PORTING.md.
