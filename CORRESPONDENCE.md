# Correspondence: informal statements ↔ formal statements (2026-10-16)

Status (commit of record b0a3671): Theorem F is a sorry-free Lean development, kernel-replayed
locally (per module), pending reviewer pass, independent statement reconstruction, and CI
comparator. It is not yet "formally verified" under the aiseminar protocol. Theorem W is admitted
(`Targets/FiniteWidth.lean`, outside Solution's import closure and not in `defaultTargets`).
Adversary passes on the formal development ('meaning', 'trust', 2026-10-16): ACCEPT_WITH_FIXES 0.97;
their documentation fixes are applied here. Commands and outcomes are in §11.

## 1. Informal claims and status
* **F** (informal: VERIFIED as an ordinary theorem, aiseminar claim_0005; formal: sorry-free,
  kernel-replayed locally, reviewer/comparator pending): for every field K, k ≥ 3, q ≥ k − 1, m = 2kq + 1, the toric ideal of
  ⟨m, m+1, m+k, m+2k−1, m+2k⟩ has minimal number of generators 4k + 2.
* **W** (conjecture): β₁ ≤ 2w + 2 for every minimally five-generated numerical semigroup of
  width 4 ≤ w ≤ 40. Out of version 1.
Claim packet: `~/aiseminar/agents/shared/claim_0005/`.

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
For the family: strict monotonicity (`Family.gens_strictMono`), gcd 1 (`Family.gens_gcd`), minimality
from n₄ < 2n₀. Known gap (packaging): no named lemma `MinimallyGenerates (familyGens k q)` exists in
`Family/Defs.lean`; F does not depend on it. The 'meaning' adversary checked it with an ad-hoc Lean
`example` (transcript 20261016T234404_adversary-meaning, accepted, exit 0); whether to add it as a named
lemma is open.

## 5. Kernel ideal and fields
`toricIdeal K n = RingHom.ker (MvPolynomial.aeval (fun i => X ^ n i)).toRingHom`, `K : Type*`
any field, any characteristic.

## 6. spanRank
`Submodule.spanRank` is a cardinal; the natural-number right-hand sides are coerced.
Equality in F needs a lower bound on every generating set (graded lemma through I/mI,
`spanRank_eq_card_of_weightedHomogeneous_irredundant`), not just nonredundancy.

## 7. Bridges
Upper bridge μ(I) ≤ β_fiber: formalized (`GenData.spanRank_toricKer_le_beta1`, Bridge.lean, sorry-free).
Lower bridge β_fiber ≤ μ(I): not formalized, and not needed for F, which is stated directly for
`spanRank` and proved through the graded lower bound (`spanRank_eq_card_of_weightedHomogeneous_irredundant`)
applied to the explicit presentation. F therefore does not formally assert equality with `betaFiber`.

## 8. Family correspondence table
| informal | Lean (all proved, sorry-free at b0a3671) |
|---|---|
| relations H (2k+2), N (2k) | `Family.Relations` |
| normal forms (A), offsets partition {0..2kq} | `Family.NormalForms` |
| every monomial ≡ a^ℓ · normal form mod J; J = I | `Family.Generation`, `toricKer_le_ideal_of_mono_sub_mem` |
| Apéry set = weights of (A), |Ap| = m | `Family.Apery` |
| nonredundancy of H ∪ N (ψ(N_r) = s^{q+1} t^r (t^m − s)); boundary q = k − 1 | `Family.Minimality` |
| spanRank = 4k + 2 | `Family.spanRank_eq`; public `family_spanRank_eq` (Solution) |

Scope of the statement of record: `Challenge.lean` and `comparator.json` freeze only the invariant
μ(I) = 4k + 2. The displayed presentation (generation `familyIdeal_eq_toricKer`, nonredundancy
`relation_nonredundant`, count `relIndex_card`) is proved in the development but is not part of the
comparator contract (packaging suggestion from both adversaries: a presentation corollary of record;
open). `Examples/Thirteen.lean` is a specialisation of F at (k,q) = (3,2), not an independent check;
its `decide` facts check finite arithmetic only.

## 9. Certificate semantics
`AperyCertificate m`: parent generator index per residue; parent residue `(r + m − n_j % m) % m`;
reconstruction `A_0 = 0`, `A_r = A_{p(r)} + n_{j(r)}`; closure inequalities; candidate degrees
`{n_i + A_r}`; support graph on `{i : d − n_i ∈ S}` with edges `d − n_i − n_j ∈ S`, guards
`n i ≤ d`, `i ≠ j`, `n i + n j ≤ d`; the zero degree is excluded from the graph correspondence.

## 10. Exclusions
Formal periodicity, the complete width-40 replay, novelty, the reverse fiber bridge, Theorem W.

## 11. Build and audit record
| date | command | commit | outcome |
|---|---|---|---|
| 2026-10-16 | `lake build` | scaffold | success, 1577 jobs, sorry warnings only |
| 2026-10-16 | `lake build` | b0a3671 | exit 0, 8984 jobs; no `declaration uses sorry` in any module of Solution's import closure (only Challenge's deliberate admissions) |
| 2026-10-16 | `lake env lean FiveGenBetti/Family/Minimality.lean` | b0a3671 | 0 sorries, 0 errors |
| 2026-10-16 | `#print axioms` for `FiveGenBetti.family_spanRank_eq` (from Solution), `FiveGenBetti.Family.spanRank_eq`, `FiveGenBetti.Examples.thirteen_spanRank_eq_fourteen` | b0a3671 | [propext, Classical.choice, Quot.sound] each |
| 2026-10-16 | `#print axioms` for the nine Minimality declarations (`psi_H`, `psi_N`, `psi_N_ne_zero`, `H_nonredundant`, `N_nonredundant`, `H_degree_lt_D`, `H_boundary_collisions`, `H_degree_lt_D_add_m`, `relation_nonredundant`) | b0a3671 | [propext, Classical.choice, Quot.sound] each |
| 2026-10-16 | `lake env leanchecker FiveGenBetti.Family.Minimality FiveGenBetti.Family.Main FiveGenBetti.Examples.Thirteen Solution` | b0a3671 | exit 0 |
| 2026-10-16 | `lake env lean FiveGenBetti/AxiomAudit.lean` (informational; not run in CI; does not fail on extra axioms) | b0a3671 | prints only `[propext, Classical.choice, Quot.sound]` for `family_spanRank_eq` |
| 2026-10-16 | `python3 scripts/check-lean-sources.py` (headers, symlinks, sizes only) | b0a3671 | satisfied |
| 2026-10-16 | `ruby scripts/validate-formalization.rb` (metadata shape only, not status) | b0a3671 | passes |
| 2026-10-16 | forbidden-construct scan of the Minimality diff | b0a3671 | 0 findings |
| 2026-10-16 | frozen files (Defs, Interface, Certificate/Defs, Family/Data, Family/Defs, Challenge, Solution) vs bootstrap 2869b0b | b0a3671 | byte-identical |
| TODO(orchestrator): full-sweep row | `lake env leanchecker` over all 22 built modules | b0a3671 | RUNNING, outcome not yet recorded |
| — | Linux comparator (`scripts/verify-comparator.sh`, CI) | b0a3671 | NOT RUN |
| — | NanoDa / con-ron external kernels; `leanchecker --fresh` | b0a3671 | NOT RUN |

Commit anchoring: e1554c4 differs from b0a3671 only in `FiveGenBetti/NOTES.md`; all Lean sources
are identical. The nine Minimality proofs were produced by GPT-6 Astra (job
five-generator-betti/20261016T233235, aiseminar `agents/runs/2026-10-16_betti-B5-minimality/reply_r1.md`)
and applied mechanically. Negative control recorded by the 'trust' adversary: under `import Challenge`
the same axiom query reports `sorryAx` and `leanchecker Challenge` still exits 0, so replay exit codes
alone do not exclude admissions; the axiom list is checked separately. Adversary-reported (not yet
re-run by the orchestrator): `leanexport Solution -- FiveGenBetti.family_spanRank_eq | leanchecker
--from-export` accepted.

## 12. Source provenance
Template PALOMAR-2026-10-07-000005 at commit aa266b8a7db2794e49a0053978852ade100d23da;
reused files listed in docs/PORTING.md.
