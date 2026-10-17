# Correspondence: informal statements ↔ formal statements (2026-10-16)

Status (commit of record b0a3671; Lean sources at 0a2a156 differ only in Solution.lean comments):
Theorem F is a sorry-free Lean development, kernel-replayed locally (literal 23-module `leanchecker`
replay at 0a2a156, §11). Astra reviewer pass 1 on the formal development (2026-10-17):
ACCEPT_WITH_FIXES 0.98; the reviewer judges that F qualifies for FORMALLY_VERIFIED under aiseminar
AGENTS.md §3; lab status (aiseminar claim_0005, 2026-10-17): FORMALLY_VERIFIED for Theorem F
with the scope of §2. Independent statement reconstruction: done, equivalence with
`family_spanRank_eq` checked in Lean (§13). Linux CI comparator: passed at 10d4722 (2026-10-17,
https://github.com/benkeene/five-generator-betti/actions/runs/39005390724; con-ron, nanoda and
the Lean default kernel accepted the solution; §11). Theorem W is admitted
(`Targets/FiniteWidth.lean`, outside Solution's import closure and not in `defaultTargets`).
Adversary passes on the formal development ('meaning', 'trust', 2026-10-16): ACCEPT_WITH_FIXES 0.97;
their documentation fixes are applied here; the reviewer pass-1 documentation fixes are applied in the
commit following 0a2a156. Packaging commit of 2026-10-17 (after 10d4722): two further statements of
record for F, `familyGens_minimallyGenerates` and `family_presentation` (§2, §4, §8), added to
`comparator.json`; the frozen-file headers and docstrings were corrected (comment-only, §2); the
vendored four-generator copy was removed (docs/PORTING.md). The CI comparator has not yet run on that
commit. Commands and outcomes are in §11.

## 1. Informal claims and status
* **F** (informal: VERIFIED as an ordinary theorem, aiseminar claim_0005; formal: sorry-free,
  kernel-replayed locally, reviewer pass 1 ACCEPT_WITH_FIXES 0.98; CI comparator passed at
  10d4722, 2026-10-17): for every field K, k ≥ 3, q ≥ k − 1, m = 2kq + 1, the toric ideal of
  ⟨m, m+1, m+k, m+2k−1, m+2k⟩ has minimal number of generators 4k + 2.
* **W** (conjecture): β₁ ≤ 2w + 2 for every minimally five-generated numerical semigroup of
  width 4 ≤ w ≤ 40. Out of version 1.
Claim packet: `~/aiseminar/agents/shared/claim_0005/`.

## 2. Statements of record
`Challenge.lean`, for F (all three in `comparator.json` since the 2026-10-17 packaging commit):
* `FiveGenBetti.family_spanRank_eq`: `(toricIdeal K (familyGens k q)).spanRank = 4k + 2`;
* `FiveGenBetti.familyGens_minimallyGenerates`: `MinimallyGenerates (familyGens k q)` (no generator
  lies in the additive closure of the other four), so `spanRank` is `β₁` of a minimally
  five-generated numerical semigroup of width `2k` (strict monotonicity and `gcd = 1` are
  `Family.gens_strictMono`, `Family.gens_gcd` in the development);
* `FiveGenBetti.family_presentation`: `Ideal.span (Set.range (familyRelation K k q)) = toricIdeal K
  (familyGens k q)`, every `familyRelation K k q i` is outside the span of the others, and
  `Fintype.card (FamilyRelIndex k) = 4k + 2`. `FamilyRelIndex`, `familyRelExp`, `familyRelation` are
  restated in `Challenge.lean` with Mathlib-only imports (`![…]` vectors, `MvPolynomial.monomial`);
  `Solution.lean` proves `familyRelation K k q = Family.relation K k q` by `funext` and case
  analysis (`fin_cases` on the four initial `H` indices, `rfl` elsewhere) and then calls
  `Family.familyIdeal_eq_toricKer`, `Family.relation_nonredundant`, `Family.relIndex_card`.
For W: `FiveGenBetti.beta1_five_le_two_width_add_two`. W's admitted development statement is
`FiveGenBetti.Targets.beta1_five_le_two_width_add_two` (outside Solution's import closure;
`comparator.all-targets.json` must fail until proved).
Frozen-file text, corrected 2026-10-17 (comment-only; the comparator compares elaborated
statements, and comment-only edits to `Solution.lean` had already passed it at 10d4722): the
module headers no longer say PROOF_ATTEMPT or "formal review pending", and the docstrings of
`familyGens` and Theorem F no longer call the family "extremal" (F proves attainment of 2w + 2
only; extremality among all minimally five-generated semigroups is the conjecture W). All
definitions and the two original theorem statements are unchanged (§11).

## 3. Generator indexing and natural subtraction
`familyGens k q` matches on `i.val`; the wildcard is index 4 (domain `Fin 5`); `m + (2*k - 1)` is
the intended `m + 2k − 1` under `3 ≤ k`. In the relations, exponents are written `q + 1 + r - k`
(never `q - k + 1 + r`, off by one at q = k − 1) and N is indexed by `Fin k ⊕ Fin k`.

## 4. Hypotheses of W
positivity, `StrictMono n` (so `n 0` is the multiplicity and `n 4 - n 0` does not truncate),
`Finset.univ.gcd n = 1` (numerical), `MinimallyGenerates n` (no generator in the additive
closure of the others; prove the equivalence with "no expression using the others", both ways).
For the family: strict monotonicity (`Family.gens_strictMono`), gcd 1 (`Family.gens_gcd`), minimality
from n₄ < 2n₀: `Family.gens_minimallyGenerates` (`Family/MinimalGeneration.lean`, 2026-10-17; every
element of the closure of the other generators is `0`, one of those generators, or at least `2m`, and
`m + 2k < 2m` once `q ≥ 1`), public statement of record `familyGens_minimallyGenerates`. F does not
depend on it. The 'meaning' adversary had checked it with an ad-hoc Lean `example` (transcript
20261016T234404_adversary-meaning, accepted, exit 0); the former packaging gap is closed.

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
| the five generators are minimal (m + 2k < 2m) | `Family.gens_minimallyGenerates`; public `familyGens_minimallyGenerates` (Solution) |
| explicit presentation: generation, nonredundancy, count 4k + 2 | public `family_presentation` (Solution), from `familyIdeal_eq_toricKer`, `relation_nonredundant`, `relIndex_card` |

Scope of the statements of record: until the 2026-10-17 packaging commit, `Challenge.lean` and
`comparator.json` froze only the invariant μ(I) = 4k + 2 (the comparator pass at 10d4722 covers that
statement alone). Since then the displayed presentation (generation, nonredundancy, count) and
minimal generation are statements of record as well (§2), as suggested by both adversaries and the
reviewer. `Examples/Thirteen.lean` is a specialisation of F at (k,q) = (3,2), not an independent
check; its `decide` facts check finite arithmetic only.

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
| 2026-10-16 (corrected 2026-10-17) | `git diff --stat 2869b0b b0a3671 -- FiveGenBetti/Defs.lean FiveGenBetti/Interface.lean FiveGenBetti/Certificate/Defs.lean FiveGenBetti/Family/Data.lean FiveGenBetti/Family/Defs.lean Challenge.lean Solution.lean` | b0a3671 | `FiveGenBetti/Family/Defs.lean \| 10 ++++++++--` only: the two `sorry` bodies of `gens_strictMono`, `gens_gcd` replaced by proofs (02409bc); all definitions and theorem signatures unchanged. (The earlier entry "byte-identical" was false.) |
| 2026-10-17 | same, `git diff --stat 2869b0b HEAD -- <same 7 files>` | 0a2a156 | `Family/Defs.lean \| 10 ++++++++--`, `Solution.lean \| 14 ++++++++------`; the Solution.lean changes (956ab8d, 0a2a156 = amended 2b736c9) are comment-only (module docstrings) |
| 2026-10-16 (historical, imprecise) | `lake env leanchecker <descriptive placeholder: "all 22 built modules: Challenge, Solution, FiveGenBetti.*">`; literal argv not retained, so whether the umbrella `FiveGenBetti` was included is unknown (there are 23 built modules) | b0a3671 | exit 0, 13 min 19 s wall; superseded by the literal replay below |
| 2026-10-17 | `lake build` (before the replay) | 0a2a156 | exit 0, 8984 jobs |
| 2026-10-17 | `lake env leanchecker FiveGenBetti Challenge Solution FiveGenBetti.Algebra FiveGenBetti.Bridge FiveGenBetti.Certificate.Defs FiveGenBetti.Defs FiveGenBetti.Examples.Thirteen FiveGenBetti.Family.Apery FiveGenBetti.Family.Data FiveGenBetti.Family.Defs FiveGenBetti.Family.Generation FiveGenBetti.Family.Lemmas FiveGenBetti.Family.Main FiveGenBetti.Family.Minimality FiveGenBetti.Family.NormalForms FiveGenBetti.Family.Relations FiveGenBetti.Fiber FiveGenBetti.Graded.Indecomposables FiveGenBetti.Graded.Projection FiveGenBetti.GradedGenerators FiveGenBetti.Interface FiveGenBetti.Main` (23 modules: every module with an `.olean` under `.lake/build/lib/lean`, i.e. the umbrella `FiveGenBetti`, `Challenge`, `Solution` and the 20 `FiveGenBetti.*` descendants; `FiveGenBetti.AxiomAudit` has no olean and `Targets.FiniteWidth` is not built; list computed by a shell loop over the oleans) | 0a2a156 (Lean sources = b0a3671 except Solution.lean comments) | exit 0, 569 s wall (9 min 29 s; `/usr/bin/time -l`: 570.16 s real, max RSS 29.5 GB), no output. Two earlier attempts of the identical command the same morning were killed by SIGKILL (rc 137, after 425 s and 418 s, no output; the first concurrently with other Lean processes; cause not established, likely memory pressure) and are not counted as replays |
| 2026-10-17 | Linux comparator `scripts/verify-comparator.sh` with bundled NanoDa / con-ron (GitHub Actions, bubblewrap; job "Check statement against solution", run https://github.com/benkeene/five-generator-betti/actions/runs/39005390724; all four jobs success) | 10d4722 (Lean sources = b0a3671 except Solution.lean comments) | build 8981 jobs; `FiveGenBetti.family_spanRank_eq` plus `propext`, `Quot.sound`, `Classical.choice` exported; con-ron accepted 22291 declarations (`--verified`), nanoda accepted, Lean default kernel accepted; `Your solution is okay!` |
| 2026-10-17 | `git diff --stat 2869b0b -- <same 7 frozen files>` after the packaging edits (working tree) | packaging commit | `Challenge.lean \| 74 +++…`, `Family/Defs.lean \| 10` (as before), `Solution.lean \| 90 +++…`: Challenge/Solution gain the definitions `FamilyRelIndex`, `familyRelExp`, `familyRelation`, the theorems `familyGens_minimallyGenerates`, `family_presentation`, three Mathlib imports (`Data.Finsupp.Defs`, `Data.Fintype.Sum`, `RingTheory.Ideal.Span`) and comment edits; `toricIdeal`, `familyGens`, `MinimallyGenerates`, `family_spanRank_eq`, `beta1_five_le_two_width_add_two` unchanged |
| 2026-10-17 | `lake env lean Challenge.lean` | packaging commit | exit 0; `declaration uses sorry` at the four deliberate admissions only (lines 109, 114, 121, 130) |
| 2026-10-17 | `lake build` (default targets, with the new module `FiveGenBetti.Family.MinimalGeneration`) | packaging commit | exit 0, 8985 jobs; `declaration uses sorry` only for the four Challenge admissions |
| 2026-10-17 | `lake env lean FiveGenBetti/AxiomAudit.lean` (now prints `family_spanRank_eq`, `familyGens_minimallyGenerates`, `family_presentation`) | packaging commit | `[propext, Classical.choice, Quot.sound]` for each of the three |
| 2026-10-17 | `python3 scripts/check-lean-sources.py`; `ruby scripts/validate-formalization.rb` | packaging commit | both pass |
| 2026-10-17 | `lake env leanchecker Challenge Solution FiveGenBetti.Family.MinimalGeneration FiveGenBetti` (the modules changed or added by the packaging edits; the other 19 `FiveGenBetti.*` modules are byte-identical to 0a2a156 and covered by the 23-module replay above) | packaging commit | exit 0, 560 s wall (`/usr/bin/time -l`: 559.82 s real, max RSS 27.1 GB), no output |
| — | Linux CI comparator on the packaging commit (three theorem names) | — | PENDING (passed at 10d4722 for `family_spanRank_eq` alone) |
| — | `leanchecker --fresh` (optional) | — | NOT RUN |

Commit anchoring: e1554c4 differs from b0a3671 only in `FiveGenBetti/NOTES.md`; all Lean sources
are identical. The nine Minimality proofs were produced by GPT-6 Astra (job
five-generator-betti/20261016T233235, aiseminar `agents/runs/2026-10-16_betti-B5-minimality/reply_r1.md`)
and applied mechanically. Negative control recorded by the 'trust' adversary: under `import Challenge`
the same axiom query reports `sorryAx` and `leanchecker Challenge` still exits 0, so replay exit codes
alone do not exclude admissions; the axiom list is checked separately. Adversary-reported and
independently re-run by the reviewer (pass 1, 2026-10-17, at 4c9349b; not re-run by the orchestrator):
`lake env leanexport Solution -- FiveGenBetti.family_spanRank_eq | lake env leanchecker --from-export
/dev/stdin`, EXPORT_EXIT 0, CHECKER_EXIT 0, 17.55 s (Lean's default kernel, empty environment; not an
external kernel).

## 12. Source provenance
Template PALOMAR-2026-10-07-000005 at commit aa266b8a7db2794e49a0053978852ade100d23da;
reused files listed in docs/PORTING.md.

## 13. Independent statement reconstruction, 2026-10-17
GPT-6 Astra (role statement-recon, no access to this repository; aiseminar
`agents/astra/transcripts/20261017T000811_statement-recon_claim_0005.md`, CONFIDENCE 0.97) wrote a
Lean statement of F from CLAIM.md alone: `TheoremFStatement.F` (verbatim in the input below; it did
not elaborate it, Mathlib being absent in its sandbox). Item-by-item comparison with
`FiveGenBetti.family_spanRank_eq` (Challenge.lean / Solution.lean):

| item | reconstruction | statement of record | verdict |
|---|---|---|---|
| generators | `exponents k q = ![m, m+1, m+k, m+(2*k-1), m+2*k]`, `m = 2*k*q+1` | `familyGens k q`, match on `i.val`, wildcard = index 4 | identical (`funext i; fin_cases i <;> rfl`) |
| hypotheses | `k q : ℕ`, `3 ≤ k`, `k - 1 ≤ q` | `k q : ℕ`, `hk : 3 ≤ k`, `hq : k - 1 ≤ q` | identical |
| field | `∀ (K : Type u) [Field K]` | `(K : Type*) [Field K]` | identical (universe-polymorphic, any characteristic) |
| ideal | `RingHom.ker (MvPolynomial.aeval (fun i => (X : K[X]) ^ exponents k q i)).toRingHom` in `MvPolynomial (Fin 5) K`, codomain `Polynomial K` | `toricIdeal K n = RingHom.ker (MvPolynomial.aeval (fun i => (Polynomial.X : Polynomial K) ^ n i)).toRingHom`, codomain `Polynomial K` | identical after rewriting the exponent vector |
| minimal number of generators | `HasMinimalNumberOfGenerators I n`: some `Finset` of card `n` spans `I`, and every spanning `Finset` has card `≥ n` | `I.spanRank = (n : Cardinal)`, `Submodule.spanRank` over the scalar ring `MvPolynomial (Fin 5) K` | equivalent for natural `n` (argument below) |

Equivalence argument. `spanRank I` is the infimum of `#s` over all sets `s` with `span s = I`, and it
is attained (`Submodule.exists_span_set_card_eq_spanRank`). If `spanRank I = n` with `n : ℕ`, the
attaining set has cardinal `n < ℵ₀`, hence is finite, hence is (the coercion of) a `Finset` of card
`n`; conversely every spanning `Finset G` satisfies `spanRank I ≤ #G = G.card`
(`Submodule.spanRank_span_le_card`), so `n ≤ G.card`. (The converse implication also holds: a
spanning Finset of card `n` gives `spanRank I ≤ n`, and an attaining set of smaller cardinal would be a
spanning Finset of card `< n`. It is not needed here and was not checked in Lean.)

Lean check (direction: statement of record ⇒ reconstruction, which is the direction that matters
for trusting the formal statement). Run at 0a2a156 from the repository root, the scratch file not
added to the repository: `lake env lean --stdin < recon_equiv.lean` (SHA-256 of input
`480ff7cca25003bc2333496817087336887255610684c86978a6d7ec9724220f`). Input:

```lean
import Solution

universe u

namespace TheoremFStatement

def exponents (k q : ℕ) : Fin 5 → ℕ :=
  let m := 2 * k * q + 1
  ![m, m + 1, m + k, m + (2 * k - 1), m + 2 * k]

noncomputable def toricMap (K : Type u) [Field K] (k q : ℕ) :
    MvPolynomial (Fin 5) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval
    (fun i => (Polynomial.X : Polynomial K) ^ exponents k q i)

noncomputable def toricIdeal (K : Type u) [Field K] (k q : ℕ) :
    Ideal (MvPolynomial (Fin 5) K) :=
  RingHom.ker (toricMap K k q).toRingHom

def HasMinimalNumberOfGenerators {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) : Prop :=
  (∃ G : Finset R, Ideal.span (↑G : Set R) = I ∧ G.card = n) ∧
  (∀ G : Finset R, Ideal.span (↑G : Set R) = I → n ≤ G.card)

-- The proposition being formalized; no proof is supplied.
def F : Prop :=
  ∀ (K : Type u) [Field K] (k q : ℕ),
    3 ≤ k → k - 1 ≤ q →
    HasMinimalNumberOfGenerators (toricIdeal K k q) (4 * k + 2)

end TheoremFStatement

open Cardinal in
/-- Generic: a cardinal `spanRank` equal to a natural `n` gives the Finset formulation. -/
theorem hasMinimal_of_spanRank_eq {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (h : I.spanRank = (n : Cardinal)) : TheoremFStatement.HasMinimalNumberOfGenerators I n := by
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hs, hspan⟩ := Submodule.exists_span_set_card_eq_spanRank I
    rw [h] at hs
    have hfin : s.Finite :=
      Cardinal.lt_aleph0_iff_set_finite.mp (hs ▸ Cardinal.natCast_lt_aleph0 (n := n))
    obtain ⟨G, rfl⟩ := Set.Finite.exists_finset_coe hfin
    refine ⟨G, hspan, ?_⟩
    have h1 : (#(↑G : Set R)) = (G.card : Cardinal) := by simp
    rw [hs] at h1
    exact_mod_cast h1.symm
  · intro G hG
    have h2 := Submodule.spanRank_span_le_card (R := R) (↑G : Set R)
    have h3 : Submodule.span R (↑G : Set R) = I := hG
    have h4 : (#(↑G : Set R)) = (G.card : Cardinal) := by simp
    rw [h3, h, h4] at h2
    exact_mod_cast h2

theorem toricIdeal_eq (K : Type u) [Field K] (k q : ℕ) :
    TheoremFStatement.toricIdeal K k q =
      FiveGenBetti.toricIdeal K (FiveGenBetti.familyGens k q) := by
  have he : TheoremFStatement.exponents k q = FiveGenBetti.familyGens k q := by
    funext i; fin_cases i <;> rfl
  unfold TheoremFStatement.toricIdeal TheoremFStatement.toricMap FiveGenBetti.toricIdeal
  rw [he]

example (K : Type u) [Field K] (k q : ℕ) (hk : 3 ≤ k) (hq : k - 1 ≤ q) :
    TheoremFStatement.HasMinimalNumberOfGenerators
      (TheoremFStatement.toricIdeal K k q) (4*k+2) := by
  rw [toricIdeal_eq]
  exact hasMinimal_of_spanRank_eq _ _ (FiveGenBetti.family_spanRank_eq K k q hk hq)

theorem F_holds : TheoremFStatement.F := by
  intro K _ k q hk hq
  rw [toricIdeal_eq]
  exact hasMinimal_of_spanRank_eq _ _ (FiveGenBetti.family_spanRank_eq K k q hk hq)

#print axioms F_holds
```

Output (complete stdout/stderr) and exit code:

```
'F_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
LEAN_EXIT 0
```

Outcome: success. The `example` requested
(`HasMinimalNumberOfGenerators (TheoremFStatement.toricIdeal K k q) (4*k+2)` from `3 ≤ k`, `k - 1 ≤ q`)
and the full proposition `TheoremFStatement.F` are proved from `FiveGenBetti.family_spanRank_eq`, with
axioms `[propext, Classical.choice, Quot.sound]`. The reconstruction's own definitions are pasted
unchanged (only `import Mathlib` replaced by `import Solution`). Fresh elaboration against the built
oleans, not a kernel replay of the scratch file.
