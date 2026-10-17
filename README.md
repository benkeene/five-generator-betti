# five-generator-betti

Lean 4 / Mathlib formalization of two statements about minimally
five-generated numerical semigroups S = ⟨n₀ < n₁ < n₂ < n₃ < n₄⟩ of width w = n₄ − n₀:

1. The family S(m,k) = ⟨m, m+1, m+k, m+2k−1, m+2k⟩ with m = 2kq + 1, k ≥ 3, q ≥ k − 1 has
   β₁(K[S]) = 4k + 2 (an explicit minimal presentation with 2k+2 homogeneous and 2k
   inhomogeneous binomials).
2. β₁(K[S]) ≤ 2w + 2 for every minimally five-generated S with 4 ≤ w ≤ 40 (finite-width
   statement, to be supported by a certified sweep over the periodicity window m ≤ w² + w).

Status: (1) VERIFIED as an ordinary theorem by the aiseminar review protocol (2026-10-16; four Astra
passes incl. an independent reconstruction). Its Lean development is a sorry-free Lean development,
kernel-replayed locally (literal 23-module `leanchecker` replay, `CORRESPONDENCE.md` §11). The Astra
reviewer pass 1 on the formal development (2026-10-17) returned ACCEPT_WITH_FIXES 0.98 and judged
that F qualifies for FORMALLY_VERIFIED under the lab's AGENTS.md §3; an independent statement
reconstruction was checked equivalent in Lean (`CORRESPONDENCE.md` §13). Lab status (aiseminar
claim_0005, 2026-10-17): FORMALLY_VERIFIED for Theorem F with the scope in `CORRESPONDENCE.md` §2.
CI comparator passed at 0223cfc (2026-10-17, GitHub Actions run
https://github.com/benkeene/five-generator-betti/actions/runs/39005390724): statement and axiom
check passed, and con-ron, nanoda and the Lean default kernel accepted the solution;
`leanchecker --fresh` has not been run (optional). Packaging additions of 2026-10-17 (after 0223cfc): two further
statements of record for F, `FiveGenBetti.familyGens_minimallyGenerates` (the five generators are a minimal generating
set) and `FiveGenBetti.family_presentation` (the explicit `4k+2` binomials generate the toric ideal, none is redundant,
and there are `4k+2` of them), both listed in `comparator.json` and proved in `Solution.lean` by thin calls into the
development; the CI comparator has not yet run on the commit containing them. `lake env lean FiveGenBetti/AxiomAudit.lean`
(from `Solution`) prints [propext, Classical.choice, Quot.sound] for each of the three statements. Adversary passes on the formal development ('meaning',
'trust', 2026-10-16): ACCEPT_WITH_FIXES 0.97, documentation fixes applied. (2) conjecture, admitted in
`Targets/FiniteWidth.lean` outside Solution's import closure. Informal argument in `docs/PROOF.md`;
plans in `docs/astra/`; audit record in `CORRESPONDENCE.md` §11. Template and reusable library: `~/semigroup-betti`
(Palomar entry PALOMAR-2026-10-07-000005; four-generator case β₁ ≤ 2w).

## Layout
- `Challenge.lean` — statements of record (Mathlib-only imports, deliberate `sorry`s): F as
  `family_spanRank_eq` (the invariant), `family_presentation` (the explicit presentation) and
  `familyGens_minimallyGenerates` (minimal generation); W as `beta1_five_le_two_width_add_two`.
- `Solution.lean` — restates the definitions and proves the three F statements by thin calls into
  `FiveGenBetti.Family` (`spanRank_eq`, `familyIdeal_eq_toricKer`, `relation_nonredundant`,
  `relIndex_card`, `gens_minimallyGenerates`); sorry-free. W is not restated: version 1 is family-only.
- `FiveGenBetti/` — Defs (generic `GenData e`, `toricKer`), Family/ (generators, relations,
  minimal generation, main theorem), Certificate/ (Apéry predecessor-tree certificates),
  Examples/Thirteen, `NOTES.md`, `AxiomAudit.lean`.
- `Targets/FiniteWidth.lean` — W, admitted, outside Solution's import closure;
  `comparator.json` (family only) and `comparator.all-targets.json` (both; must fail until W is proved).
- `docs/PROOF.md` (labelled informal proof of F; lab status VERIFIED as an ordinary theorem), `docs/PORTING.md`,
  `docs/CHECKER.md`, `docs/astra/`, `CORRESPONDENCE.md`.
- `paper/` — LaTeX write-up of Theorem F (`main.tex`, `refs.bib`; build outputs are ignored).

## Building and checking

```
lake exe cache get      # on a clean machine; locally .lake/packages is cloned from ~/semigroup-betti
lake build
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
lake env lean FiveGenBetti/AxiomAudit.lean   # informational only (not run in CI): expect propext, Classical.choice, Quot.sound for all three statements
./scripts/verify-comparator.sh          # Linux with bubblewrap only; passed in CI at 0223cfc
```

Pinned toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib `v4.35.0-rc3`
(`c55e6e786f49471c72fbddbec5415808896aec1e`), the same as PALOMAR-2026-10-07-000005. Never commit `.lake`.

## Submission
Palomar submissions go through https://submit.palomar-registry.org/ with the full 40-character commit SHA. This repository is
ready for submission from the registry's side once the CI comparator passes on the commit to be
submitted: it passed at 0223cfc (2026-10-17,
https://github.com/benkeene/five-generator-betti/actions/runs/39005390724; con-ron, nanoda
and the Lean default kernel accepted the solution) for `family_spanRank_eq` alone, and the
2026-10-17 packaging commit adds `familyGens_minimallyGenerates` and `family_presentation` to
`comparator.json` (local build, axiom audit and replay recorded in `CORRESPONDENCE.md` §11; CI
pending). Remaining before submitting, the owner's decisions: repository visibility (currently
private; the registry must be able to clone) and a human read of `CORRESPONDENCE.md`.
`leanchecker --fresh` has not run (optional; the registry's comparator performs independent
replay). See `status.scope` in `formalization.yaml` and `CORRESPONDENCE.md` §11.
