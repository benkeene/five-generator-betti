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
`leanchecker --fresh` has not been run (optional). The CI comparator then passed with all three statements of record on the rewritten main 0a897c8 (2026-10-17, run 39036226197: con-ron accepted 22338 declarations with --verified, nanoda and the Lean default kernel accepted; "Your solution is okay!"). Packaging additions of 2026-10-17 (after 0223cfc): two further
statements of record for F, `FiveGenBetti.familyGens_minimallyGenerates` (the five generators are a minimal generating
set) and `FiveGenBetti.family_presentation` (the explicit `4k+2` binomials generate the toric ideal, none is redundant,
and there are `4k+2` of them), both listed in `comparator.json` and proved in `Solution.lean` by thin calls into the
development; the CI comparator passed with all three on the rewritten main `0a897c8` (run 39036226197). `lake env lean FiveGenBetti/AxiomAudit.lean`
(from `Solution`) prints [propext, Classical.choice, Quot.sound] for each of the three statements. Adversary passes on the formal development ('meaning',
'trust', 2026-10-16): ACCEPT_WITH_FIXES 0.97, documentation fixes applied. (2) conjecture, admitted in
`Targets/FiniteWidth.lean` outside Solution's import closure. Informal argument in `docs/PROOF.md`;
plans in `docs/astra/`; audit record in `CORRESPONDENCE.md` §11. Template and reusable library: `~/semigroup-betti`
(Palomar entry PALOMAR-2026-10-07-000005; four-generator case β₁ ≤ 2w).
Registered on Palomar as PALOMAR-2026-10-17-000014 v1 (2026-10-17; see below).

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

## Palomar entry and citation
This formalization is hosted on Palomar as
[PALOMAR-2026-10-17-000014 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-17-000014&version=1).
Version 1 pins commit `65cd1b7289ed27ff6ffec32c5644a8b4323918d2` (the main head when it was submitted; the
README and `formalization.yaml` at that commit still describe the repository as private, which it
was until submission). Palomar's mechanical verification (https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/39043271825) checked the three
statements of record with Comparator, nanoda and con-ron; the pinned commit is preserved in
https://github.com/PalomarArchive/benkeene--five-generator-betti--724a4e2a049a. Registry review outcome `neutral`
(by Palomar's policy not an acceptance or endorsement), with one warning: "The proof account misidentifies the decisive
H-only nonredundancy argument used by Lean. Replace that passage with the coefficient-and-divisibility argument, or
explicitly identify the quotient argument as an alternative informal proof rather than the architecture of the
imported proof." Addressed on main on 2026-10-21 (after the pinned commit) by rewriting the H-only
nonredundancy passage of `docs/PROOF.md` (section Family.Minimality, layer (i)) to the witness-monomial
divisibility argument that `H_nonredundant` formalizes, with the paper's quotient argument modulo (a, c², bd)
identified as an alternative informal proof; no Lean source changed. The registered v1 still shows the
warning until a new version is submitted. Registration is not a review of novelty: no novelty claim is made. Theorem W is not part of the entry.
To cite it:
```bibtex
@misc{palomar-2026-10-17-000014-v1,
  author = {{Ben Keene}},
  title = {{First Betti numbers of five-generated numerical semigroups}},
  year = {2026},
  howpublished = {Palomar, PALOMAR-2026-10-17-000014 v1},
  url = {https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-17-000014&version=1},
}
```

## Submission
Palomar submissions (including new versions of this entry) go through https://submit.palomar-registry.org/ with the
full 40-character commit SHA. Before the submission the CI comparator passed with all three statements
of record (`family_spanRank_eq`, `familyGens_minimallyGenerates`, `family_presentation`) on the
rewritten main `0a897c8` (2026-10-17,
https://github.com/benkeene/five-generator-betti/actions/runs/39036226197; con-ron, nanoda and
the Lean default kernel accepted the solution), after an earlier pass at 0223cfc for
`family_spanRank_eq` alone. Ben Keene read `CORRESPONDENCE.md` in full on 2026-10-17.
`leanchecker --fresh` has not run (optional). Commits on main after `65cd1b7` are not part of version 1.
See `status.scope` in `formalization.yaml` and `CORRESPONDENCE.md` §11.
