# TODO: address the Palomar review warning on PALOMAR-2026-10-17-000014 v1

Recorded 2026-10-21. Items (a) and (b) were done on 2026-10-21 on main (no Lean source changed); item (c) is open.

- Entry: PALOMAR-2026-10-17-000014 v1, pinning commit `65cd1b7289ed27ff6ffec32c5644a8b4323918d2`
  - Page: https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-17-000014&version=1
  - Entry JSON: https://data.palomar-registry.org/entries/PALOMAR-2026-10-17-000014-v1.json
- Review: https://data.palomar-registry.org/evidence/PALOMAR-2026-10-17-000014-v1/62de693e86b7da2712831d50739215e9b696571a72ba799f8e74a95d45af7486/review.json
  (fetched 2026-10-21; SHA-256 `608346bf460e92c089be94a240249881af65f1bca58ebae4942638ff077656d7`, which matches
  `review.report.sha256` in the entry JSON)

## Reviewer fields (verbatim from review.json)

- `outcome`: `neutral`; `requested_changes`: `[]`
- `reviewer_models`: `["codex:gpt-6-sol"]`
- `reviewed_at`: `2026-10-17T19:54:57Z`
- `policy_commit`: `96b034cc31a72a63d4f4041911dce337a85c9a04`
- `submission_id`: `at6sypr5fxsw`
- `summary`: "Mechanical verification passed, and the editorial checks found no blocking problem. The proof account has a disclosed, non-blocking mismatch with the Lean proof."
- The warning is the only finding. It sits in check `step: "proof_account"`, `outcome: "warning"`, `trust_level: "high"`, with summary:
  "The proof account largely tracks all three selected declarations, but it attributes the decisive H-only nonredundancy step to an argument different from the one formalized."

## Warning (verbatim)

> message: "The proof account misidentifies the decisive H-only nonredundancy argument used by Lean. Replace that passage with the coefficient-and-divisibility argument, or explicitly identify the quotient argument as an alternative informal proof rather than the architecture of the imported proof."
>
> evidence: "README.md points to docs/PROOF.md; docs/PROOF.md, under “Family.Minimality,” attributes H-only nonredundancy to a degree-k argument modulo (a, c², bd). FiveGenBetti/Family/Minimality.lean proves H_nonredundant by selecting a monomial coefficient and showing that neither monomial of any other H-relation divides it, with a separate choice for bd − ae."

## Where the passage is (line numbers as of the commit adding this file)

- **Primary target:** `docs/PROOF.md:64-79`, section "Family.Minimality". Lines 67-70 say layer (i) follows
  "the order of the Lean proof" and cite `H_nonredundant`; the bullet at lines 76-79 ("* H (layer (i) ...")
  gives the quotient argument modulo (a, c², bd).
- Lean proof being described: `FiveGenBetti/Family/Minimality.lean:230` (`theorem H_nonredundant`).
- `paper/main.tex:290` and `:305-309` give the same quotient argument as the paper's proof of the H lemma.
  `paper/main.tex:362` already says the Lean proof uses "a divisibility argument with witness monomials where
  the paper projects modulo (a,c^2,bd)", so the paper may need no change; check.
- `docs/astra/2026-10-16_lean_plan.md:639` (the Astra plan: coefficient selectors outside (a,c²,bd)) may help
  when writing the Lean-faithful version.
- Places that record the warning (update their wording once it is addressed):
  `README.md:73-76` and `formalization.yaml:155-157` ("not yet addressed").

## Checklist for Ben

- [x] (a) Decided 2026-10-21: rewrite the passage with the witness-monomial divisibility argument that `H_nonredundant`
      formalizes, and name the paper's quotient argument modulo (a, c², bd) as an alternative informal proof. The paper
      (`paper/main.tex:362`) already states the difference and was not changed.
- [x] (b) Done 2026-10-21: `docs/PROOF.md` section Family.Minimality, layer (i) and the H bullet, rewritten (the old
      sentence about projecting to the ordinary degree of f was removed because it did not identify the decisive
      coefficient-and-divisibility argument; the helper `homogeneous_mem_span_range` still performs that projection
      internally, but its degree-related conclusions are discarded); warning notes in `README.md` and
      `formalization.yaml` updated to "addressed on main, after the pinned commit". Adversarial review of the rewrite
      by GPT-6 Astra (`docs/astra/2026-10-21_adversary_proofmd_hrewrite.md`, ACCEPT_WITH_FIXES 0.97): its eight
      findings (scoping of the divisibility lemmas, the ae witness justification, the N bullet's signed degree, the
      assembly's actual case split, the paper's degree-2 case, the Apéry quotient-basis sentence, the record wording)
      were applied in the commit following aaae2b9.
- [ ] (c) Decide whether to resubmit as v2 or leave v1 as registered. Recommendation: submit v2 (the registry reads the
      proof account at the pinned commit, so v1 keeps the warning; Lean sources are unchanged, so mechanical verification
      should pass again; v2 also retires the stale "private" wording at 65cd1b7). If v2 is registered, update the
      bibtex and the entry links in `README.md` and `formalization.yaml`.
