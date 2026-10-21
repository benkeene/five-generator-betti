# TODO: address the Palomar review warning on PALOMAR-2026-10-17-000014 v1

Recorded 2026-10-21. Nothing has been fixed yet; no proof text has been changed.

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

- [ ] (a) Decide: rewrite the passage with the coefficient-and-divisibility argument, or label the quotient argument as an alternative informal proof.
- [ ] (b) Edit the file(s) identified above (at least `docs/PROOF.md` 64-79; then the warning notes in `README.md` and `formalization.yaml`).
- [ ] (c) Decide whether to resubmit as v2 or leave v1 as registered.
