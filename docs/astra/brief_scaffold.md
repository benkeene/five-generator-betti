# Brief: a step-by-step report for building the `five-generator-betti` Lean formalization repository

You are rooted (read-only) in `~/semigroup-betti`, Ben Keene's completed Palomar-registered
Lean 4 / Mathlib formalization of β₁ ≤ 2w for four-generated numerical semigroups. **It is both
the template and the library to reuse.** Read `README.md`, `Challenge.lean`, `Solution.lean`,
`formalization.yaml`, `comparator.json`, `CORRESPONDENCE.md`, `lakefile.toml`,
`lean-toolchain`, `lake-manifest.json`, `.github/workflows/ci.yml`, `scripts/`, and the whole
`SemigroupBetti/` library (`Defs.lean`, `Fiber.lean`, `Bridge.lean`, `Partition.lean`,
`Antichain.lean`, `Critical.lean`, `Exceptional.lean`, `Identities.lean`, `Arith.lean`,
`Main.lean`, `NOTES.md`). Note what is hardcoded to `Fin 4`. A compiled Mathlib for the pinned
toolchain (v4.35.0-rc3) exists in this repo's `.lake` (11 GB), so a new repo pinning the same
toolchain and Mathlib revision can reuse it.

**The new repository** is `~/five-generator-betti` (created today, empty apart from a README).
Its goal is a Palomar-compatible formalization of the five-generator results in the inlined
workflow reply (read the whole inlined file, especially §2 "Mathematics first" with the uniform
presentation and its adversarial check, the "corrected five-generator decomposition", §4
certificate/verifier spec, and §7 "Verification and Lean plan" with its port order):

- **Theorem F (family).** For every field K, k ≥ 3, q ≥ k − 1, m = 2kq + 1, the toric ideal of
  S = ⟨m, m+1, m+k, m+2k−1, m+2k⟩ has spanRank exactly 4k + 2, with the explicit minimal
  generating set (2k+2 ordinary-homogeneous binomials H and 2k binomials N) in the reply.
  Sub-results: the Apéry normal form (A) modulo a; (J,a) = (I,a) by the dimension count
  m = |Ap|; J = I by weighted-degree induction; minimality of H; indispensability of each N_r
  via the (s,t) monomial map; the boundary q = k − 1 collisions.
- **Decomposition lemma.** β₁ + p = 5 + N with p ≤ 2 (singleton counting), and the pair-support
  antichain lemma; the finite-width bound β₁ ≤ 2w + 2 is equivalent to N ≤ 2w − 3 + p.
- **Theorem W (finite width, later).** β₁ ≤ 2w + 2 for every minimally five-generated S with
  4 ≤ w ≤ 40, to be supported by a certified sweep (packed predecessor-tree certificates;
  checker soundness lemmas: Apéry correctness, candidate completeness, graph correspondence)
  — scaffold the statement and the checker-soundness lemmas now; the full computational theorem
  (periodicity + ~10⁸ instances) is explicitly out of scope for the first version.

Everything is PROOF_ATTEMPT (family) or conjecture (finite width).

**What the report must contain** (numbered steps Claude Code will execute in order; be concrete:
file names, declaration names, exact Lean statement drafts, commands):

1. **Repository layout and bootstrap.** Directory tree; `lakefile.toml`, toolchain and
   Mathlib pin strategy (reuse the template's pins and copy/symlink `.lake/packages/mathlib`, or
   `lake exe cache get`; exact commands, trade-offs); `formalization.yaml` for this project
   (classification arXiv math.AC/math.CO, MSC 13D02/20M14/13F65/05E40; status scope text);
   `comparator.json`; `LICENSE`; `CORRESPONDENCE.md` skeleton; CI; scripts to copy; and the
   **reuse strategy for `SemigroupBetti/`**: copy files and generalize `Fin 4` → `Fin 5` (or a
   generic `Fin e`), or depend on the template as a Lake package? Which files port unchanged,
   which need the five-generator cases (the 2+2+unused and 1+2+2 support types), which must not
   be ported (e.g. `sigma_le_four`), with per-file effort estimates.
2. **`Challenge.lean` draft.** Mathlib-only statements of record using the template's
   formulation (toric ideal as `RingHom.ker (MvPolynomial.aeval (fun i => X ^ n i))`,
   `Submodule.spanRank`): the family equality `spanRank = 4k + 2` quantified over k, q (define
   the generator function `n : Fin 5 → ℕ` explicitly), and the finite-width inequality with
   hypotheses (positivity, strict monotonicity, gcd = 1, minimality, 4 ≤ w ≤ 40). Write the Lean
   text. Say what is risky (the `AddSubmonoid.closure` minimality hypothesis, `Fin 5` indexing,
   `spanRank` vs the fiber invariant, universe/field generality) and how it will be checked in
   CORRESPONDENCE.md.
3. **Proof decomposition into a library** `FiveGenBetti/` (one file per lemma group, dependency
   order, Lean signatures where possible, strategy, difficulty): finite-generator infrastructure
   (factorizations, fibers, component supports, degree cutoff); the upper bridge
   μ(I) ≤ β_fiber (existing); the reverse bridge β_fiber ≤ μ(I) (needed for equality; the
   template did not formalize it — say how); singleton counting and β₁ + p = 5 + N; the antichain
   lemma; the family: the explicit binomials as `MvPolynomial` elements, membership in I,
   the spanning argument modulo a (terminating reduction), the Apéry count 2kq+1 = m, the
   dimension argument for (J,a) = (I,a), weighted-degree induction, minimality of H by disjoint
   supports in K[b,c,d,e]/(c²,bd), the monomial map argument for the N_r, the boundary case;
   certificate-checker soundness lemmas for Theorem W. Which parts to do by `decide` on concrete
   instances (e.g. ⟨13,14,16,18,19⟩) and how to keep that kernel-feasible (no `native_decide`).
4. **Scaffolding order.** What to `sorry` first so `lake build` passes on day one with the full
   statement chain present, and the order to discharge sorries so the first real theorem lands
   early (suggest: a kernel-checked concrete instance, then membership of the family binomials in
   I, then the Apéry count).
5. **Informal proof write-up.** `docs/PROOF.md` structure with lemma labels matching Lean names;
   the review protocol before Lean work on minimality starts (adversary → response → reviewer →
   independent reconstruction; claim packet in `~/aiseminar`); where the certified-sweep
   artifacts for Theorem W will live (not in the Lean checkout: Palomar's 500 MiB cap).
6. **Correspondence and verification.** CORRESPONDENCE.md argument, `#print axioms`, sorry/axiom
   grep, `leanchecker`, NanoDa, comparator, size limits.
7. **Risks and open questions** specific to the formalization (Mathlib commutative-algebra API
   for quotient dimension counts and weighted homogeneity, the reverse bridge, generalizing the
   template's `Fin 4` code, kernel cost of concrete instances), ranked, with what to try first.

Do not assume the informal proof is correct; where a step looks under-justified for
formalization, say so and propose the needed lemma. End with `CONFIDENCE: 0-1` on the plan
being executable as written, and state how many subagents you used.
