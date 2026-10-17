# Brief: an executable Lean 4 formalization plan for Theorem F, split into two parallel streams

You are rooted read-only in `~/five-generator-betti`. Read, in this order: `README.md`,
`docs/PROOF.md` (the reviewed informal proof: Proof A, Proof B, the corrected decomposition
notes), `docs/astra/2026-10-16_scaffold_plan.md` (your earlier plan; its §5–§8 and §9 discharge
order), `Challenge.lean`, `Solution.lean`, every file under `FiveGenBetti/` and `Targets/`
(the current scaffold: definitions real, theorems admitted), `vendor/SemigroupBetti-aa266b8/`
(the complete four-generator Lean library you may port: `Defs.lean`, `Fiber.lean`, `Bridge.lean`,
`Critical.lean`, `Partition.lean`, `Antichain.lean`, `Identities.lean`, `Exceptional.lean`,
`Arith.lean`, `Main.lean`, `NOTES.md`), and the pinned Mathlib under `.lake/packages/mathlib`
(Lean v4.35.0-rc3, Mathlib c55e6e78) for exact lemma names. You can elaborate candidate
statements with `lake env lean --stdin` as you did before; do so for every signature you propose.

**Goal.** A plan that two Claude Opus 5.5 coding agents can execute *in parallel, without editing
the same files*, to prove `FiveGenBetti.family_spanRank_eq` with no `sorry`, no `native_decide`,
only `propext`/`Quot.sound`/`Classical.choice`, under the module system (`module`,
`public import`, `@[expose] public section`), with `lake build` green at every commit. Theorem W
stays out of scope. The reviewed proof's chosen route is Proof A (staged normal-form generation,
homogeneous-projection nonredundancy, the graded I/𝔪I cardinality lemma); Proof B's Gröbner route
is a fallback only.

**Deliverable: a document with these sections.**

0. **Dependency graph and file ownership.** The final file list under `FiveGenBetti/`, which
   stream (A or B) owns each file, and the import DAG. The two streams must be able to work for
   days without touching each other's files; shared definitions must be frozen in a file written
   FIRST (say exactly what goes into it, with full Lean text), after which neither stream edits it.
   Suggested split to evaluate: Stream A = generic infrastructure + bridges (GenData, fibers,
   factorization graphs, upper bridge μ(I) ≤ β_fiber ported from the vendored Bridge.lean, the
   graded cardinality lemma `spanRank_eq_card_of_weightedHomogeneous_irredundant`); Stream B =
   the family (generators, relations as MvPolynomial elements, membership in the kernel, normal
   forms, the offset bijection, the staged reduction and generation, Apéry, nonredundancy via
   projection and ψ, the boundary case). Say whether that split is right and where they meet
   (the exact statement each stream must deliver to the other).
1. **Frozen interface file(s).** Full Lean text (elaborated) of the shared definitions and the
   signatures of the handoff theorems, so both streams compile against the same interface from
   day one, with `sorry` bodies that each stream later replaces.
2. **Stream A work list**, in order: each declaration with its full signature, a proof sketch,
   the Mathlib lemmas it uses (exact names you verified in the pinned Mathlib), what to port from
   `vendor/SemigroupBetti-aa266b8` and how to generalize it (`Fin 4` → `Fin e`, `GenData` without
   offsets), an effort estimate, and a "done when" test (e.g. `#print axioms` of a lemma shows no
   sorryAx; a concrete instance checked by `decide`).
3. **Stream B work list**, the same shape. Include the natural-subtraction conventions
   (`q + 1 + r - k`, indexing N by `Fin k ⊕ Fin k`), the weight identities to prove for each
   relation, how to state the normal-form type and the offset equivalence
   `NormalForm k q ≃ Fin (2*k*q+1)` (residue-class table), the induction for
   `monomial_normal_form`, how to derive J = I from it using the coefficient-sum lemma from the
   vendored Bridge.lean, the Apéry statements, and the nonredundancy proof plan including
   `MvPolynomial.IsWeightedHomogeneous`, `weightedHomogeneousComponent`, the monomial map ψ as an
   `aeval`, and the q = k−1 collisions.
4. **Integration.** The final assembly in `Family/Main.lean` and `Solution.lean`, the
   `#print axioms` check, the comparator run, and the order in which sorries disappear so that
   `lake build` never breaks.
5. **Pitfalls** specific to this development (universe issues with `spanRank` as a Cardinal,
   `Finsupp` vs function exponents, `MvPolynomial` monomial API, decidability for the concrete
   instance, `Fin 5` case splits, linter settings in `lakefile.toml`), each with the workaround.
6. **Milestones and checks** for the two agents: what to commit after each milestone, what to
   benchmark (the ⟨13,14,16,18,19⟩ instance), and what to report back.

Be concrete enough that an agent can start typing from section 1. End with `CONFIDENCE: 0-1`
on the plan being executable as written, and how many subagents you used.
