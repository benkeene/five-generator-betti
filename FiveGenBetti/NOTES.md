# Development notes

Plan of record: `docs/astra/2026-10-16_lean_plan.md` (§0 ownership and DAG, §1 frozen interfaces,
§2 stream A, §3 stream B, §4 integration). State: **Bootstrap** milestone — every planned module
exists, all real definitions are in place, all handoff signatures are frozen, the final assembly of
Theorem F is real proof text, and the tree builds. A green build with admitted dependencies is not
evidence that F is proved: `lake env lean FiveGenBetti/AxiomAudit.lean` still reports `sorryAx`.

Rules: definitions frozen byte-for-byte; theorem *signatures* frozen, bodies edited only by their
owner (A or B) in their owner's files; no theorem relocation after bootstrap.

Status: **def** = genuine definition; **proved** = real proof body (may still depend on admitted
lemmas); **stub** = `sorry` body; **frozen** = shared interface, not to be edited.

## Shared / frozen

| declaration | file | owner | status |
|---|---|---|---|
| `toricKer`, `GenData`, `GenData.nu`, `GenData.fiber`, `GenData.cutoff` | Defs.lean | frozen | def |
| `mono`, `weight` | Interface.lean | frozen | def |
| `Certificate.AperyCertificate` | Certificate/Defs.lean | frozen | def |

## Stream A

All Stream A files are sorry-free (A1–A5); every handoff's `#print axioms` is
`[propext, Classical.choice, Quot.sound]`.

| declaration | file | owner | status |
|---|---|---|---|
| `toricMap` | Algebra.lean | A | def |
| `mono_coe` | Algebra.lean | A | proved |
| `toricMap_monomial` | Algebra.lean | A | proved (sorry-free) |
| `toricMap_mono` | Algebra.lean | A | proved (sorry-free) |
| `mem_toricKer` | Algebra.lean | A | proved |
| `mono_sub_mem_toricKer` | Algebra.lean | A | proved (sorry-free) |
| `coeff_sum_eq_zero` | Algebra.lean | A | proved (sorry-free) |
| `toricKer_le_ideal_of_mono_sub_mem` (handoff to B) | Algebra.lean | A | proved (sorry-free) |
| `SharesVar`, its `DecidableRel` instance | Fiber.lean | A | def |
| `SharesVar.symm` | Fiber.lean | A | proved |
| `GenData.nabla`, `ncomp`, `contributes`, `betaFiber` (+ decidability instances) | Fiber.lean | A | def |
| `GenData.mem_fiber` | Fiber.lean | A | proved (sorry-free) |
| `GenData.reachable_of_coord_gt` | Fiber.lean | A | proved (sorry-free) |
| `GenData.coord_le_of_contributes` | Fiber.lean | A | proved (sorry-free) |
| `GenData.le_cutoff_of_contributes` | Fiber.lean | A | proved (sorry-free) |
| `GenData.ncomp_le_one_of_cutoff_lt` | Fiber.lean | A | proved (sorry-free) |
| `GenData.betaFiber_eq_sum_of_le` | Fiber.lean | A | proved (sorry-free) |
| `GenData.n_pos`, `nu_zero`, `nu_add`, `nu_single`, `nu_sub`, `single_le_nu`, `m_mul_le_nu`, `nu_pos_of_pos`, `le_div_m_of_nu_eq`, `nu_replace`, `reachable_of_sharesVar`, `ncomp_le_one_of_reachable`, `exists_not_reachable`, `reachable_of_bridge` (new A helpers, vendor port) | Fiber.lean | A | proved (sorry-free) |
| `X_mul_mono` | Bridge.lean | A | proved (sorry-free) |
| `GenData.rep`, `genSet`, `binomGens` | Bridge.lean | A | def |
| `GenData.nu_rep`, `rep_mk`, `card_genSet_le`, `card_binomGens_le`, `binomGens_subset_toricKer`, `sub_mem_of_sharesVar`, `sub_mem_of_reachable`, `rep_sub_rep_mem`, `mono_sub_mem_span`, `toricKer_eq_span` (new A helpers, vendor port; containment via A1's handoff) | Bridge.lean | A | proved (sorry-free) |
| `GenData.spanRank_toricKer_le_beta1` | Bridge.lean | A | proved (sorry-free) |
| `homogeneousComponent_mul_right` | Graded/Projection.lean | A | proved (sorry-free) |
| `homogeneous_mem_span_range` (handoff to B) | Graded/Projection.lean | A | proved (sorry-free) |
| `weighted_component_eq_zero_of_small` (handoff to B) | Graded/Projection.lean | A | proved (sorry-free) |
| `augmentationIdeal`, `decomposables`, `Indecomposables`, `indecomposablesMk` | Graded/Indecomposables.lean | A | def |
| `mem_augmentationIdeal_iff` | Graded/Indecomposables.lean | A | proved (sorry-free) |
| `indecomposablesMk_mul` | Graded/Indecomposables.lean | A | proved (sorry-free) |
| `span_indecomposablesMk_eq_top` | Graded/Indecomposables.lean | A | proved (sorry-free) |
| `generatorClass` | Graded/Indecomposables.lean | A | def |
| `sub_C_coeff_zero_mem_augmentationIdeal`, `indecomposablesMk_eq_zero_iff` (new A helpers) | Graded/Indecomposables.lean | A | proved (sorry-free) |
| `linearIndependent_generatorClass` | Graded/Indecomposables.lean | A | proved (sorry-free) |
| `card_le_card_of_span_eq` | GradedGenerators.lean | A | proved (sorry-free) |
| `card_le_spanRank_of_independent_generatorClass` | GradedGenerators.lean | A | proved (sorry-free) |
| `spanRank_eq_card_of_weightedHomogeneous_irredundant` (handoff to B) | GradedGenerators.lean | A | proved (sorry-free) |

The plan's helpers `degreeRoot` / `weight_degreeRoot` (§2 A1) are private in Algebra.lean, together
with `toricKer_le_ideal_aux` (the proof body of the handoff, inside `section Helpers`).

## Stream B

| declaration | file | owner | status |
|---|---|---|---|
| `Family.gens` (+ five `rfl` value lemmas), `HIndex`, `NIndex` | Family/Defs.lean | B | def / proved |
| `Family.gens_pos` | Family/Defs.lean | B | proved |
| `Family.gens_strictMono` | Family/Defs.lean | B | stub |
| `Family.gens_gcd` | Family/Defs.lean | B | stub |
| `exp5`, `hExp`, `nExp`, `RelIndex`, `relExp`, `relation`, `familyIdeal`, `relationDegree`, `nOffset` | Family/Data.lean | B | def |
| `NormalB`, `NormalBC`, `NormalD`, `NormalCD`, `NormalForm`, `normalExp`, `normalOffset`, `normalMono` | Family/Data.lean | B | def |
| `offset`, `psi`, `attainable`, `IsApery` | Family/Data.lean | B | def |
| `relIndex_card` (handoff) | Family/Relations.lean | B | stub |
| `h_weight` | Family/Relations.lean | B | stub |
| `n_weight` | Family/Relations.lean | B | stub |
| `relation_weightedHomogeneous` (handoff) | Family/Relations.lean | B | stub |
| `relationDegree_pos` (handoff) | Family/Relations.lean | B | stub |
| `relation_mem_toricKer` | Family/Relations.lean | B | stub |
| `normalOffset_lt` | Family/NormalForms.lean | B | stub |
| `normalOffset_injective` | Family/NormalForms.lean | B | stub |
| `normalOffset_surjective` | Family/NormalForms.lean | B | stub |
| `normalOffsetEquiv` | Family/NormalForms.lean | B | def (from stubs) |
| `card_normalForm` | Family/NormalForms.lean | B | proved |
| `normalWeight` | Family/NormalForms.lean | B | stub |
| `normal_repr_injective` | Family/NormalForms.lean | B | stub |
| `residual_step` | Family/Generation.lean | B | stub |
| `monomial_normal_form` | Family/Generation.lean | B | stub |
| `familyIdeal_eq_toricKer` (handoff) | Family/Generation.lean | B | stub |
| `normalWeight_isApery` | Family/Apery.lean | B | stub |
| `apery_iff_normalWeight` | Family/Apery.lean | B | stub |
| `psi_H` | Family/Minimality.lean | B | stub |
| `psi_N` | Family/Minimality.lean | B | stub |
| `psi_N_ne_zero` | Family/Minimality.lean | B | stub |
| `H_nonredundant` | Family/Minimality.lean | B | stub |
| `N_nonredundant` | Family/Minimality.lean | B | stub |
| `H_degree_lt_D` | Family/Minimality.lean | B | stub |
| `H_boundary_collisions` | Family/Minimality.lean | B | stub |
| `H_degree_lt_D_add_m` | Family/Minimality.lean | B | stub |
| `relation_nonredundant` (handoff) | Family/Minimality.lean | B | stub |
| `Family.spanRank_eq` (Theorem F, internal) | Family/Main.lean | B | proved (assembly; depends on stubs) |
| `Examples.thirteen`, `thirteenApery` | Examples/Thirteen.lean | B | def |
| `Examples.thirteen_spanRank_eq_fourteen` | Examples/Thirteen.lean | B | proved (specialization of F) |
| `family_spanRank_eq` (public Theorem F) | Solution.lean | B | proved (wrapper of `Family.spanRank_eq`) |
| `Targets.beta1_five_le_two_width_add_two` (Theorem W) | Targets/FiniteWidth.lean | — | admitted, outside Solution |

## Contract deviations

None. Every signature from the plan elaborated verbatim; no import, universe or instance fix was
needed. Layout-only choices (no change to any statement):

* Algebra.lean: the A1 helper lemmas sit in a `section Helpers` so that their section variables
  `{e} {K} [Field K]` are closed before the handoff theorem, which binds its own `{e} {K}`.
* Fiber.lean: the A5 definitions and the cutoff lemmas share one `namespace GenData` block with a
  single `variable (G : GenData e)` instead of the plan's two blocks that redeclare `{e}`.
* `gens_pos` lives in Family/Defs.lean (plan §3 B1 adds it next to `gens_strictMono`/`gens_gcd`).

Linter noise accepted from verbatim plan text: the unused hypothesis `hm : 0 < m` in the frozen
signature of `weighted_component_eq_zero_of_small` (implied by `0 < n < m`); the unused `hd : ∀ i, 0 < d i`
in `linearIndependent_generatorClass` (the independence argument does not need positive degrees); `linter.style.whitespace` ("`k-1` should be written
`k - 1`", 32 instances) and the unused-`[Fintype ι]` linter on `linearIndependent_generatorClass`.
Fixing either would alter frozen text; leave them, or clean up together after completion.
