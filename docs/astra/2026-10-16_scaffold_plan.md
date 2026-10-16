<!-- astra: model=gpt-6-astra effort=high status=completed thread=01a146e2-e126-77f0-9ed3-d6a0e42d86ab job=20261016T184356_scaffold-five-generator-betti-lean-repo-plan -->

I read `Defs`, `Fiber`, `Critical`, `Partition`, `Identities`, `Antichain`, `Arith`, `Exceptional`, `Main`, `NOTES`, and `Basic` completely. I inspected the `Bridge` declaration inventory; another branch should own its full proof audit.

**Principal correction:** the invalid five-generator port begins at `Critical.ncomp_sub_one_le`, not merely `sigma_le_four`. Its proof explicitly excludes two nonsingleton components plus one singleton because \(2+2+1>4\). This exclusion fails in dimension five.

A direct in-memory computation for \(\langle13,14,16,18,19\rangle\) gave:

- Apéry values by residue: `[0,14,28,16,30,18,19,33,34,35,36,37,38]`.
- `betaFiber = 14`, old `sigma = 8`, singleton-component total `5`, `p = 0`, `N = 9`.
- At degree `32`, support components `{0,4}`, `{1,3}`, `{2}`.
- At degree `44`, support components `{0,3}`, `{1,2}`, unused index `4`.
- At degrees `52` and `54`, additional `1+2+2` cases occur.

These are independent computed checks, not Lean proofs. They give a concrete counterexample to `sigma ≤ 5`.

A valid predecessor certificate for residues `1..12`, using generator indices `1..4`, is:

```text
[1,1,2,1,3,4,1,3,2,3,4,4]
```

The support-graph contributing degrees and components are:

```text
32: {0,4} | {1,3} | {2}
42: {0,2} | {1}
44: {0,3} | {1,2}
47: {0,2,3} | {1,4}
49: {0,3} | {1,2,4}
52: {0} | {1,4} | {2,3}
53: {0,1} | {2,3,4}
54: {0,1} | {2,4} | {3}
55: {0,1,2} | {3,4}
56: {0,1,2} | {3,4}
57: {0,1,2,3} | {4}
```

### Per-file reuse assessment

Efforts below are implementation estimates for one experienced Lean developer, not measured completion forecasts.

| Existing file | Reuse and changes | Estimated work |
|---|---|---:|
| `Basic.lean`, 21 lines | Unused skeleton containing only `IsFactorization`; absorb into new `Defs`, do not create a competing factorization definition | <½ day |
| `Defs.lean`, 205 lines | Reuse `len`, `supp`, `SharesVar`, additive degree lemmas. Replace offset-specific `GenData`, not just `Fin 4`. Drop normalized `A,B,W` arithmetic from generic core | 1–2 days |
| `Fiber.lean`, 247 lines | Almost all arguments generic. Replace `n 3` by maximum generator; keep finite cutoff proof. Fiber box uses minimum generator | 1–2 days |
| `Bridge.lean`, 380 lines | Declaration inventory indicates first ≈300 lines dimension-generic; replace `ofChallenge` offset conversion at end with direct generic constructor | Agent owning Bridge should estimate |
| `Critical.lean`, 346 lines | Reuse through `two_le_crit`, `HasSingletonComp`, `critIndices`; replace `succ_ne` by “there exists a different index” under `2≤e`. Discard `ncomp_sub_one_le` and `sigma_le_four` | 1–2 days port; 2–4 days new exact counting |
| `Partition.lean`, 343 lines | Reuse `reachable_induction`, `comp_eq_of_mem`, `exists_full_vertex`, `exists_supp_eq`, selection machinery. Replace `IsSplit`, `lemma5`, `famP/Q/E`, `beta1_eq`, `no_replace`, and antichain interfaces | 2–4 days |
| `Antichain.lean`, 279 lines | `IsPairAntichain` through `exists_rank` (lines 29–120) ports unchanged, apart from imports/namespace. General coordinate injection lemmas adapt to pair-component interface. Do not port `P_le`, `Q_le`, `E_le` | ½–1½ days |
| `Identities.lean`, 170 lines | Four-generator arithmetic argument; no wholesale port. Its vector-identity proof style is useful for family membership. Replace by new `Family/Relations.lean` | No port; new work separately |
| `Exceptional.lean`, 305 lines | Extract generic pair-coordinate helpers through `exists_coord_eq` (lines 29–94), adapting interface. Do not port exceptional arithmetic and saturation contradiction | ½–1 day extraction |
| `Arith.lean`, 79 lines | Entire concluding width argument depends on four-generator decomposition; do not port | None |
| `Main.lean`, 38 lines | Rewrite exports around family theorem and explicitly conjectural finite-width target | ½ day |
| `NOTES.md`, 210 lines | Rewrite provenance/API map; historical toolchain prose is stale | ½ day |

No entire substantive file ports literally unchanged because every substantive library file imports or refers to the old offset-specific structure. The genuinely unchanged proof blocks are the abstract reachability induction and positive-pair antichain theory.

The actual `lean-toolchain` is `leanprover/lean4:v4.35.0-rc3`. `NOTES.md` says a move to rc4 occurred; this prose must not determine the new pin.

### Generic data design

The old structure has fields `m a b w`, and defines

```lean
gens m a b w : Fin 4 → ℕ := ![m, m+a, m+b, m+w]
```

It mixes positivity, ordering, primitivity, minimality, and normalized offsets. Do not copy that structure and add a fifth offset throughout all proof files.

Prefer generic positive-generator infrastructure; keep numerical-semigroup/minimality assumptions in a separate wrapper. For example, a practical structure can store:

```lean
structure GenData (e : ℕ) where
  n : Fin e → ℕ
  m : ℕ
  maxGen : ℕ
  m_pos : 0 < m
  lower : ∀ i, m ≤ n i
  upper : ∀ i, n i ≤ maxGen
```

This avoids delicate `Fin e` zero/last indexing in the generic core and allows exactly the existing efficient fiber box and cutoff:

```lean
def fiber (d : ℕ) : Finset (Fin e → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (d / G.m + 1)).filter
    (fun z => G.nu z = d)

def cutoff : ℕ := G.maxGen * ∑ i, G.n i
```

The five-generator constructor sets `m := n 0`, `maxGen := n 4`, using strict monotonicity. Critical exponents additionally require `2 ≤ e`; minimality is needed for `two_le_crit`, but not for the singleton-counting identity itself.

### Correct decomposition interfaces

Define the contributing-degree finset first:

```lean
noncomputable def bettiDegrees : Finset ℕ :=
  (Finset.range (G.cutoff + 1)).filter G.contributes
```

Define `singletonCount d` and `nonsingletonCount d` by filtering connected components according to support cardinality `=1` and `≥2`. Define `p` and `N` **only over `bettiDegrees`**; otherwise `t_d=0` includes infinitely many empty fibers.

Suggested declaration chain:

```lean
theorem critDegree_contributes (i : Fin e) :
    G.contributes (G.crit i * G.n i)

theorem singletonCount_eq_critIndices_card
    {d : ℕ} (hd : G.contributes d) :
    G.singletonCount d = (G.critIndices d).card

theorem sum_singletonCount_eq :
    ∑ d ∈ G.bettiDegrees, G.singletonCount d = e

theorem singletonCount_add_nonsingletonCount
    {d : ℕ} (hd : G.contributes d) :
    G.singletonCount d + G.nonsingletonCount d = G.ncomp d
```

For `G : GenData 5`:

```lean
theorem nonsingletonCount_le_two
    {d : ℕ} (hd : G.contributes d) :
    G.nonsingletonCount d ≤ 2

theorem betaFiber_add_p_eq :
    G.betaFiber + G.p = 5 + G.N

theorem p_le_two : G.p ≤ 2
```

Proof of exact singleton counting: use `compSupp_critVertex`, `degree_eq_of_singleton_comp`, and `comp_eq_critVertex` to prove equality with `critIndices`, rather than merely the old injection inequality. Every critical degree contributes because its isolated pure-power vertex has an alternative factorization. Then sum the cardinalities of fibers of the function `i ↦ crit i * n i`.

For `p_le_two`, every contributing degree with no nonsingleton components has at least two singleton components. Therefore `2*p ≤ 5`, using the exact total count.

State the equivalence with a width lower bound, to justify natural subtraction:

```lean
theorem betaFiber_bound_iff (w : ℕ) (hw : 4 ≤ w) :
    G.betaFiber ≤ 2*w+2 ↔ G.N ≤ 2*w-3+G.p
```

This is `omega` after `betaFiber_add_p_eq`.

### Pair-component antichain: stronger and cleaner than the old interface

Replace complement-based `IsSplit` by:

```lean
def HasPairComponent (d : ℕ) (K : Finset (Fin e)) : Prop :=
  G.contributes d ∧ K.card = 2 ∧
    ∃ C : (G.nabla d).ConnectedComponent, G.compSupp C = K
```

Then:

```lean
theorem exists_pair_factorization
    (h : G.HasPairComponent d K) :
    ∃ z : Fin e → ℕ, G.nu z = d ∧ supp z = K

theorem pairComponent_antichain
    (h : G.HasPairComponent d K)
    (h' : G.HasPairComponent d' K)
    (hne : d ≠ d') :
    ¬ G.sel d K ≤ G.sel d' K
```

The strengthened proof does **not** need any full-support representative of a complementary component at degree `d'`:

1. Suppose `u ≤ v`, where both selected vectors have support `K`, but distinct degrees.
2. Choose any factorization `y` in a different component from `u` at degree `d`. Its nonempty support is disjoint from `K`.
3. `v-u` is nonzero because the degrees differ.
4. `b := v-u+y` has the later degree and shares a retained coordinate with `v`.
5. Hence `b` belongs to the later component of `v`, whose support is exactly `K`.
6. But `y` gives a positive coordinate of `b` outside `K`, contradiction.

This works for all three five-generator support types, and in fact arbitrary finite embedding dimension. Existing `nu_replace`, `reachable_of_sharesVar`, `supp_subset_compSupp`, and `compSupp_disjoint` supply almost the entire proof.

Likewise rewrite `no_replace` as a statement about a **single component with exact support `K`**. Its current complement-based proof makes an unnecessary assumption that breaks reuse.

The `2+3`, `2+2+unused`, and `1+2+2` classification should follow from disjoint nonempty component supports and `r+2t≤5`. A finite `decide` proof can count labeled patterns once a precise finite encoding is chosen, but the mathematical decomposition does not require pattern enumeration.

I used no additional subagents.

I read all assigned files, all scripts, and the new repository README. No applicable `AGENTS.md` exists in these repositories or their `/Users/ben` ancestors. No files were written.

**Verified facts and corrections**

- Toolchain: `leanprover/lean4:v4.35.0-rc3`.
- Mathlib: tag `v4.35.0-rc3`, exact commit `c55e6e786f49471c72fbddbec5415808896aec1e`.
- Template current commit: `aa266b8a7db2794e49a0053978852ade100d23da`.
- Template has uncommitted README, metadata, correspondence changes and untracked C/results files. Do not reset or “clean” it.
- Actual `.github/workflows/ci.yml` **already contains the comparator job**. README says it does not: stale documentation.
- README and correspondence record only per-project-module `leanchecker` replay; whole-import `--fresh`, NanoDa and comparator are not recorded as completed. Do not inherit those as verified results.
- `.lake` is 11 GB; Mathlib package accounts for essentially all of it.
- New repo contains README plus the two `docs/astra` files, so preserve them.
- Source checker and metadata validator both passed in this audit.
- The three infrastructure scripts to copy are `check-lean-sources.py`, `validate-formalization.rb`, `verify-comparator.sh`.
- Do not copy the four-generator C sweep or results as new-project evidence. They are exploratory four-generator computations, not the requested five-generator certificate implementation.

**Bootstrap recommendation**

Copy/adapt the development sources rather than making the old root package a dependency: the needed combinatorial definitions are hardcoded to four generators and require actual generalization; importing the old package does not solve that. Preserve original source copyright and document the source commit.

Prefer an APFS clone of **all dependency packages**, with a separate new-root `.lake/build`; otherwise symlink all package directories, not only Mathlib. Mathlib depends on the other eight packages listed in the copied manifest.

Suggested commands Claude may execute, from writable context:

```sh
src=/Users/ben/semigroup-betti
dst=/Users/ben/five-generator-betti

mkdir -p "$dst/scripts" "$dst/.github/workflows" "$dst/FiveGenBetti" "$dst/docs"
cp "$src/lean-toolchain" "$src/lake-manifest.json" "$src/LICENSE" "$dst/"
cp "$src/scripts/check-lean-sources.py" "$dst/scripts/"
cp "$src/scripts/validate-formalization.rb" "$dst/scripts/"
cp "$src/scripts/verify-comparator.sh" "$dst/scripts/"
cp "$src/.github/workflows/ci.yml" "$dst/.github/workflows/ci.yml"
chmod +x "$dst/scripts/verify-comparator.sh"
mkdir -p "$dst/.lake"
cp -cR "$src/.lake/packages" "$dst/.lake/packages"
```

`cp -cR` is the macOS APFS clone option; it saves initial physical storage while isolating subsequent writes. Run only when the destination packages directory is absent. Portable alternative: `cp -a`, costing approximately 11 GB. Lightweight symlink alternative:

```sh
mkdir -p "$dst/.lake/packages"
for package in "$src"/.lake/packages/*; do
  ln -s "$package" "$dst/.lake/packages/$(basename "$package")"
done
```

Symlinks share writes; do not run `lake update` or cache-mutating experiments against shared dependencies. Symlinks under ignored `.lake` are local-only and are not source `.lean` symlinks.

For a clean machine, use copied pins/manifest and `lake exe cache get`, then `lake build`; the template reports incomplete cache availability on 2026-10-06, not a guarantee of today’s completeness. CI cannot reuse macOS binary artifacts.

Set root manifest `"name": "fivegenbetti"` while retaining **every packages entry unchanged**. Keep the lakefile tag matching manifest `inputRev`; the committed full manifest fixes its actual commit. No `lake update` is necessary.

```toml
name = "fivegenbetti"
version = "0.1.0"
keywords = ["math"]
defaultTargets = ["FiveGenBetti", "Challenge", "Solution"]

[leanOptions]
pp.unicode.fun = true
autoImplicit = false
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.35.0-rc3"

[[lean_lib]]
name = "FiveGenBetti"

[[lean_lib]]
name = "Challenge"

[[lean_lib]]
name = "Solution"
```

Copy Apache LICENSE unchanged, including its inherited template appendix; new/modified Lean files retain and add accurate copyright/authorship/modification notices.

**Statement draft actually elaborated**

I submitted the following through `lake env lean --stdin` against the pinned cached environment. It exited successfully with precisely two expected `sorry` warnings. Thus its statement syntax, coercions, imports, universe-polymorphic field and match-based generator function have been checked; its mathematics has not been proved.

```lean
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Algebra.Group.Submonoid.Basic

@[expose] public section

namespace FiveGenBetti

noncomputable def toricIdeal (K : Type*) [Field K] (n : Fin 5 → ℕ) :
    Ideal (MvPolynomial (Fin 5) K) :=
  RingHom.ker
    (MvPolynomial.aeval
      (fun i => (Polynomial.X : Polynomial K) ^ n i)).toRingHom

def familyGens (k q : ℕ) (i : Fin 5) : ℕ :=
  let m := 2 * k * q + 1
  match i.val with
  | 0 => m
  | 1 => m + 1
  | 2 => m + k
  | 3 => m + (2 * k - 1)
  | _ => m + 2 * k

def MinimallyGenerates (n : Fin 5 → ℕ) : Prop :=
  ∀ i : Fin 5,
    n i ∉ AddSubmonoid.closure (n '' {j | j ≠ i})

theorem family_spanRank_eq (K : Type*) [Field K] (k q : ℕ)
    (hk : 3 ≤ k) (hq : k - 1 ≤ q) :
    (toricIdeal K (familyGens k q)).spanRank = (4 * k + 2 : ℕ) := by
  sorry

theorem beta1_five_le_two_width_add_two
    (K : Type*) [Field K] (n : Fin 5 → ℕ)
    (hpos : 0 < n 0) (hmono : StrictMono n)
    (hgcd : Finset.univ.gcd n = 1)
    (hmin : MinimallyGenerates n)
    (hwlo : 4 ≤ n 4 - n 0)
    (hwhi : n 4 - n 0 ≤ 40) :
    (toricIdeal K n).spanRank ≤
      (2 * (n 4 - n 0) + 2 : ℕ) := by
  sorry

end FiveGenBetti
```

`familyGens` uses `i.val` to avoid vector notation/import ambiguities. Under `k ≥ 3`, `m+(2*k-1)` equals intended `m+2*k-1`. The wildcard means only index 4 because domain is `Fin 5`; prove five `[simp]` value lemmas and the domain hypotheses explicitly.

Solution must repeat these definitions/statements without importing Challenge; comparator checks agreement through definitions. A project-level definitions file cannot be publicly imported into Challenge if “Mathlib-only” is meant literally.

**Comparator**

```json
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": [
    "FiveGenBetti.family_spanRank_eq",
    "FiveGenBetti.beta1_five_le_two_width_add_two"
  ],
  "permitted_axioms": [
    "propext",
    "Quot.sound",
    "Classical.choice"
  ]
}
```

This is the **eventual two-theorem comparator configuration**. It must fail during scaffolding. Do not add `sorryAx` to permitted axioms to obtain a green badge. Because W is explicitly outside v1 completion, use a family-only comparator configuration for the first honest family release, and clearly advertise W as an unproved target; keep its unproved declaration outside the released Solution dependency closure. During day-one scaffolding both Solution statements can contain holes, but that is not a submission.

The script rejects submitter-supplied `external_kernels`, removes `enable_nanoda`, and supplies bundled NanoDa and con-ron itself. It requires Linux `bwrap`; it runs `lake exe cache get` and `lake comparator --config <temporary-config>`. Copy the actual CI comparator job, which installs bubblewrap and disables disposable-runner AppArmor user-namespace restriction.

Day-one CI can run build and metadata while leaving comparator manual or explicitly expected to fail; never depict an expected comparator failure as completed proof verification.

**Metadata**

Use the template’s v0.4 shape. Important fields:

```yaml
version: "v0.4"

project:
  name: "First Betti numbers of five-generated numerical semigroups"
  description: >-
    A Lean 4 and Mathlib formalization project for an explicit family
    with toric-ideal spanRank 4k+2 and a proposed finite-width upper bound
    2w+2 for minimally five-generated numerical semigroups.
  authors: ["Ben Keene"]
  license: "Apache-2.0"
  responsible_maintainers: ["Ben Keene"]

repository:
  role: substantive-development

classification:
  arxiv: [math.AC, math.CO]
  msc2020: ["13D02", "20M14", "13F65", "05E40"]

status:
  scope: >-
    SCAFFOLD (2026-10-16). The family formula is PROOF_ATTEMPT:
    its informal presentation and minimality argument await the prescribed
    independent review and Lean completion. The finite-width inequality
    is a conjecture. Version 1 targets family formalization and
    certificate-checker soundness; formal periodicity and the complete
    finite-width computational theorem are excluded. A successful
    scaffold build is not a proof.
  # Set sorry_count, sorry_in_definitions and axioms from the actual tree.
  main_results:
    - "FiveGenBetti.family_spanRank_eq"

fidelity:
  divergences: >-
    Statements use Submodule.spanRank of the toric ideal as a cardinal.
    Equality with the factorization-fiber invariant requires a new reverse
    bridge. The finite-width target has not been proved.

related_formalizations:
  - id: "https://palomar-registry.org/entry?id=PALOMAR-2026-10-07-000005&version=1"
    relationship: other
    note: >-
      Four-generator template and source library; reused files and
      source commit are recorded in docs/PORTING.md.

automation:
  methods:
    - method: agent
      models: ["GPT-6 Astra (OpenAI)"]
      framework: "Codex"
      tool_setup: "Read-only repository and mathematical audit for the scaffold plan."
      prompting_notes: "Independent audit; no proof status inferred from agent agreement."
  notes: "Update with actual Claude implementation model and workflow when execution begins."

review:
  status: self-assessed
  reviewers: []
  notes: "No completed review or proof verification is claimed at scaffold stage."

known_gaps:
  - "Family generation and minimality are not yet formalized."
  - "Reverse bridge is not yet formalized."
  - "Finite-width theorem is unproved; periodicity and exhaustive replay are out of v1 scope."
```

The copied Ruby validator checks YAML shape, v0.4, mandatory sections, description length, Apache license, and absence of `TEMPLATE` values. It **does not perform full remote JSON-schema validation**, count holes, inspect axioms, or verify alignment status values. Do not mistake its success for those stronger checks. Fill counts from the actual scaffold; do not fabricate them in the plan. If admitted Solution results are listed, record `sorryAx` honestly in observed status while keeping comparator whitelist strict.

Add sources for the inlined workflow as unpublished PROOF_ATTEMPT and for the reused formalization. Do not copy old novelty/review/completion statements.

**Verification commands and correspondence skeleton**

```sh
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
lake build

rg -n '\b(sorry|admit|axiom)\b|native_decide|ofReduceBool|unsafe' \
  --glob '*.lean' --glob '!.lake/**' .

lake env leanchecker FiveGenBetti
lake env leanchecker Solution
lake env leanchecker --fresh Solution
./scripts/verify-comparator.sh
```

A scratch module importing **Solution**, not Challenge, should contain:

```lean
#print axioms FiveGenBetti.family_spanRank_eq
```

Only check W as proved once it really is. `rg` is a lexical audit, not axiom verification. `leanchecker Solution` rechecks the module against trusted imports; `--fresh` checks its import closure and can take hours. Bundled comparator supplies independent kernels. For manual exports, keep `.export` and NanoDa config/output outside checkout; prior README estimated export around 6 GB.

CORRESPONDENCE sections:

1. Informal claim, parameter domain, status, source claim-packet paths.
2. Verbatim statements of record.
3. Generator indexing and `Nat` subtraction checks.
4. Positivity, strict monotonicity, gcd/cofiniteness, minimal generation.
5. Kernel ideal and field universes.
6. Cardinal `spanRank` versus ideal generator count.
7. Both bridge directions and precise formal scope.
8. Family normal-form, generation, minimality correspondence table.
9. Checker input semantics and three soundness lemmas.
10. Explicit exclusions: periodicity, exhaustive W replay, novelty.
11. Build/axiom/comparator/independent-kernel record, each with date, command, commit and actual outcome.
12. Source provenance and verified statement deltas from the four-generator library.

Source checker enforces module headers, forbids source `.lean` symlinks, caps every Lean file at 10,000 lines, and Challenge at 1,000 lines/100 KiB. It skips `.lake` and `.git`. It does **not** check the stated 500 MiB submission cap. Add a separate tracked-archive size check; ignore `.lake`, exports, bulk certificates and local logs.

Potentially useful Mathlib facts inspected locally: `Submodule.exists_span_set_card_eq_spanRank`, `FG.exists_span_finset_card_eq_spanFinrank`, `FG.spanRank_eq_spanFinrank`, `spanRank_span_le_card`, `spanRank_map_le`, and `Module.Basis.mk_eq_spanRank`. The generic reverse bridge can lower-bound arbitrary spanning sets through the appropriate quotient; irredundancy of one list alone is not a lower bound on spanRank.

No subagents used within this delegated audit.

The family equality remains plausible, but the requested indispensability claim is false.

For every admissible \(k,q\),
\[
N_0=cd^{k-1}e^{q-k+1}-a^{q+2}
\]
can be replaced by
\[
N'_0=be^q-a^{q+2}
=N_0+e^{q-k+1}(be^{k-1}-cd^{k-1}).
\]
The parenthesized relation is already in \(H\). This replacement preserves the generated ideal and cardinality. Consequently \(N_0\) is not indispensable in the standard sense of occurring, up to scalar, in every minimal binomial generating set. The valid target is **nonredundancy within the displayed presentation**.

A second missing step is the passage from irredundancy to `spanRank`. In a general nonlocal ring, an irredundant generating set need not have minimum cardinality. Here positivity and weighted homogeneity repair this through
\[
Q=I/\mathfrak m I,\qquad \mathfrak m=(a,b,c,d,e).
\]
The classes of the displayed generators span \(Q\). A scalar dependence modulo \(\mathfrak m I\), projected to each weighted degree, expresses some generator using the others: the coefficients contributed by \(\mathfrak m I\) have positive weight. Thus nonredundancy makes these classes independent. Every arbitrary ideal generating set maps to a spanning set of \(Q\), proving the required minimum cardinality.

A useful generic draft is:
```lean
theorem spanRank_eq_card_of_weightedHomogeneous_irredundant
    {σ ι : Type*} [Fintype σ] [Fintype ι]
    (K : Type*) [Field K]
    (w : σ → ℕ) (hpos : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial σ K))
    (f : ι → MvPolynomial σ K) (deg : ι → ℕ)
    (hhom : ∀ j, (f j).IsWeightedHomogeneous w (deg j))
    (hgen : Ideal.span (Set.range f) = I)
    (hirr : ∀ j, f j ∉ Ideal.span (f '' {i | i ≠ j})) :
    I.spanRank = (Fintype.card ι : Cardinal)
```
This is a proposed declaration, not compiled code. It lets the family theorem land independently of the complete reverse fiber bridge.

Local APIs verified:

- `MvPolynomial.IsWeightedHomogeneous`
- `MvPolynomial.weightedHomogeneousComponent`
- `MvPolynomial.sum_weightedHomogeneousComponent`
- `Submodule.exists_span_set_card_eq_spanRank`
- `Submodule.FG.exists_span_finset_card_eq_spanFinrank`

The existing `IsLocalRing.spanFinrank_eq_finrank_quotient` cannot be applied directly to the polynomial ring.

The cleanest generation proof avoids the finite-dimensional quotient API. Prove:
```lean
lemma monomial_normal_form (z : Fin 5 → ℕ) :
    ∃ (ℓ : ℕ) (u : NormalForm k q),
      mono K z -
        MvPolynomial.X 0 ^ ℓ * normalMono K u ∈ familyIdeal K k q
```
Use strong induction on weighted degree. Whenever a reduction introduces \(a\), strip it and invoke induction. The only reductions preserving the absence of \(a\) are the last \(B\)-relation, which removes \(b\), and \(d^k\to ce^{k-1}\), which decreases the \(d\)-exponent; a second such reduction introduces \(c^2\), hence \(a\).

The specific divisors needed are:

- \(b^i e^j\), \(i+j\ge k\), \(2\le i<k\): use \(B_{k-1-i}\).
- \(be^j\), \(j\ge k-1\): use \(B_{k-2}\).
- \(b^ice^j\), \(i+j\ge k-1\), \(i<k\): use \(A_{k-1-i}\).
- \(d^te^j\), \(t<k\), \(t+j\ge q+1\): use \(N_{2k-1-t}\).
- \(cd^te^j\), \(t<k\), \(t+j\ge q\): use \(N_{k-1-t}\).

The normal forms have offsets
\[
i+2kj,\quad k+i+2kj,\quad 2k(t+j)-t,\quad k+2k(t+j)-t.
\]
These partition \(\{0,\ldots,2kq\}\). A direct proof splits by residue \(h\bmod 2k\):

| Residue | Normal forms and quotient levels |
|---|---|
| \(h=0\) | \(d\)-family, \(t=0\), levels \(0,\ldots,q\) |
| \(1\le h<k\) | \(b\)-family levels \(0,\ldots,k-h-1\); \(cd\)-family \(t=k-h\), levels \(k-h,\ldots,q-1\) |
| \(h=k\) | \(cd\)-family \(t=0\), levels \(0,\ldots,q-1\) |
| \(k<h<2k-1\) | \(bc\)-family levels \(0,\ldots,2k-h-2\); \(d\)-family \(t=2k-h\), levels \(2k-h-1,\ldots,q-1\) |
| \(h=2k-1\) | \(d\)-family \(t=1\), levels \(0,\ldots,q-1\) |

Therefore the images \(a^\ell A_u\) have distinct exponents under the toric map. Equal-weight monomials have identical normal forms, so their difference lies in \(J\). Abstract the existing coefficient-sum argument in `Bridge.lean` into `toricKer_le_ideal_of_mono_sub_mem`; it then proves \(J=I\). Apéry correctness, the cardinality \(m\), equality modulo \(a\), and the requested dimension statement follow afterward. Distinct residues alone must **not** be used to assert independence modulo \(t^m\) before Apéry minimality is established.

The minimality argument otherwise survives:

- Modulo \(a,c^2,bd\), all degree-\(k\) images of \(H\) have pairwise disjoint nonzero supports.
- The monomial map satisfies the explicit identity
  \[
  \psi(N_r)=s^{q+1}t^r(t^m-s)\ne0,
  \]
  over every field.
- At \(q=k-1\), the only \(H\)-degrees in the \(N\)-band are \(D\) and \(D+k-1\).
- At \(q\ge k\), every \(H\)-degree is below \(D\).
- All \(H\)-degrees are below \(D+m\), so at a collision only a scalar multiple of the corresponding \(N_r\) can contribute.

Natural subtraction requires deliberate rewriting. Never encode the printed exponent \(q-k+1+r\) as `q - k + 1 + r`: at \(q=k-1\) that is off by one. Use `q + 1 + r - k`; similarly use `q + 2 + r - 2*k`. Better, index \(N\) by `Fin k ⊕ Fin k`, eliminating the second branch’s subtraction by \(2k\).

Computed evidence: an exact in-memory Python check verified the offset partition for **546 parameter pairs**, \(3\le k\le30\), \(k-1\le q\le2k+1\). This is computation, not a Lean proof.

No files were written; no additional subagents were used.

The plan is executable after correcting two claims in the brief:

- **The displayed \(N_r\) are not all indispensable.** Indeed,
  \[
  N_0+e^{q-k+1}(be^{k-1}-cd^{k-1})=be^q-a^{q+2}.
  \]
  Replacing \(N_0\) by this binomial preserves the generated ideal. The valid objective is **nonredundancy of the displayed generating list**.
- **Nonredundancy alone does not establish `spanRank`.** The missing argument is a lower bound on every generating set, obtained from \(I/\mathfrak m I\), or an equivalent component-charge construction.

I found no counterexample to the family equality. Its status remains **PROOF_ATTEMPT**. No files were written.

1. **Record the corrected scope and preserve the existing evidence.**

   Before creating Lean declarations, add these corrections to `docs/PROOF.md` and a separate family claim packet under `~/aiseminar`. Use declaration names such as `N_not_mem_span_other_relations`; do not introduce `N_indispensable`.

   The first completed release should contain:

   - The family theorem.
   - Generic fiber infrastructure and both algebraic bridges.
   - Correct singleton counting and the pair-component antichain lemma.
   - Certificate-checker soundness and a small kernel-checked example.
   - An explicitly unproved statement of the finite-width target.

   Formal periodicity and the complete width-40 replay remain outside version 1.

   Two template facts need correction in the new documentation:

   - The actual pin is **Lean v4.35.0-rc3**, despite historical rc4 prose in `SemigroupBetti/NOTES.md`.
   - The actual CI already contains a comparator job, despite contrary README prose.

   The template has uncommitted changes. Preserve them; record both its current commit and which working-tree files were copied. The inspected commit is `aa266b8a7db2794e49a0053978852ade100d23da`.

2. **Bootstrap a separate repository, copying and generalizing the useful library.**

   Do **not** make the four-generator root package the principal dependency. Its `GenData` stores `m,a,b,w`, and its main counting arguments are intrinsically four-generator arguments. A dependency would retain that structure without supplying the generic infrastructure needed here.

   Copy the useful proof blocks, preserve their notices, rename their namespace, and document provenance in `docs/PORTING.md`. Keep the original repository unchanged.

   Proposed tree:

   ```text
   five-generator-betti/
   ├── Challenge.lean
   ├── Solution.lean
   ├── FiveGenBetti.lean
   ├── FiveGenBetti/
   │   ├── Defs.lean
   │   ├── Fiber.lean
   │   ├── BridgeUpper.lean
   │   ├── BridgeLower.lean
   │   ├── GradedGenerators.lean
   │   ├── Critical.lean
   │   ├── Decomposition.lean
   │   ├── PairSupport.lean
   │   ├── Antichain.lean
   │   ├── Certificate/
   │   │   ├── Defs.lean
   │   │   ├── Apery.lean
   │   │   ├── SupportGraph.lean
   │   │   ├── Candidates.lean
   │   │   ├── Checker.lean
   │   │   └── Soundness.lean
   │   ├── Family/
   │   │   ├── Defs.lean
   │   │   ├── Relations.lean
   │   │   ├── NormalForms.lean
   │   │   ├── Generation.lean
   │   │   ├── Apery.lean
   │   │   ├── Minimality.lean
   │   │   └── Main.lean
   │   └── Examples/Thirteen.lean
   ├── Targets/
   │   └── FiniteWidth.lean
   ├── docs/
   │   ├── PROOF.md
   │   ├── PORTING.md
   │   ├── CHECKER.md
   │   └── astra/                 # preserve existing files
   ├── scripts/
   ├── .github/workflows/ci.yml
   ├── formalization.yaml
   ├── comparator.json
   ├── comparator.all-targets.json
   ├── CORRESPONDENCE.md
   ├── LICENSE
   ├── lakefile.toml
   ├── lake-manifest.json
   └── lean-toolchain
   ```

   Execute from a writable session:

   ```sh
   src=/Users/ben/semigroup-betti
   dst=/Users/ben/five-generator-betti

   mkdir -p "$dst/scripts" "$dst/.github/workflows" "$dst/FiveGenBetti" "$dst/docs"
   cp "$src/lean-toolchain" "$src/lake-manifest.json" "$src/LICENSE" "$dst/"
   cp "$src/scripts/check-lean-sources.py" "$dst/scripts/"
   cp "$src/scripts/validate-formalization.rb" "$dst/scripts/"
   cp "$src/scripts/verify-comparator.sh" "$dst/scripts/"
   cp "$src/.github/workflows/ci.yml" "$dst/.github/workflows/"
   chmod +x "$dst/scripts/verify-comparator.sh"
   ```

   Preserve the existing README and `docs/astra` contents.

   Use this `lakefile.toml`:

   ```toml
   name = "fivegenbetti"
   version = "0.1.0"
   keywords = ["math"]
   defaultTargets = ["FiveGenBetti", "Challenge", "Solution"]

   [leanOptions]
   pp.unicode.fun = true
   autoImplicit = false
   relaxedAutoImplicit = false
   weak.linter.mathlibStandardSet = true
   maxSynthPendingDepth = 3

   [[require]]
   name = "mathlib"
   scope = "leanprover-community"
   rev = "v4.35.0-rc3"

   [[lean_lib]]
   name = "FiveGenBetti"

   [[lean_lib]]
   name = "Challenge"

   [[lean_lib]]
   name = "Solution"
   ```

   Keep:

   ```text
   leanprover/lean4:v4.35.0-rc3
   ```

   The copied manifest pins Mathlib to:

   ```text
   c55e6e786f49471c72fbddbec5415808896aec1e
   ```

   Change only the manifest’s root `"name"` to `"fivegenbetti"`; preserve all package entries. There are dependencies besides Mathlib, so copying only its directory is insufficient for reliable offline reuse.

   On this Mac, prefer an APFS clone, provided the destination packages directory does not already exist:

   ```sh
   mkdir -p "$dst/.lake"
   cp -cR "$src/.lake/packages" "$dst/.lake/packages"
   ```

   Alternatives:

   | Method | Benefit | Cost/risk |
   |---|---|---|
   | APFS clone | Reuses blocks while isolating subsequent writes | Requires supported filesystem |
   | `cp -a` | Independent dependency tree | Approximately 11 GB |
   | Symlink dependency packages | Almost no extra storage | Package writes affect the template |
   | `lake exe cache get` | Clean bootstrap from committed pins | Network/cache availability; possible compilation |

   A symlink alternative is:

   ```sh
   mkdir -p "$dst/.lake/packages"
   for package in "$src"/.lake/packages/*; do
     ln -s "$package" "$dst/.lake/packages/$(basename "$package")"
   done
   ```

   Keep the new root’s `.lake/build` separate. Do not run `lake update` against shared packages. CI must obtain Linux artifacts independently.

   Copy the Apache license unchanged. Do not copy `betti_bruteforce.c` or its results as five-generator evidence.

   Per-file reuse assessment:

   | Template file | Action | Estimated effort |
   |---|---|---:|
   | `Basic.lean` | Absorb its lone factorization definition into `Defs` | <½ day |
   | `Defs.lean` | Generalize vector operations; replace offset-specific structure | 1–2 days |
   | `Fiber.lean` | Generalize fibers, supports, replacement, cutoff | 1–2 days |
   | `Bridge.lean` | Port proof core; replace `ofChallenge`; extract kernel-binomial lemma | 2–3 days |
   | `Critical.lean` | Port through critical-vertex results; replace counting tail | 1–2 days, plus new counting |
   | `Partition.lean` | Extract support lemmas; replace complementary splits | 2–4 days |
   | `Antichain.lean` | Copy abstract pair-antichain block; adapt selection interface | ½–1½ days |
   | `Exceptional.lean` | At most extract generic pair-coordinate helpers | ½–1 day |
   | `Identities.lean` | Do not port its arithmetic; write family identities separately | New work |
   | `Arith.lean` | Do not port | — |
   | `Main.lean` | Replace with new theorem assembly | ½ day |
   | `NOTES.md` | Rewrite provenance and API notes | ½ day |

   No substantive file ports literally unchanged. Some proof blocks do: abstract reachability induction and the abstract positive-pair antichain theory.

3. **Install honest metadata and separate the release comparator from the research targets.**

   Start `formalization.yaml` with:

   ```yaml
   version: "v0.4"

   project:
     name: "First Betti numbers of five-generated numerical semigroups"
     description: >-
       Lean 4 and Mathlib formalization of a proposed explicit family
       with toric-ideal spanRank 4k+2, together with structural lemmas
       and certificate-checker infrastructure for a proposed finite-width
       bound 2w+2.
     authors: ["Ben Keene"]
     license: "Apache-2.0"
     responsible_maintainers: ["Ben Keene"]

   repository:
     role: substantive-development

   classification:
     arxiv: [math.AC, math.CO]
     msc2020: ["13D02", "20M14", "13F65", "05E40"]

   status:
     scope: >-
       SCAFFOLD (2026-10-16). The family theorem is PROOF_ATTEMPT,
       awaiting complete informal review and Lean proofs. The finite-width
       inequality is conjectural. Version 1 targets the family theorem,
       structural lemmas and certificate-checker soundness. Formal
       periodicity and complete width-40 replay are outside version 1.
       A successful scaffold build does not establish the statements.
     main_results:
       - "FiveGenBetti.family_spanRank_eq"

   fidelity:
     divergences: >-
       The statements use cardinal-valued Submodule.spanRank of the
       toric ideal. Equality with the fiber invariant requires new
       lower-bound infrastructure. Nonredundancy of the displayed
       family presentation is intended; indispensability is not claimed.

   automation:
     methods:
       - method: agent
         models: ["GPT-6 Astra (OpenAI)"]
         framework: "Codex"
         tool_setup: "Read-only mathematical and repository audit."
     notes: >-
       Add the actual implementation models and workflow as work occurs.

   review:
     status: self-assessed
     reviewers: []
     notes: "No completed family proof review is claimed."

   known_gaps:
     - "Family generation and minimum generator cardinality are not formalized."
     - "The reverse fiber bridge is not formalized."
     - "The finite-width theorem is unproved."
   ```

   Add source entries for the unpublished workflow and reused formalization. Fill `sorry_count`, `sorry_in_definitions`, and observed axioms from the actual scaffold. During development, dependencies on `sorryAx` must be reported honestly.

   For the family release, use:

   ```json
   {
     "challenge_module": "Challenge",
     "solution_module": "Solution",
     "theorem_names": [
       "FiveGenBetti.family_spanRank_eq"
     ],
     "permitted_axioms": [
       "propext",
       "Quot.sound",
       "Classical.choice"
     ]
   }
   ```

   Put both theorem names in `comparator.all-targets.json`. That configuration must fail while W is unfinished.

   Keep W’s admitted proof placeholder in `Targets/FiniteWidth.lean`, outside `Solution`’s import closure. Its statement can remain in `Challenge.lean`. Do not whitelist `sorryAx`, add submitted `external_kernels`, or turn an expected comparator failure into a successful proof badge.

   Copy the existing CI, including its Linux comparator job. During scaffolding, a red comparator is accurate. Alternatively, make that job manually triggered until the family proof is ready, with the README explicitly saying it has not passed.

4. **Create the statements of record exactly, then freeze their correspondence.**

   The following draft **was elaborated successfully against the pinned installation**, with only the two expected `sorry` warnings:

   ```lean
   module

   public import Mathlib.Algebra.MvPolynomial.Basic
   public import Mathlib.Algebra.MvPolynomial.Eval
   public import Mathlib.Algebra.Polynomial.Basic
   public import Mathlib.Algebra.Polynomial.AlgebraMap
   public import Mathlib.Algebra.Module.SpanRank
   public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
   public import Mathlib.Algebra.GCDMonoid.Finset
   public import Mathlib.Data.Nat.GCD.Basic
   public import Mathlib.Order.Monotone.Basic
   public import Mathlib.Algebra.Group.Submonoid.Basic

   @[expose] public section

   namespace FiveGenBetti

   noncomputable def toricIdeal
       (K : Type*) [Field K] (n : Fin 5 → ℕ) :
       Ideal (MvPolynomial (Fin 5) K) :=
     RingHom.ker
       (MvPolynomial.aeval
         (fun i => (Polynomial.X : Polynomial K) ^ n i)).toRingHom

   def familyGens (k q : ℕ) (i : Fin 5) : ℕ :=
     let m := 2 * k * q + 1
     match i.val with
     | 0 => m
     | 1 => m + 1
     | 2 => m + k
     | 3 => m + (2 * k - 1)
     | _ => m + 2 * k

   def MinimallyGenerates (n : Fin 5 → ℕ) : Prop :=
     ∀ i : Fin 5,
       n i ∉ AddSubmonoid.closure (n '' {j | j ≠ i})

   theorem family_spanRank_eq
       (K : Type*) [Field K] (k q : ℕ)
       (hk : 3 ≤ k) (hq : k - 1 ≤ q) :
       (toricIdeal K (familyGens k q)).spanRank =
         (4 * k + 2 : ℕ) := by
     sorry

   theorem beta1_five_le_two_width_add_two
       (K : Type*) [Field K] (n : Fin 5 → ℕ)
       (hpos : 0 < n 0)
       (hmono : StrictMono n)
       (hgcd : Finset.univ.gcd n = 1)
       (hmin : MinimallyGenerates n)
       (hwlo : 4 ≤ n 4 - n 0)
       (hwhi : n 4 - n 0 ≤ 40) :
       (toricIdeal K n).spanRank ≤
         (2 * (n 4 - n 0) + 2 : ℕ) := by
     sorry

   end FiveGenBetti
   ```

   `Solution.lean` should follow the template convention: repeat the relevant definitions and theorem statement, import the development library, and **not import `Challenge`**. Avoid defining the same public names in the imported library; use internal names such as `toricKer` and `Family.gens`.

   In `CORRESPONDENCE.md`, verify:

   - The wildcard in `familyGens` denotes index 4 because its domain is `Fin 5`.
   - `m + (2*k - 1)` has the intended value under `hk`.
   - The closure hypothesis is equivalent to absence of an expression using the other generators. Prove this equivalence, not merely one direction.
   - Strict monotonicity makes `n 0` the multiplicity and prevents width subtraction from truncating.
   - Positivity and gcd one give a numerical semigroup.
   - `spanRank` is a cardinal; the natural-number right side is coerced into that cardinal universe.
   - `K : Type*` permits arbitrary field universes and arbitrary characteristic.

   For the family, separately prove positivity, strict monotonicity, gcd one, and minimality. Consecutive generators give gcd one. The inequality \(n_4<2n_0\) gives minimality once distinctness is established.

5. **Port the generic infrastructure and both bridges before specializing the counting.**

   A practical generic structure preserving the existing fiber bounds is:

   ```lean
   structure GenData (e : ℕ) where
     n : Fin e → ℕ
     m : ℕ
     maxGen : ℕ
     m_pos : 0 < m
     lower : ∀ i, m ≤ n i
     upper : ∀ i, n i ≤ maxGen
   ```

   Keep ordering, gcd and minimality outside this structure. The five-generator constructor uses `m := n 0` and `maxGen := n 4`.

   Retain:

   ```lean
   def nu (z : Fin e → ℕ) : ℕ := ∑ i, z i * G.n i

   def fiber (d : ℕ) : Finset (Fin e → ℕ) :=
     (Fintype.piFinset fun _ => Finset.range (d / G.m + 1)).filter
       (fun z => G.nu z = d)

   def cutoff : ℕ := G.maxGen * ∑ i, G.n i
   ```

   Port `compSupp_disjoint`, `compSupp_nonempty`, `nu_replace`, `reachable_of_bridge`, and the cutoff proof. Preserve the bounded sum defining `betaFiber`.

   **Do not evaluate that Cartesian-box fiber definition in the computational checker.**

   In `BridgeUpper.lean`, port the existing proofs through:

   ```lean
   theorem spanRank_toricKer_le_betaFiber
       (K : Type*) [Field K] :
       (G.toricKer K).spanRank ≤ (G.betaFiber : Cardinal)
   ```

   Extract a reusable lemma from the coefficient-sum portion:

   ```lean
   theorem toricKer_le_ideal_of_mono_sub_mem
       (J : Ideal (MvPolynomial (Fin e) K))
       (h :
         ∀ z z', G.nu z = G.nu z' →
           mono K z - mono K z' ∈ J) :
       G.toricKer K ≤ J
   ```

   The exact elaboration of these new signatures remains implementation work.

   For `BridgeLower.lean`, I recommend a **component-charge map**, avoiding a full quotient-isomorphism development initially.

   For every \(d\le H\), let
   \[
   V_d=\{v:\operatorname{Comp}(d)\to K:\sum_Cv_C=0\}.
   \]
   Map \(f\in I\) to its coefficient sum on each component, degree by degree.

   Prove:

   - `componentCharge_sum_eq_zero`: follows from the existing `coeff_sum_eq_zero`.
   - `componentCharge_X_mul`: multiplication by any variable annihilates the charge. At each degree, all terms containing that variable lie in one component.
   - `componentCharge_mul`: multiplication by \(p\) acts by the constant coefficient \(p(0)\).
   - `componentCharge_surjective`: representative differences realize the vectors \(e_C-e_{C_0}\).
   - `componentCharge_finrank`: the target has dimension \(\sum_d(c_d-1)\), treating empty fibers separately.
   - `betaFiber_le_spanRank_toricKer`.

   Thus any ideal generating set maps to a \(K\)-spanning set of a vector space of dimension `betaFiber`. This proves the lower bound for **arbitrary polynomial generators**, not just binomials.

   Useful APIs verified in this checkout include:

   ```text
   Submodule.exists_span_set_card_eq_spanRank
   Submodule.FG.exists_span_finset_card_eq_spanFinrank
   Submodule.spanRank_map_le
   Submodule.spanRank_range_le
   Submodule.spanRank_top
   ```

   The charge map is semilinear for evaluation at zero \(K[x]\to K\); this fits the semilinear span-rank API. Universe lifts may be necessary.

   Finish with:

   ```lean
   theorem spanRank_toricKer_eq_betaFiber
       (K : Type*) [Field K] :
       (G.toricKer K).spanRank = (G.betaFiber : Cardinal)
   ```

   This is substantial new work. Budget **5–10 person-days**, not an assured two-day port.

6. **Prove certificate soundness and land the first small instance.**

   Use natural-number arithmetic in the initial Lean checker. Delay packed-byte decoding and machine-integer refinement until the mathematical checker is proved.

   Define:

   ```text
   AperyCertificate
   decodePredecessors
   reconstructApery
   validAperyCertificate
   semigroupMember
   candidateDegrees
   supportGraph
   componentCount
   checkedBeta
   ```

   A parent label should have type `Fin 4`, decoded to generator index `label.val + 1`. Reconstruct parent residues using

   ```text
   (r + m - (n_j % m)) % m
   ```

   **Do not use natural subtraction `r - n_j` before taking the modulus.**

   Use a fuel-bounded traversal of at most \(m\) steps to reject nonzero cycles and reconstruct values. The certificate must establish every residue’s path to zero.

   Soundness declarations should include these contracts:

   ```lean
   theorem validCertificate_aper y_minimal ... :
       ∀ r, A r ∈ generatedMonoid n ∧
         A r % m = r.val ∧
         ∀ x, x ∈ generatedMonoid n →
           x % m = r.val → A r ≤ x
   ```

   Name this declaration `validCertificate_apery_minimal` in the source; the contract is what matters.

   ```lean
   theorem mem_generatedMonoid_iff_apery_le ... :
       x ∈ generatedMonoid n ↔
         A ⟨x % m, Nat.mod_lt _ hm⟩ ≤ x

   theorem contributes_mem_candidates ... :
       G.contributes d → d ∈ candidateDegrees n A

   theorem supportGraph_components_equiv ... (hd : 0 < d) :
       (G.nabla d).ConnectedComponent ≃
         (supportGraph n A d).ConnectedComponent

   theorem checkedBeta_eq_betaFiber ... (hv : valid ... = true) :
       checkedBeta n cert = G.betaFiber
   ```

   These are interface drafts, not checked declarations.

   Necessary details:

   - The membership lemma uses `n 0 = m`, so adding multiples of \(m\) preserves attainability.
   - Vertices require `n i ≤ d` before testing `d - n i`.
   - Edges require `i ≠ j` and `n i + n j ≤ d` before testing subtraction.
   - The incidence-graph correspondence requires \(d>0\). At zero, the factorization graph has one vertex while the support graph is empty; both contributions are zero.
   - Candidate completeness says every *contributing* degree occurs. It does not require every candidate to contribute.
   - Deduplicate candidate degrees before summing.

   For `Examples/Thirteen.lean`, use:

   ```text
   n = [13,14,16,18,19]
   A = [0,14,28,16,30,18,19,33,34,35,36,37,38]
   predecessor indices for residues 1..12:
       [1,1,2,2,3,4,4,3,4,3,4,4]
   ```

   During this audit, ordinary Lean `decide` successfully checked all residue equations, predecessor value equations and closure inequalities for this certificate. `#print axioms` returned only `propext`.

   Separately, Python computed:

   ```text
   distinct candidates: 33
   contributing degrees: 32,42,44,47,49,52,53,54,55,56,57
   betaFiber: 14
   ```

   The Python count is **not yet a Lean theorem**.

   First prove:

   ```lean
   theorem thirteen_spanRank_le_fourteen
       (K : Type*) [Field K] :
       (toricKer K ![13,14,16,18,19]).spanRank ≤ (14 : ℕ)
   ```

   After the reverse bridge, upgrade to equality.

   Use ordinary `decide` only for the explicit checker result and finite arithmetic. Prove the field-independent theorem by applying soundness and the bridge. Record wall time, peak memory, proof artifact size and independent-kernel replay. The proposed ten-minute/2-GB cap is a benchmark gate, not a prediction.

7. **Replace four-generator singleton and split counting with the correct statements.**

   Here “singleton” must mean **component support of cardinality one**. It must not mean merely a component containing one factorization.

   Port critical-exponent results including:

   ```text
   crit_spec
   exists_alt
   compSupp_critVertex
   degree_eq_of_singleton_comp
   comp_eq_critVertex
   two_le_crit
   ```

   Replace the cyclic `succ_ne` proof by existence of a distinct index under `2 ≤ e`.

   Do not port:

   ```text
   ncomp_sub_one_le
   sigma_le_four
   beta1_eq = sigma + P + Q + E
   ```

   The failure begins at `ncomp_sub_one_le`, whose proof excludes \(1+2+2\).

   Define `bettiDegrees` as the contributing degrees below the cutoff. Define `singletonCount`, `nonsingletonCount`, `p` and `N` only over that finite set. Counting `t_d=0` over all degrees would include infinitely many irrelevant degrees.

   Required chain:

   ```lean
   theorem singletonCount_eq_critIndices_card
       (hd : G.contributes d) :
       G.singletonCount d = (G.critIndices d).card

   theorem sum_singletonCount_eq :
       ∑ d ∈ G.bettiDegrees, G.singletonCount d = e
   ```

   Then, for `G : GenData 5`:

   ```lean
   theorem nonsingletonCount_le_two
       (hd : G.contributes d) :
       G.nonsingletonCount d ≤ 2

   theorem betaFiber_add_p_eq :
       G.betaFiber + G.p = 5 + G.N

   theorem p_le_two : G.p ≤ 2

   theorem betaFiber_bound_iff (w : ℕ) (hw : 4 ≤ w) :
       G.betaFiber ≤ 2*w + 2 ↔
         G.N ≤ 2*w - 3 + G.p
   ```

   Prove `2*p ≤ 5` first: each contributing degree with no nonsingleton support consumes at least two of the five singleton supports.

   For pair components, replace `IsSplit` with:

   ```lean
   def HasPairComponent (d : ℕ) (K : Finset (Fin e)) : Prop :=
     G.contributes d ∧ K.card = 2 ∧
       ∃ C : (G.nabla d).ConnectedComponent, G.compSupp C = K
   ```

   Prove existence of a factorization with support exactly `K`, using the existing pair-support argument. Then prove:

   ```lean
   theorem pairComponent_antichain
       (h : G.HasPairComponent d K)
       (h' : G.HasPairComponent d' K)
       (hne : d ≠ d') :
       ¬ G.sel d K ≤ G.sel d' K
   ```

   The replacement proof needs no full-support representative of the other component. If \(u\le v\), replace \(u\) inside \(v\) by any factorization in another component. The nonzero residual connects the result to the later pair component, while the replacement introduces a coordinate outside its exact support.

   This works for all three types:

   | Type | Labeled patterns |
   |---|---:|
   | \(2+2+\) unused | 15 |
   | \(2+3\) | 10 |
   | \(1+2+2\) | 15 |

   Pattern counts can be checked by finite `decide` after defining a precise encoding. The structural proofs should not depend on those counts.

   The small example gives a useful regression: Python found `sigma = 8 > 5`, `p = 0`, `N = 9`, and total singleton count 5. Degree 44 exhibits \(2+2+\) unused; degree 32 exhibits \(1+2+2\).

8. **Formalize the family through explicit monomial normal forms, then prove minimum cardinality.**

   I recommend changing the generation proof’s dependency order. The direct normal-form route is more concrete than first developing general semigroup-ring quotient dimensions. It also delivers the requested Apéry and dimension statements afterward.

   **Definitions and membership.** Use an indexed family rather than a finset of polynomials initially:

   ```lean
   abbrev HIndex (k : ℕ) :=
     Fin 4 ⊕ (Fin (k - 1) ⊕ Fin (k - 1))

   abbrev NIndex (k : ℕ) := Fin k ⊕ Fin k
   ```

   `HIndex` indexes the four initial relations and the two \(k-1\) families. Its cardinality is \(2k+2\) under `hk`.

   Define the polynomial functions `HquadOrEnd`, `Hleft`, `Hright`, and `Nrel` using the displayed formulas. For `Nrel`, the split index avoids awkward subtraction by \(2k\):

   \[
   \begin{aligned}
   N^{(0)}_r&=
   cd^{k-1-r}e^{q+1+r-k}-a^{q+2-r}b^r,\\
   N^{(1)}_s&=
   d^{k-1-s}e^{q+2+s-k}-a^{q+1-s}b^sc,
   \qquad r,s<k.
   \end{aligned}
   \]

   These correspond to original indices \(r\) and \(k+s\).

   **Natural subtraction is a real correctness hazard.** At \(q=k-1\),

   ```lean
   q - k + 1
   ```

   equals 1, whereas the intended exponent is 0. Use `q + 1 + r - k`, and establish subtraction bounds before rewriting.

   Define:

   ```text
   familyRelations
   familyIdeal := Ideal.span (Set.range familyRelations)
   relationDegree
   ```

   Prove:

   ```text
   H_card
   N_card
   familyRelations_card
   H_weightedHomogeneous
   N_weightedHomogeneous
   H_mem_toricKer
   N_mem_toricKer
   familyIdeal_le_toricKer
   ```

   Work with exponent vectors first. Prove weight identities in `ℕ` or `ℤ`, then use `mono_sub_mem_toricKer`. Do not expect `ring` to resolve truncated subtraction.

   **Normal forms and their count.** Define a finite tagged type `NormalForm k q` representing exactly the four families (A). Keep the tags until injectivity of the exponent-vector map is proved.

   Establish:

   ```text
   normalOffset_lt_m
   normalOffset_injective
   normalOffset_surjective
   normalOffsetEquiv : NormalForm k q ≃ Fin (2*k*q+1)
   card_normalForm
   ```

   The offsets are:

   \[
   i+2kj,\quad k+i+2kj,\quad 2k(t+j)-t,\quad k+2k(t+j)-t.
   \]

   They partition \(0,\ldots,2kq\). Splitting by residue modulo \(2k\) gives a direct inverse. This proves the count without triangular-number division or fragile natural subtraction.

   **Generation.** Prove the stronger normal-form lemma:

   ```lean
   theorem monomial_normal_form
       (hk : 3 ≤ k) (hq : k - 1 ≤ q)
       (z : Fin 5 → ℕ) :
       ∃ (ell : ℕ) (u : NormalForm k q),
         mono K z -
           MvPolynomial.X 0 ^ ell * normalMono K u
             ∈ familyIdeal K k q
   ```

   Use strong induction on weighted degree whenever a reduction introduces \(a\). The remaining reductions terminate by eliminating \(b\), then reducing the \(d\)-exponent.

   Explicit obstruction lemmas should handle:

   - `c²`, `bd`, and `b^k`: introduce a positive power of \(a\).
   - Excessive \(b^ice^j\): use the appropriate first \(H\)-family.
   - Excessive \(b^ie^j\), \(i≥2\): use the second \(H\)-family.
   - \(be^{k-1}\): replace by \(cd^{k-1}\), removing \(b\).
   - \(d^k\): replace by \(ce^{k-1}\); a second replacement creates \(c^2\).
   - Remaining excessive \(d^te^j\): divide by \(U_{2k-1-t}\).
   - Remaining excessive \(cd^te^j\): divide by \(U_{k-1-t}\).

   The last two replacements introduce \(a\), including at the boundary.

   Distinct normal forms have distinct residues modulo \(m\). Therefore two equal-weight monomials reduce to the same \(a^\ell A\). Apply `toricKer_le_ideal_of_mono_sub_mem` to conclude:

   ```lean
   theorem familyIdeal_eq_toricKer ... :
       familyIdeal K k q = toricKer K (Family.gens k q)
   ```

   This uses the existing library’s coefficient-sum argument and avoids quotient dimension infrastructure on the critical path.

   **Apéry and the requested dimension statements.** Now prove:

   ```text
   normalWeight_is_apery
   apery_eq_normalWeights
   card_apery
   familyIdeal_sup_a_eq_toricKer_sup_a
   quotient_basis_normalForms
   quotient_finrank_eq_m
   ```

   Minimality in each residue follows because every semigroup expression reduces to \(a^\ell A\), hence its weight is at least that of \(A\).

   The quotient theorem has the intended form:

   ```lean
   Module.finrank K
     (MvPolynomial (Fin 5) K ⧸
       (familyIdeal K k q ⊔
         Ideal.span {MvPolynomial.X 0})) =
     2*k*q + 1
   ```

   Construct the finite basis or `FiniteDimensional` instance before using finrank comparisons. `finrank` alone is unsafe as evidence of finite dimension.

   If Claude retains the original dimension-first proof, it needs additional lemmas proving the Apéry quotient basis, finite-dimensional surjection equality, and homogeneous coefficient selection. Both routes are valid objectives; do not implement both merely to imitate the sketch. Record the chosen dependency change in `CORRESPONDENCE.md`.

   **Minimality and the cardinal lower bound.** First prove weighted-component selection for ideal membership. The verified Mathlib APIs include:

   ```text
   MvPolynomial.IsWeightedHomogeneous
   MvPolynomial.weightedHomogeneousComponent
   MvPolynomial.sum_weightedHomogeneousComponent
   MvPolynomial.weightedHomogeneousComponent_mem_of_mem
   ```

   Then prove:

   ```text
   H_nonredundant
   psi_H_eq_zero
   psi_N_formula
   N_not_mem_span_other_relations
   H_degree_lt_D_of_k_le_q
   H_boundary_collisions
   H_not_mem_span_other_relations
   familyRelations_nonredundant
   ```

   The monomial-map identity should be explicit:

   \[
   \psi(N_r)=s^{q+1}t^r(t^m-s)\ne0.
   \]

   Its nonvanishing is characteristic-independent.

   For \(H\), prove linear independence of the two quadratics, then the disjoint-support statement for the degree-\(k\) images modulo \((a,c^2,bd)\). At \(q=k-1\), isolate precisely the collisions at \(D\) and \(D+k-1\); weighted-component selection permits only the matching scalar \(N_r\), and \(\psi\) forces that scalar to vanish.

   In `GradedGenerators.lean`, prove the missing general bridge:

   ```lean
   theorem spanRank_eq_card_of_weightedHomogeneous_irredundant
       {σ ι : Type*} [Fintype σ] [Fintype ι]
       (K : Type*) [Field K]
       (w : σ → ℕ) (hpos : ∀ i, 0 < w i)
       (I : Ideal (MvPolynomial σ K))
       (f : ι → MvPolynomial σ K) (deg : ι → ℕ)
       (hhom : ∀ j, (f j).IsWeightedHomogeneous w (deg j))
       (hgen : Ideal.span (Set.range f) = I)
       (hirr : ∀ j, f j ∉ Ideal.span (f '' {i | i ≠ j})) :
       I.spanRank = (Fintype.card ι : Cardinal)
   ```

   This signature is proposed, not compiled.

   Prove it through \(I/\mathfrak m I\). Generator classes span; weighted nonredundancy makes them independent; every arbitrary ideal generating set maps to a spanning set. Do not apply a local-ring Nakayama theorem directly to the polynomial ring.

   This lemma can complete the family equality independently of the full reverse fiber bridge. The latter remains a separate library deliverable.

9. **Make the day-one scaffold build, then discharge holes in a controlled order.**

   On day one:

   - Implement genuine definitions, including the checker data and all relation formulas.
   - Admit proof lemmas with `by sorry`.
   - Include the full dependency chain through `Family.Main`.
   - Put W’s unproved target in `Targets/FiniteWidth.lean`.
   - Keep `Solution`’s family wrapper admitted until its dependencies are proved.
   - Do not use `sorry` to fabricate computational data or definitions.

   Run:

   ```sh
   python3 scripts/check-lean-sources.py
   ruby scripts/validate-formalization.rb
   lake build
   lake env lean Targets/FiniteWidth.lean
   ```

   Discharge in this order:

   1. Generic definitions, fibers, cutoff and upper bridge.
   2. Certificate arithmetic and checker soundness.
   3. `thirteen_spanRank_le_fourteen`.
   4. Family generator properties and membership of all displayed binomials.
   5. Normal-form offset bijection and cardinality \(2kq+1\).
   6. Singleton counting and pair antichain.
   7. Component-charge lower bridge; upgrade the concrete example to equality.
   8. Family monomial reduction and generation.
   9. Apéry and quotient-basis consequences.
   10. Graded generator-cardinality lemma and reviewed family minimality.
   11. Final `Solution` wrapper and family comparator.

   Independent branches can proceed in parallel after the generic interfaces stabilize: checker proofs, family arithmetic/normal forms, and graded lower-bound infrastructure. Avoid concurrent incompatible edits to `Defs`.

   Structure `docs/PROOF.md` around the exact Lean names above. Before minimality coding begins, complete the requested review sequence:

   ```text
   adversary → written response → reviewer → independent reconstruction
   ```

   Put the family claim packet under, for example:

   ```text
   ~/aiseminar/claims/five-generator-betti-family/
   ```

   Include the false indispensability claim and its correction in the objection log. The independent reconstruction should derive the presentation argument without being told that prior reviewers accepted it.

   Maintain a separate finite-width claim packet. Store full sweep certificates outside the Lean checkout, for example:

   ```text
   ~/five-generator-betti-artifacts/sweeps/v1/
   ```

   Commit format specifications, manifests, hashes, small regression certificates and verification instructions. External hashes establish integrity, not theorem truth.

10. **Verify correspondence and proof trust separately from successful compilation.**

   `CORRESPONDENCE.md` should contain:

   - Exact informal statements and status.
   - Generator indexing and every natural-subtraction convention.
   - Minimality-as-closure equivalence.
   - Positivity, gcd and numerical-semigroup interpretation.
   - Cardinal `spanRank` and arbitrary field universes.
   - Both fiber bridges and their actual formal status.
   - A lemma-by-lemma family correspondence table.
   - The correction from indispensability to nonredundancy.
   - Certificate semantics, graph guards, zero-degree exception and coverage requirements.
   - Explicit exclusions: periodicity, complete W replay and novelty clearance.
   - Verification records with commit, command, date and outcome.

   Run lexical checks, but do not confuse them with axiom checking:

   ```sh
   rg -n '\b(sorry|admit|axiom)\b|native_decide|ofReduceBool|unsafe' \
     --glob '*.lean' --glob '!.lake/**' .
   ```

   Check the completed theorem from an import of `Solution`, never `Challenge`:

   ```lean
   module
   import Solution

   #print axioms FiveGenBetti.family_spanRank_eq
   ```

   Expected permitted axioms are only:

   ```text
   propext
   Quot.sound
   Classical.choice
   ```

   Then run:

   ```sh
   lake env leanchecker FiveGenBetti
   lake env leanchecker Solution
   lake env leanchecker --fresh Solution
   ./scripts/verify-comparator.sh
   ```

   Recheck individual project modules as well; checking the root module alone does not replay every imported project declaration. `--fresh` performs the broader replay.

   The copied comparator script requires Linux `bwrap` and invokes the toolchain’s bundled NanoDa and con-ron. Record actual outcomes. The template’s historical record does not establish that these checks have succeeded for the new project.

   Keep manual exports outside the checkout:

   ```sh
   mkdir -p /Users/ben/five-generator-betti-artifacts/replay
   lake env leanexport Solution \
     > /Users/ben/five-generator-betti-artifacts/replay/Solution.export
   ```

   Use the bundled comparator for the independent-kernel invocation rather than inventing a NanoDa configuration schema.

   The local source checker enforces module headers, no source `.lean` symlinks, 10,000 lines per Lean file, and 1,000 lines/100 KiB for `Challenge`. It does not enforce the 500-MiB submission cap. Add a separate archive-size check:

   ```sh
   git archive --format=tar HEAD | wc -c
   ```

   Ignore `.lake`, exports, bulk certificates and replay logs. A 16-GB certificate corpus cannot become a Palomar proof artifact merely by placing it behind a download link.

   For the eventual W theorem, formal periodicity remains essential. I verified the primary source: Conaway et al., Theorem 4.9, gives the minimal-presentation correspondence for \(m>w^2\); the terminal band is \(w^2<m\le w^2+w\). Confidence in that reading: **0.99**. This does not eliminate the need to formalize the theorem and certify coverage. [Primary paper](https://arxiv.org/pdf/1701.08555)

11. **Use these ranked risks to allocate the first implementation experiments.**

   | Rank | Risk | First experiment |
   |---|---|---|
   | 1 | Minimum generator cardinality is not supplied by irredundancy alone | Implement the graded quotient lower-bound lemma on a small homogeneous ideal |
   | 2 | Generic reverse bridge requires substantial linear algebra | Construct one degree’s component-charge map and prove variable multiplication kills it |
   | 3 | Family reduction and boundary subtraction may be encoded incorrectly | Prove all exponent identities at \(q=k-1\), then symbolic membership |
   | 4 | Quotient dimension APIs may consume disproportionate effort | Use direct monomial normal forms and derive the dimension theorem afterward |
   | 5 | Four-generator assumptions survive a superficial port | Replace `GenData`, `IsSplit`, and the singleton-counting tail before porting conclusions |
   | 6 | Concrete kernel evaluation may become expensive | Benchmark the 13-residue certificate and its independent replay before increasing size |
   | 7 | W has neither formal periodicity nor feasible complete kernel replay | Keep it outside the completed release; require a measured compression strategy |
   | 8 | Novelty and informal review remain unresolved | Maintain dated claim packets; make no new novelty assertion from this audit |

   A credible planning budget is **roughly 25–45 person-days** for the family, generic bridges, structural lemmas and a small sound checker, with overlap between independent branches. This is an estimate, not a guarantee. The complete finite-width theorem has no defensible completion estimate yet.

**Subagents used: 3** — independent family-proof audit; complete combinatorial-library and decomposition audit; bootstrap, statement-elaboration and verification audit. I reconciled their reports, inspected the upper bridge and Mathlib APIs, independently computed the small support graphs, and kernel-checked the small certificate’s arithmetic.

**CONFIDENCE: 0.87**