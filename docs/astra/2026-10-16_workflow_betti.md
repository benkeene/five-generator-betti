<!-- astra: model=gpt-6-astra effort=high status=completed thread=01a146d3-856f-7e10-b22a-1c47880b786e job=20261016T182709_workflow-five-generator-linear-betti-bound -->

Dated audit: **2026-10-16**. I found no primary source establishing the proposed five-generator linear bound or the exact family formula. This supports investigation, not a definitive novelty claim.

**Periodicity reduction is valid, with a citation correction.** Conaway–Gotti–Horton–O’Neill–Pelayo–Williams–Wissman, *Minimal presentations of shifted numerical monoids*, IJAC 28 (2018), 53–68, Theorem 4.9, proves a cardinality-preserving bijection of minimal presentations for
\[
M_m=\langle m,m+a,m+b,m+c,m+w\rangle
\quad\longrightarrow\quad M_{m+w}
\]
when **\(m>w^2\)**. Therefore every \(m>w^2+w\) reduces to its unique representative in \(w^2<m'\le w^2+w\), proving that testing \(1\le m\le w^2+w\) suffices. The theorem assumes primitive, minimal generators. Both hold along this high-multiplicity reduction: all generators lie below \(2m'\), and their gcd is unchanged under subtracting \(w\). Cite **Theorem 4.9**, not merely Corollary 5.2: the latter counts distinct Betti elements, which need not equal total \(\beta_1\). Confidence **0.99**. [Primary paper](https://arxiv.org/pdf/1701.08555), [journal DOI](https://doi.org/10.1142/S0218196718500030).

Do **not** discard offset vectors with \(\gcd(a,b,c,w)>1\). Primitivity requires \(\gcd(m,a,b,c,w)=1\), not primitive offsets. No normalization by dividing just the offsets has been justified.

**Current general status.** Moscariello–Sammartano’s survey, updated **28 September 2026**, still lists the general width bound \(\rho(S)\le\binom{w+1}{2}\) and its higher-Betti analogues as problems; its width section does not give the requested five-generator linear result. Caviglia–Moscariello–Sammartano prove general subexponential-in-width bounds and the quadratic conjecture for embedding dimension four at width at least 40. These results do not close this target. Confidence **0.98** in this reading; **0.75** that no narrower matching five-generator result has been published. [Updated survey, §3](https://arxiv.org/html/2406.00790v3), [CMS paper, arXiv:2307.05770](https://arxiv.org/abs/2307.05770), [DOI](https://doi.org/10.1090/proc/16862).

**Family audit.**

- The proposed offsets \(\{0,1,k,2k-1,2k\}\), \(k\ge3\), contain **no four-term arithmetic progression**. This is an elementary check of the five possible deletions. Consequently the standard almost-arithmetic-sequence presentation formulas, whose hypotheses require all but one generator to form an arithmetic progression, do not apply directly. See the explicit hypotheses in §1 of [Al-Ayyoub’s corrected Gröbner-basis treatment](https://arxiv.org/pdf/math/0411372). Caution: its introductory wording contains an apparent indexing slip; §1 makes the intended hypothesis explicit.
- The recent [*Numerical Semigroups of Sally Type*](https://arxiv.org/html/2507.11738v2) determines presentations for intervals with two omitted generators and width equal to multiplicity minus one. It supplies known small-multiplicity comparison cases, not this proposed tail.
- Singh–Srinivasan’s [*Structure and Symmetry of Sally Type Semigroup Rings*](https://arxiv.org/html/2512.18136v1) likewise concerns width \(m-1\), including intervals with consecutive deletions. Our family has \(2k<m-1\) throughout the stated range, so it is outside those hypotheses. The paper’s Theorem 2.3 recalls a useful **Gastinger criterion**: for a weighted homogeneous binomial ideal \(J\subset I_S\), proving
  \[
  \dim_K K[x_0,\ldots,x_4]/(J,x_0)=m
  \]
  suffices to prove \(J=I_S\). An explicit Apéry basis could make this the shortest family-presentation proof. Minimality still requires its own argument.

Search terminology included “almost arithmetic sequence,” “arithmetic progression with gaps,” “minimal presentation,” “shifted numerical monoids,” five generators, linear width bounds, and the exact offset expressions. I did not find a matching family theorem. **Confidence that the family result is new: 0.70**; this remains the weaker part of the audit. An indexed absence is not proof of novelty.

Suggested status sentence:

> What appears to remain unknown is exactly whether every minimally five-generated numerical semigroup of widths \(4\le w\le40\) satisfies \(\beta_1\le2w+2\), what its complete equality cases are, and whether the displayed two-parameter family has \(\beta_1=4k+2\) for every stated \(m,k\).

Classification:

| Statement | Status |
|---|---|
| Periodicity and finite multiplicity reduction | Established theorem |
| Archived \(w\le20\), omitting low multiplicities | KNOWN COMPUTATION, repository observation only |
| Complete maxima/equality cases through width 40 | UNKNOWN FINITE VALUE / UNKNOWN CLASSIFICATION, provisional |
| All-width five-generator linear bound | OUR PROPOSED NEW CONTRIBUTION; unproved conjecture |
| Uniform family presentation and equality formula | OUR PROPOSED NEW CONTRIBUTION; novelty provisional |

I read the survey’s e6/e7 audit and agree with its certification objection: verifying extremizers plus samples cannot certify an upper bound. The trimmed e6 campaign can be an independently budgeted companion, but its literature reduction and complete replay must pass the same gates.

All linked sources accessed **2026-10-16**. No writes or computations performed. **0 additional subagents** used within this delegated literature branch.

The existing sweeper is mathematically plausible, but its current verification does not certify exhaustive maxima. The repaired workflow can retain complete certificates within the disk budget by storing **packed predecessor trees**, rather than Apéry arrays.

### Exact certificate and independent checker

For generators \(n_0=m<n_1<\cdots<n_4\), a certificate stores, for every residue \(r\ne0\), a choice \(j(r)\in\{1,2,3,4\}\). This requires two bits per residue. Define
\[
p(r)=(r-n_{j(r)})\bmod m.
\]
The verifier independently:

1. Checks the input domain, gcd, and minimality.
2. Checks that the parent graph is a tree directed toward residue \(0\): no nonzero cycle, every chain reaches \(0\).
3. Reconstructs
   \[
   A_0=0,\qquad A_r=A_{p(r)}+n_{j(r)}.
   \]
4. Checks every residue congruence and every closure inequality
   \[
   A_{(r+n_i)\bmod m}\le A_r+n_i.
   \]
5. Constructs the entire candidate set \(C=\{n_i+A_r\}\), deduplicating independently with sorting.
6. For every \(d\in C\), reconstructs the generator-support graph
   \[
   V_d=\{i:d-n_i\in S\},\quad
   ij\in E_d\Longleftrightarrow d-n_i-n_j\in S
   \]
   using \(x\in S\iff x\ge0\land x\ge A_{x\bmod m}\).
7. Counts components with a five-vertex bitset traversal, rather than the searcher’s union–find, and computes \(\sum_d\max(c_d-1,0)\).

**Proof of Apéry correctness.** The tree supplies attainability of every \(A_r\). Closure, by induction along any expression of an element of \(S\), proves \(A_r\) is no larger than any element of \(S\) in residue \(r\). Thus these are exactly the Apéry entries. This verifier need not run a shortest-path algorithm.

**Proof of candidate completeness.** Suppose \(d\notin C\), but \(d-n_i\in S\). Then \(d-n_i\notin\operatorname{Ap}(S,m)\), so \(d-n_i-m\in S\). Consequently every present generator vertex is connected to vertex \(0\); the graph is connected. Therefore every disconnected degree belongs to \(C\).

**Proof of graph correspondence.** For \(d>0\), consider the incidence graph between factorizations of \(d\) and generator indices in their supports. Factoring through either side gives respectively the factorization graph and the generator-support graph, with identical connected components. Treat \(d=0\) separately.

These three short lemmas should be independently reviewed and formalized before trusting the checker.

### Coverage, size, and boundary defects

The raw domain \(4\le w\le40\), \(2\le m\le w^2+w\), \(0<a<b<c<w\), contains:

- **104,824,330** parameter instances before gcd/minimality filters.
- **66,861,198,170** Apéry entries, counting one length-\(m\) array per instance.

Full 64-bit Apéry arrays would occupy **534.9 GB**. Packed predecessor choices need at most **16.72 GB**, before filters and modest record padding. A four-byte per-instance Betti ledger adds **0.42 GB**. Therefore a **40 GB retained-output cap** is credible for packed complete certificates, subject to a measured framing/compression benchmark.

The verifier must enumerate the parameter domain independently; it must not trust the searcher’s task list. It should confirm every expected lexicographic slot exactly once, independently validate skipped slots, and check that prefix tasks form a disjoint complete partition. Checksums and `.done` markers provide integrity and scheduling, not coverage proofs.

For low multiplicities, test minimality exactly. For each \(n_j\), only smaller generators can represent it, so a small incremental coin-reachability DP suffices. For \(m>w\), every generator is less than \(2m\), so minimality is automatic. The archived lower cutoff \(w+2\) unnecessarily excludes \(m=w+1\), as well as the genuinely nontrivial low range. Five-generated numerical semigroups necessarily have \(m\ge5\), but using a wider raw domain and independently rejecting nonminimal tuples is harmless.

Specific defects discovered:

- The archived e5 README says **1,366,267** instances in prose; its table and task-pool reproduction say **1,371,247**. Reconcile from archived records.
- Current code tests violations against \(\binom{w+1}{2}\), not \(2w+2\). All reporting and stop conditions must change.
- Current `--stdin` does not reject gcd \(>1\). Unreachable Apéry entries remain `INT64_MAX`, so later additions can overflow. Validate gcd before calling it.
- `worker.sh` stale-claim takeover has a remove/recreate race; one reclaimer can remove another’s new claim. An `squeue` failure is also interpreted as dead ownership. Fix takeover or make duplicate execution harmless through immutable, validated task outputs.
- `beta1_ref_e.py` is separately written but uses essentially the same Dijkstra/graph method. It is useful, but the predecessor/closure checker supplies a clearer independent correctness boundary.

The tree certificate also gives the safe bound \(A_r\le(m-1)n_4\). Here \(m\le1640\), \(n_4\le1680\), so reconstructed entries and candidate degrees fit comfortably in unsigned 32-bit arithmetic; use wider checked arithmetic for intermediate calculations.

### Structural information the sweep must retain

The proposed “2+3 split” omits a real case.

**Proved elementary lemma:** if a disconnected five-generator fiber has no singleton component, it has exactly two components, with actual support sizes either:

- \(2+3\), covering all five generators; or
- \(2+2\), leaving one generator unused.

There are **10 labeled 2+3 patterns** and **15 labeled 2+2-plus-unused patterns**. Padding the unused coordinate into a triple does not satisfy the existing library’s `IsSplit`, whose component supports equal complementary sets.

Moreover, a component with three-element support need not contain a single factorization using all three generators. Connectedness of its support graph does not imply such a factorization. The four-generator pair-support lemma cannot simply be copied.

For every retained structural record, include:

- Degree, vertex mask, edge mask, component masks, unused mask.
- One explicitly verified factorization per component.
- A spanning tree between components, giving the \(c_d-1\) presentation binomials.
- Critical exponents and alternative factorizations.
- For triple components, a small connecting collection of factorizations; do not silently assume a full-support representative.
- Along each fixed offset tuple, the exact multiplicities where the signature changes, with degree/exponent differences across successive multiplicities and period-\(w\) shifts.

For all instances, the checker reconstructs component counts itself. Retaining every candidate count would destroy the compact storage estimate. Retain complete packed Apéry certificates and the Betti ledger; retain expanded presentations for all extremizers, violations, transition representatives, and each new support signature.

### Laptop and cluster implications

Use complete e5 widths \(4\!:\!20\), all omitted low multiplicities, then \(21\!:\!30\), with certificate checking throughout. Include \(\langle3,5,7\rangle\), whose first Betti number is \(3\), and \(\langle4,6,9\rangle\), whose value is \(2\), as generic checker regressions. Use e5 arithmetic-progression examples independently checked by GAP/Singular.

Add adversarial certificate tests: corrupted parent bits, nonzero cycles, wrong roots, closure failure, missing residue, omitted/duplicated parameter slot, and forged skip classifications. A checker that merely reproduces valid certificates is insufficiently tested.

Measure search, certificate writing, and complete verification separately at widths \(20,25,30\), including slow offset-prefix strata. Report seconds per task, RSS, raw/compressed disk, and effective node1-equivalent core-hours. The historical 1–5 core-hour search forecast excludes richer recording and complete verification.

Task decomposition should use width, offset prefix, and—if needed—multiplicity interval, with both measured time and output-size caps. Suggested initial targets: **10–30 minutes per task**, **≤256 MB certificate per task**, **≤1 GB RAM**, and a separate verifier pool. Store temporary outputs on `/scratch`; publish certificates atomically to `/shared` only after completion. Publish a separate verified marker after independent checking.

The existing node measurements show node2 delivering about **0.27 node1-equivalent work per core-hour**. Do not count physical core-hours from both nodes equally.

### e6 decision

The survey establishes the relevant scope correction: widths **40–44** are already covered by the compressed-algebra bound at the periodicity-window maximum. Restrict e6 to widths **5–39** and multiplicities not covered by an independently audited algebraic bound.

Run this only as a separately budgeted secondary campaign, after the e5 checker and census pass. Its contribution is completion of the quadratic-bound case, not evidence for the five-generator linear theorem. Algebraically skipped instances cannot yield exact e6 maxima or extremizer classifications.

The trimmed e6 certificate volume must be measured separately: five possible predecessor generators require three bits, and the untrimmed parameter space is much larger. Do not silently charge it to the e5 40 GB cap. Reject the present month-scale e7 campaign.

### Lean statement and order

The intended finite-width theorem should retain the existing Mathlib formulation:

```lean
theorem beta1_five_le_two_width_add_two
    (K : Type*) [Field K] (n : Fin 5 → ℕ)
    (hpos : 0 < n 0) (hmono : StrictMono n)
    (hgcd : Finset.univ.gcd n = 1)
    (hmin : ∀ i, n i ∉ AddSubmonoid.closure (n '' {j | j ≠ i}))
    (hwlo : 4 ≤ n 4 - n 0) (hwhi : n 4 - n 0 ≤ 40) :
    (RingHom.ker
      (MvPolynomial.aeval
        (fun i => (Polynomial.X : Polynomial K) ^ n i)).toRingHom).spanRank
      ≤ (2 * (n 4 - n 0) + 2 : ℕ)
```

This is a target statement, not compiled code or a presently proved theorem.

Port in this order:

1. Generic finite-generator definitions, factorization fibers, component supports, and finite degree cutoff.
2. The existing explicit-binomial generating-set bridge \(\mu(I)\le\beta_{\mathrm{fiber}}\).
3. Apéry-certificate soundness, candidate completeness, and the five-vertex graph correspondence.
4. A single small e5 upper-bound instance using ordinary kernel `decide` for its certificate. Measure build time, proof size, and independent NanoDa replay here.
5. General singleton contribution bound \(\sigma\le5\), followed by the correct \(2+3\)/\(2+2+\mathrm{unused}\) partition.
6. The reverse bridge \(\beta_{\mathrm{fiber}}\le\mu(I)\), required for exact family equality.
7. A symbolic family proof, if the mathematics succeeds.

The existing brute-force fiber definition should not become the computational checker: it enumerates a Cartesian box of factorizations. Prove equivalence to the small support-graph calculation.

The uniform family can be parameterized as \(m=2kq+1\), \(k\ge3\), \(q\ge k-1\), with the target equality `spanRank = (4*k+2 : ℕ)`. A structural family proof avoids formalizing periodicity.

A complete computational theorem for all multiplicities additionally requires a formal periodicity reduction, absent from the existing library. Likewise, checking roughly \(10^8\) instances inside Lean is not made cheap merely by proving the checker once. The first kernel benchmark should determine whether finite certificates scale at all; prefer the short family proof or a proved transition compression for the final formal result.

I used **0 additional subagents**; this was the parent’s delegated certification, infrastructure, and Lean audit.

**PROOF_ATTEMPT: the full family formula has a short uniform proof.** It does not require another sweep. I derived the presentation independently; parent has separately audited its core counting/minimality argument. Formal adversarial review and repository promotion remain outstanding.

**Uncertainty reduced.** Does the proposed family really satisfy \(\beta _1=4k+2\) uniformly, and what accounts for its generators?  
**New statement if validated.** For every field \(K\), \(k\ge3\), \(q\ge k-1\), and \(m=2kq+1\), the toric ideal of
\[
\langle m,m+1,m+k,m+2k-1,m+2k\rangle
\]
has the following minimal presentation of cardinality \(4k+2\), and the explicit Apéry normal form below.

Write \(a,b,c,d,e\) for the five variables.

### Uniform presentation

The \(2k+2\) ordinary homogeneous binomials are
\[
c^2-bd,\quad bd-ae,\quad b^k-a^{k-1}c,\quad d^k-ce^{k-1},
\]
and, for \(0\le i\le k-2\),
\[
b^{k-1-i}ce^i-a^{k-1-i}d^{i+1},
\qquad
b^{k-1-i}e^{i+1}-a^{k-2-i}cd^{i+1}.
\tag{H}
\]

There are another \(2k\) binomials \(U_r-V_r\), \(0\le r<2k\):
\[
U_r=
\begin{cases}
cd^{k-1-r}e^{q-k+1+r},&r<k,\\
d^{2k-1-r}e^{q-2k+2+r},&r\ge k,
\end{cases}
\]
\[
V_r=
\begin{cases}
a^{q+2-r}b^r,&r<k,\\
a^{q+k+1-r}b^{r-k}c,&r\ge k.
\end{cases}
\tag{N}
\]
Their common semigroup degree is
\[
\deg_S(U_r)=\deg_S(V_r)=(q+2)m+r.
\]
Their ordinary lengths are \(q+1\) and \(q+2\), respectively. All exponents are nonnegative under \(q\ge k-1\), and every \(V_r\) is divisible by \(a\).

### Generation proof

Let \(J\) be generated by these binomials and \(I\) be the toric ideal. Every identity can be checked directly, so \(J\subseteq I\).

Modulo \(a\), the relations give a spanning set consisting of these four monomial families:
\[
\begin{array}{ll}
b^ie^j:& i\ge1,\quad i+j\le k-1,\\
b^ice^j:& i\ge1,\quad i+j\le k-2,\\
d^te^j:&0\le t\le k-1,\quad t+j\le q,\\
cd^te^j:&0\le t\le k-1,\quad t+j\le q-1.
\end{array}
\tag{A}
\]

Here is an explicit terminating reduction argument.

* First kill monomials divisible by \(c^2\) or \(bd\).
* A surviving monomial containing \(b\) has \(d=0\) and \(c\)-exponent at most one. The monomial relations obtained from \(H\) kill those outside the first two families, except for multiples of \(be^{k-1}\).
* Replace \(be^{k-1}\) by \(cd^{k-1}\). This removes \(b\); if another \(b\) remains, \(bd\) kills the result.
* For a monomial without \(b\), replace \(d^k\) by \(ce^{k-1}\). This decreases the \(d\)-exponent by \(k\); a second such replacement produces \(c^2\), hence zero.
* The images of the \(U_r\) now impose the last two bounds in (A).

The number of displayed monomials is
\[
\frac{k(k-1)}2+\frac{(k-1)(k-2)}2
+\sum_{t=0}^{k-1}(q+1-t)
+\sum_{t=0}^{k-1}(q-t)
=2kq+1=m.
\]

On the other hand, \(K[S]/(t^m)\) has dimension \(m\), with its usual Apéry basis. Therefore the surjection
\[
K[a,b,c,d,e]/(J,a)\longrightarrow K[S]/(t^m)
\]
is an isomorphism.

This also implies \(J=I\): for a weighted homogeneous \(f\in I\), equality modulo \(a\) writes \(f=j+ag\), with \(j\in J\). Since \(K[S]\) is a domain, \(g\in I\). A minimal-weight element of \(I\setminus J\) would therefore give a smaller one, a contradiction.

Consequently, the weights of the monomials in (A) are **exactly** \(\operatorname{Ap}(S;m)\), providing the desired symbolic normal form.

### Minimality proof

The \(H\)-relations comprise two quadratics and \(2k\) ordinary-degree-\(k\) relations. Modulo \(a\), the quadratics generate the monomial ideal \((c^2,bd)\). The degree-\(k\) images have pairwise disjoint supports, none divisible by \(c^2\) or \(bd\). They are therefore linearly independent modulo the degree-\(k\) consequences of the quadratics. Hence \(H\) is a minimal generating list for its ideal.

Put \(D=(q+2)m\). The \(N\)-degrees occupy \(D,\ldots,D+2k-1\), an interval shorter than the least positive semigroup element \(m\). Thus a positive monomial multiple of one \(N\)-relation cannot occur in another \(N\)-degree.

Furthermore, \(H\) preserves ordinary length. Its ideal is contained in the kernel of
\[
a,b,c,d,e\longmapsto s,\ st,\ st^k,\ st^{2k-1},\ st^{2k},
\]
which contains no monomial. Each \(N_r\), having two different ordinary lengths, has nonzero image under this map. Thus \(N_r\) cannot follow from \(H\), or from \(H\) and the other \(N\)'s.

For \(q\ge k\), every \(H\)-degree is below \(D\), so adding \(N\) cannot make an \(H\)-relation redundant.

At the boundary \(q=k-1\), exactly two \(H\)-degrees reach the \(N\)-band:
\[
be^{k-1}-cd^{k-1}\quad\text{has degree }D,
\]
\[
d^k-ce^{k-1}\quad\text{has degree }D+k-1.
\]
All other \(H\)-degrees are below \(D\), and the largest \(H\)-degree is \(D+k-1<D+m\). Only the corresponding scalar \(N\)-relation could enter a putative redundancy at either collision. Applying the displayed \(s,t\)-map forces that scalar to vanish. Minimality of \(H\) then excludes redundancy.

Thus the presentation has exactly \(4k+2\) minimal generators.

### Explicit small symbolic cases

For \(k=3\), \(m=6q+1,\ q\ge2\), the eight \(H\)-relations are
\[
c^2-bd,\ bd-ae,\ b^3-a^2c,\ b^2c-a^2d,
\]
\[
b^2e-acd,\ bce-ad^2,\ be^2-cd^2,\ d^3-ce^2.
\]
The six additional pairs \(U,V\) are
\[
\begin{array}{c|c}
cd^2e^{q-2}&a^{q+2}\\
cde^{q-1}&a^{q+1}b\\
ce^q&a^qb^2\\
d^2e^{q-1}&a^{q+1}c\\
de^q&a^qbc\\
e^{q+1}&a^{q-1}b^2c
\end{array}
\]
giving \(14\) generators.

For \(k=4\), \(m=8q+1,\ q\ge3\), the ten \(H\)-relations are
\[
c^2-bd,\ bd-ae,\ b^4-a^3c,\ d^4-ce^3,
\]
\[
b^3c-a^3d,\ b^2ce-a^2d^2,\ bce^2-ad^3,
\]
\[
b^3e-a^2cd,\ b^2e^2-acd^2,\ be^3-cd^3.
\]
The eight additional pairs are
\[
\begin{array}{c|c}
cd^3e^{q-3}&a^{q+2}\\
cd^2e^{q-2}&a^{q+1}b\\
cde^{q-1}&a^qb^2\\
ce^q&a^{q-1}b^3\\
d^3e^{q-2}&a^{q+1}c\\
d^2e^{q-1}&a^qbc\\
de^q&a^{q-1}b^2c\\
e^{q+1}&a^{q-2}b^3c
\end{array}
\]
giving \(18\) generators.

### Computed checks and fiber information

An independent, exact, in-memory Apéry/factorization enumeration returned:

| \(k\) | \(q\) | \(m\) | Computed \(\beta_1\) |
|---:|---:|---:|---:|
| 3 | 2 | 13 | 14 |
| 3 | 3 | 19 | 14 |
| 3 | 4 | 25 | 14 |
| 4 | 3 | 25 | 18 |
| 4 | 4 | 33 | 18 |

The degree of \(c^2=bd=ae\) has three components and contributes two. At \(q=k-1\), the two collision degrees above also have three components, each contributing two. The collision joins the two homogeneous-length components to a component of length \(k+1\); it does not reduce the generator count.

The normal-form and minimality proof is stronger evidence than these five computations, but it remains a **proof attempt awaiting the prescribed adversarial review**. No repository files were written.

Subagents used by this subtask: **0**; the parent already allocated the available parallel agents.

**Verdict: the new argument survives this adversarial pass.** I found no counterexample or substantive gap. It is a valid **proof sketch**, pending a complete written proof and the repository’s second independent review; this is not a status promotion.

I independently checked the delicate boundary \(q=k-1\).

1. **Relations and nonnegative exponents.** Both monomials of \(N_r\) have weighted degree \(D+r\), where \(D=(q+2)m\). Their ordinary degrees are \(q+1\) and \(q+2\). The smallest exponent \(q-k+1\) can be zero; no exponent becomes negative.

2. **Spanning modulo \(a\).** The reductions suffice. First eliminate \(c^2\) and \(bd\). Reducing \(d^k\) introduces \(c\), so a second such reduction kills the monomial. The relation \(be^{k-1}=cd^{k-1}\) removes the remaining exceptional \(b\)-monomials. The \(U_r\) then impose precisely
   \[
   d^te^{q+1-t}=0,\qquad cd^te^{q-t}=0
   \quad(0\le t<k).
   \]
   These include \(cd^{k-1}=0\) when \(q=k-1\), correctly handling the boundary.

   The four proposed spanning classes have respective sizes
   \[
   \frac{k(k-1)}2,\quad
   \frac{(k-1)(k-2)}2,\quad
   k(q+1)-\frac{k(k-1)}2,\quad
   kq-\frac{k(k-1)}2.
   \]
   Their sum is \(2kq+1=m\). The last formula remains valid at \(q=k-1\): its final \(t\)-slice is empty.

3. **Generation.** Since \(m,m+1\) are generators, the semigroup is numerical. Its quotient by \(t^m\) has dimension \(m\). Thus the spanning bound plus the surjection proves
   \[
   (J,a)=(I,a).
   \]
   For a weighted homogeneous \(f\in I\), write \(f=j+ah\), with \(j,h\) homogeneous. Cancellation of \(t^m\) gives \(h\in I\); induction on weighted degree proves \(I=J\). State the homogeneity selection explicitly.

4. **Minimality of \(H\).** The two quadratics are linearly independent. All remaining \(2k\) relations have ordinary degree \(k\). After reducing modulo \(a\) and the quadratics, their nonzero images have disjoint monomial supports in
   \[
   K[b,c,d,e]/(c^2,bd).
   \]
   Hence none belongs to the ideal generated by the remaining \(H\)-relations. This works over every field.

5. **Minimality after adding \(N\).** Use weighted-homogeneous ideal membership explicitly. The interval of \(N\)-degrees has width \(2k-1<m\), so no positive-degree polynomial multiple of another \(N\)-relation can enter a relation of degree \(D+r\). The monomial map
   \[
   (a,b,c,d,e)\mapsto(s,st,st^k,st^{2k-1},st^{2k})
   \]
   annihilates \(H\) and sends each \(N_r\) to a nonzero difference of monomials with distinct \(s\)-degrees. Thus each \(N_r\) is indispensable relative to this generating set.

   Conversely, every \(H\)-degree is below \(D+m\). Therefore only scalar multiples of matching \(N_r\) can occur in a hypothetical redundancy relation for \(H\). At \(q=k-1\), the only collisions are exactly those stated: the last \(B\) at \(D\), and \(d^k-ce^{k-1}\) at \(D+k-1\). Applying the monomial map forces that scalar to vanish. For \(q\ge k\), there are no collisions.

Consequently the sketch establishes a minimal generating set of cardinality
\[
(2k+2)+2k=4k+2.
\]
It yields \(14\) relations for \(k=3\), \(m=6q+1\), \(q\ge2\), and \(18\) for \(k=4\), \(m=8q+1\), \(q\ge3\).

The full write-up should avoid claiming unique normal forms: **spanning plus the dimension lower bound is enough**, and uniqueness has not been independently derived here. No computation or subagents were used in this adversarial pass.

My earlier claim \(\sigma\le5\), with \(\sigma\) counting all contributions from singleton-containing fibers, was **false**.

The corrected decomposition is valid. Over contributing degrees, let \(r_d\) count singleton components and \(t_d\) nonsingleton components. Each generator contributes exactly one singleton component, at its critical degree, so
\[
\sum_d r_d=5.
\]
Since \(t_d\le2\),
\[
\boxed{\beta_1+p=5+N},
\]
where \(p=\#\{d:t_d=0\}\) and \(N=\#\{d:t_d=2\}\). Moreover \(p\le2\).

The degrees counted by \(N\) have exactly these support types:

| Type | Labeled patterns |
|---|---:|
| \(2+2+\) unused generator | 15 |
| \(2+3\) | 10 |
| \(1+2+2\) | 15 |

Thus the desired bound is equivalent to
\[
N\le2w-3+p.
\]

The pair-component antichain lemma survives all three types. For a fixed pair support \(K\), select a factorization positive on both coordinates. If \(u\le v\) at distinct degrees, replace \(u\) inside \(v\) by a factorization of its degree from another component, whose support is disjoint from \(K\). The nonzero residual retains a coordinate in \(K\), while the replacement introduces one outside \(K\), contradicting that the component of \(v\) has support exactly \(K\).

The Lean port should first formalize **singleton-component counting**, then this corrected decomposition—not port `sigma_le_four` by replacing four with five.

The family is more tractable than the brief suggests: we obtained a uniform \(4k+2\)-generator presentation and a proof sketch of minimality. It survived an independent adversarial pass. Its repository status should remain **PROOF_ATTEMPT** until the full review protocol is completed.

The general upper bound still needs work. In particular, the four-generator counting argument has two additional cases in embedding dimension five: **2+2 with an unused generator**, and **1+2+2**. Ignoring the latter gives a false singleton-contribution bound.

No repository files were written or cluster jobs launched.

## 0. The two questions and the statement

**What mathematical uncertainty does the computation reduce?**

Whether every minimally five-generated numerical semigroup of width \(4\le w\le40\) satisfies \(\beta_1\le2w+2\), and which component configurations account for equality or a counterexample.

**If it succeeds, what new mathematical statement will we know?**

A computer-assisted upper bound for **all multiplicities** in those widths. Separately, validating the presentation below gives an infinite family attaining the bound at every even width \(w\ge6\).

The finite-width target is
\[
\forall K,\ \forall S=\langle n_0<n_1<n_2<n_3<n_4\rangle
\text{ minimally generated and numerical},\qquad
4\le n_4-n_0\le40
\Longrightarrow
\beta_1(K[S])\le2(n_4-n_0)+2.
\]

The computational domain is
\[
4\le w\le40,\quad
0<a<b<c<w,\quad
2\le m\le w^2+w,
\]
retaining exactly the primitive, minimally generated tuples
\[
(m,m+a,m+b,m+c,m+w).
\]
Multiplicity \(1\) cannot occur for embedding dimension five.

A verified violation refutes the proposed bound. A completed search without violations, combined with the periodicity reduction and complete independent verification, proves the finite-width statement. Neither outcome settles the all-width upper bound.

## 1. Status check

**Checked 2026-10-16.**

The multiplicity reduction is valid. Conaway et al., **Theorem 4.9**, gives a cardinality-preserving correspondence of minimal presentations when \(m>w^2\), between shifts \(m\) and \(m+w\). Thus the terminal band is
\[
w^2<m\le w^2+w.
\]
The strict inequality matters. Cite this theorem rather than only Corollary 5.2, which concerns the number of distinct Betti elements. [Primary paper, arXiv:1701.08555](https://arxiv.org/pdf/1701.08555), [DOI](https://doi.org/10.1142/S0218196718500030).

The September 2026 Moscariello–Sammartano survey does not supply the requested five-generator linear bound. The known general width estimates do not close it. The survey’s compressed-algebra calculation at \(w=40,m=1640\), even with strictness, gives \(598>82\). [Current survey](https://arxiv.org/html/2406.00790v3), [multiplicity bounds](https://arxiv.org/html/2405.19810v1).

For the family, searches covered “almost arithmetic sequence,” “arithmetic progression with gaps,” “minimal presentation,” “shifted numerical monoids,” and the exact offsets. No matching result was located. Standard almost-arithmetic hypotheses do not apply directly: the five offsets contain no four-term arithmetic progression. Recent Sally-type results concern width equal to multiplicity minus one, outside this family’s stated range. [Almost-arithmetic presentation hypotheses](https://arxiv.org/pdf/math/0411372), [Sally-type results](https://arxiv.org/html/2512.18136v1).

> **What appears to remain unknown is exactly** whether every minimally five-generated numerical semigroup of widths \(4\le w\le40\) satisfies the proposed linear bound, and its complete equality cases; the uniform family formula now has a proof attempt requiring full validation and novelty clearance.

| Item | Current classification |
|---|---|
| Periodicity reduction | Established theorem |
| Archived sweep through width 20 | KNOWN COMPUTATION; incomplete independent certification |
| Exact maxima and equality cases through 40 | UNKNOWN FINITE VALUE / UNKNOWN CLASSIFICATION |
| Proposed linear bound | OUR PROPOSED NEW CONTRIBUTION |
| Family presentation below | PROOF_ATTEMPT; novelty provisional |

Confidence in the periodicity reading: **0.99**. Confidence that the family formula is unpublished: **0.70**.

Before G0 closes, Claude should save the dated source audit and reconcile an archive discrepancy: the e5 README’s prose says **1,366,267** instances, while its table and task-pool reproduction say **1,371,247**.

## 2. Mathematics first

### A uniform family presentation

Write
\[
m=2kq+1,\qquad k\ge3,\quad q\ge k-1.
\]
Let \(a,b,c,d,e\) denote variables of weights
\[
m,\ m+1,\ m+k,\ m+2k-1,\ m+2k.
\]

**PROOF_ATTEMPT.** The following is a minimal generating set of the toric ideal.

First take the \(2k+2\) ordinary homogeneous relations
\[
c^2-bd,\quad bd-ae,\quad
b^k-a^{k-1}c,\quad d^k-ce^{k-1},
\]
and, for \(0\le i\le k-2\),
\[
b^{k-1-i}ce^i-a^{k-1-i}d^{i+1},
\qquad
b^{k-1-i}e^{i+1}-a^{k-2-i}cd^{i+1}.
\tag{H}
\]

Add \(2k\) relations \(U_r-V_r\), \(0\le r<2k\), where
\[
U_r=
\begin{cases}
cd^{k-1-r}e^{q-k+1+r},&r<k,\\
d^{2k-1-r}e^{q-2k+2+r},&r\ge k,
\end{cases}
\]
and
\[
V_r=
\begin{cases}
a^{q+2-r}b^r,&r<k,\\
a^{q+k+1-r}b^{r-k}c,&r\ge k.
\end{cases}
\tag{N}
\]
Both sides have semigroup degree
\[
D+r,\qquad D=(q+2)m,
\]
but ordinary lengths \(q+1\) and \(q+2\).

All exponents are nonnegative, including at \(q=k-1\).

**Generation sketch.** Let \(J\) be the ideal generated by these relations. Direct weight calculations give \(J\subseteq I_S\). Modulo \(a\), the following monomials span:
\[
\begin{array}{ll}
b^ie^j:&i\ge1,\quad i+j\le k-1,\\
b^ice^j:&i\ge1,\quad i+j\le k-2,\\
d^te^j:&0\le t<k,\quad t+j\le q,\\
cd^te^j:&0\le t<k,\quad t+j\le q-1.
\end{array}
\tag{A}
\]
All exponents are nonnegative integers.

To see spanning, modulo \(a\) first use \(c^2=bd=b^k=0\). The remaining homogeneous relations eliminate excessive \(b\)-monomials, with the exception handled by
\[
be^{k-1}=cd^{k-1}.
\]
Then \(d^k=ce^{k-1}\) reduces the \(d\)-exponent; a second such reduction produces \(c^2\). Finally the \(U_r\) impose exactly the last two bounds in (A). This is a terminating spanning argument; confluence is unnecessary.

The displayed set has size
\[
\frac{k(k-1)}2+\frac{(k-1)(k-2)}2
+\sum_{t=0}^{k-1}(q+1-t)+\sum_{t=0}^{k-1}(q-t)
=2kq+1=m.
\]
It surjects onto \(K[S]/(t^m)\), whose dimension is \(m\). Hence
\[
(J,a)=(I_S,a).
\]
Weighted-degree induction now proves \(J=I_S\): write a homogeneous \(f\in I_S\) as \(j+ag\); cancellation of \(t^m\) gives \(g\in I_S\), at smaller degree. This is also the mechanism behind Gastinger’s criterion. [Statement and proof](https://arxiv.org/html/2512.18136v1#S2.Thmtheorem2.3).

Consequently, the weights of (A) give an explicit Apéry basis.

**Minimality sketch.** The two quadratic \(H\)-relations are independent. The other \(2k\) relations have ordinary degree \(k\). Modulo \(a\) and the quadratics, their nonzero images have disjoint monomial supports in
\[
K[b,c,d,e]/(c^2,bd).
\]
Thus \(H\) is minimal for its ideal.

The \(N\)-degrees lie in an interval shorter than \(m\), so a positive monomial multiple of one cannot contribute at another’s degree. The map
\[
(a,b,c,d,e)\longmapsto(s,st,st^k,st^{2k-1},st^{2k})
\]
annihilates \(H\) and sends each \(N_r\) to a nonzero polynomial. This excludes redundancy of an \(N_r\).

For \(q\ge k\), all \(H\)-degrees precede the \(N\)-band. At \(q=k-1\), the only collisions are
\[
be^{k-1}-cd^{k-1}\quad\text{at }D,
\qquad
d^k-ce^{k-1}\quad\text{at }D+k-1.
\]
Only a scalar multiple of the matching \(N_r\) can enter a redundancy relation; the displayed map forces that scalar to vanish. Hence all \(4k+2\) generators remain necessary.

This proves the proposed formula **at proof-sketch level**, uniformly over every field. A full claim packet and prescribed review remain necessary.

### Small symbolic cases

For \(k=3\), \(m=6q+1,\ q\ge2\), the eight homogeneous relations are
\[
\begin{gathered}
c^2-bd,\ bd-ae,\ b^3-a^2c,\ d^3-ce^2,\\
b^2c-a^2d,\ bce-ad^2,\ b^2e-acd,\ be^2-cd^2.
\end{gathered}
\]
The six additional relations have these two sides:
\[
\begin{array}{c|c}
cd^2e^{q-2}&a^{q+2}\\
cde^{q-1}&a^{q+1}b\\
ce^q&a^qb^2\\
d^2e^{q-1}&a^{q+1}c\\
de^q&a^qbc\\
e^{q+1}&a^{q-1}b^2c
\end{array}
\]
Thus the sketch gives \(\beta_1=14\).

For \(k=4\), \(m=8q+1,\ q\ge3\), substitution gives ten \(H\)-relations and eight \(N\)-relations, hence \(\beta_1=18\). The same four normal-form classes have \(8q+1\) elements; no new argument is needed.

Independent exploratory calculations returned \(14\) for \((k,q)=(3,2),(3,3),(3,4)\), and \(18\) for \((4,3),(4,4)\). These were in-memory checks, not archived computational certificates.

### The corrected five-generator decomposition

The naive extension of `sigma_le_four` is false.

Let \(r_d\) count singleton components and \(t_d\) nonsingleton components at a contributing degree. Each generator index contributes exactly one singleton component, at its critical degree. Therefore
\[
\sum_d r_d=5.
\]
Since component supports are disjoint, \(t_d\le2\). Define
\[
p=\#\{d:t_d=0\},\qquad N=\#\{d:t_d=2\}.
\]
Then
\[
\boxed{\beta_1+p=5+N},\qquad p\le2.
\]
The desired bound is therefore equivalent to
\[
\boxed{N\le2w-3+p}.
\]

Degrees counted by \(N\) have three possible support types:

| Type | Labeled patterns |
|---|---:|
| \(2+2+\) unused generator | 15 |
| \(2+3\) | 10 |
| \(1+2+2\) | 15 |

The family already exhibits the last type through \(c^2=bd=ae\).

A useful lemma **does** survive: selected positive exponent pairs from components with a fixed two-element support form an antichain. If \(u\le v\) at different degrees, replace \(u\) inside \(v\) by a factorization from another component. The residual retains a coordinate in the pair, while the replacement introduces an outside coordinate, contradicting the component support.

The unresolved upper-bound problem is to bound these pair antichains **jointly across the 40 patterns**. Bounding ten pair supports separately is unlikely to give the sharp constant.

## 3. Laptop tests

Claude should first run `make test`, open the journal, and create separate artifacts for the family proof and exhaustive-bound campaign. The following are execution specifications, not newly measured results.

| Test | Exact inputs and purpose | Required output | Cap |
|---|---|---|---:|
| **1. Correctness and rejection** | \(\langle3,5,7\rangle\), \(\langle4,6,9\rangle\), \(\langle5,6,7,8,9\rangle\); all raw e5 tuples at widths 4–8; invalid gcd and nonminimal inputs | Expected Betti values \(3,2,10\); independent GAP/Singular agreement; exact skip decisions | 1 laptop core-hour |
| **2. Family and boundary** | \(3\le k\le10\), \(q\in\{k-2,k-1,k,k+1,2k+1\}\), retaining admissible inputs | Explicit presentation, Apéry basis, component types; verify the formula only where claimed; inspect below-threshold behavior | 1 core-hour |
| **3. Archive plus omitted multiplicities** | Complete widths 4–20, including every \(2\le m\le w+1\) | Complete certificate replay; reproduce archived high-range counts/maxima; reconcile count discrepancy | 3 core-hours |
| **4. New widths** | Complete widths 21–30, all multiplicities in the window | Independently certified upper bounds, maxima, equality cases, structural records | 14 core-hours |
| **5. Cost model** | Whole widths 20,25,30; fixed first/middle/last prefix strata at 35,40; seed 20261016 for additional strata | Search, writing and checking costs separately; seconds/task, RSS, bytes/task, projections | 3 core-hours |
| **6. Fault and restart tests** | Corrupt parent labels; introduce cycles; omit/duplicate slots; forge skips; interrupt workers and checker publication | Every invalid certificate rejected; every incomplete run labeled incomplete; safe restart | 2 core-hours |

**Aggregate laptop cap: 24 core-hours.** A timeout is a failed measurement, never a passed width.

Test 5 must populate this table before deployment:

| Width/prefix | Raw/admissible instances | Search seconds | Check seconds | Peak RSS | Certificate bytes | Projected node1 core-hours |
|---|---:|---:|---:|---:|---:|---:|

Historical evidence is limited: the archived e5 search through 20 reports **20 CPU-seconds and 6 MB RSS**. Applying its workload scaling gives roughly **1.55 search core-hours through 40**, excluding new instrumentation, certificate writing and verification. Treat that as a forecast, not a benchmark.

## 4. Searcher, verifier and certificate specifications

### Searcher

Extend the existing task sweeper, with explicit versioned changes:

- Domain: all increasing interior offset triples and the complete multiplicity window.
- Reject gcd \(>1\) before Dijkstra.
- Test minimality exactly for small multiplicities. For \(m>w\), it is automatic.
- Compute Apéry entries and predecessor labels.
- Compute every candidate support graph and \(\sum_d(c_d-1)\).
- Change every bound test, violation condition and report from \(\binom{w+1}{2}\) to \(2w+2\).

Use checked integer arithmetic. The current `--stdin` gcd omission can leave unreachable distances at `INT64_MAX`; it must be repaired before reuse.

The only initial symmetry reduction is sorting the generators, which merely removes permutations. **Do not identify reflected offsets**, divide only the offsets by their gcd, or discard nonprimitive offset vectors. Primitivity is
\[
\gcd(m,a,b,c,w)=1.
\]

### Retained certificate: packed predecessor trees

For each admissible instance and each nonzero residue \(r\bmod m\), store a generator choice
\[
j(r)\in\{1,2,3,4\}.
\]
This requires **two bits per residue**. Its parent is determined:
\[
p(r)=(r-n_{j(r)})\bmod m.
\]

The certificate record contains:

- Instance identity, or its unambiguous position in a declared canonical stream.
- Disposition: nonprimitive, nonminimal, or admissible.
- Packed predecessor labels for admissible instances.
- Claimed \(\beta_1\).
- Format and domain versions; block checksums.

Apéry entries and attainability witnesses are encoded by the tree, rather than stored redundantly.

### Independent verifier

Implement separately, without importing the searcher’s enumeration, heap, deduplication or union–find code.

For every expected instance, the verifier:

1. Independently checks gcd and minimality, including every skipped slot.
2. Rejects parent cycles and verifies that every residue reaches \(0\).
3. Reconstructs
   \[
   A_0=0,\qquad A_r=A_{p(r)}+n_{j(r)}.
   \]
4. Checks congruences and all closure inequalities
   \[
   A_{(r+n_i)\bmod m}\le A_r+n_i.
   \]
5. Independently constructs and sorts
   \[
   C=\{n_i+A_r:0\le i<5,\ 0\le r<m\}.
   \]
6. For every distinct \(d\in C\), reconstructs
   \[
   V_d=\{i:d-n_i\in S\},\qquad
   ij\in E_d\iff d-n_i-n_j\in S,
   \]
   and counts components using a five-vertex bitset traversal.
7. Checks the resulting Betti value and the proposed bound.

This is a **complete independent replay**, using certificates rather than a second shortest-path computation.

Three soundness lemmas must accompany it:

- **Apéry correctness:** tree paths establish attainability; closure proves \(A_r\) is no larger than any attainable value in residue \(r\).
- **Candidate completeness:** if \(d\notin C\), each present vertex \(i\ne0\) connects to \(0\), because \(d-n_i-m\in S\). Thus a disconnected degree cannot be omitted.
- **Graph correspondence:** the incidence graph between factorizations and their supported generator indices identifies the connected components of the factorization graph with those of the small support graph.

### Complete coverage

The verifier independently enumerates the entire raw parameter domain. Every expected slot must occur exactly once; duplicates, missing records, extra records and unjustified skips fail.

It must also check the prefix/multiplicity partition. Neither the searcher’s task list nor its `.done` markers constitute coverage evidence.

Through width 40, the raw domain \(m\ge2\) contains **104,824,330 slots**. Full 64-bit Apéry arrays would require about **535 GB**. Packed predecessors require at most approximately **16.72 GB**, before filtering and modest framing overhead; a four-byte Betti ledger adds approximately **0.42 GB**.

The tree gives
\[
A_r\le(m-1)n_4.
\]
With \(m\le1640,n_4\le1680\), reconstructed values fit comfortably in 32 bits. Use checked 64-bit intermediates regardless.

### Structural records for proof discovery

For every expanded record, retain:

- Degree, active and unused masks, edge mask, component masks.
- One verified factorization per component.
- \(c_d-1\) binomials joining component representatives.
- Critical exponents and alternative factorizations.
- Selected pair exponents, lengths and offset weights.
- \(r_d,t_d\), and the resulting \(p,N\).

A triple-support component need not contain one factorization using all three variables; retain connecting witnesses when necessary.

Retain expanded records for every equality case, violation, family instance, new support pattern and selected transition representative. Along each fixed offset tuple, retain the Betti sequence and structural signatures, identifying changes under both \(m\mapsto m+1\) and \(m\mapsto m+w\). Signature hashes guide discovery; they are not correctness certificates.

## 5. One brief iteration

Allow **one working day and at most five additional laptop core-hours**.

1. **Family proof survives.** Write the complete presentation and Apéry proof first. Have a fresh independent prover reconstruct it, and an adversary examine boundary collisions and minimality. Freeze the checked family as a regression suite. Continue the sweep to settle the separate finite-width upper bound.

2. **A structural inequality fails or a violation appears.** Export the complete offending fibers immediately. Independently verify the presentation. A failed antichain charging proposal goes into `FAILED_APPROACHES.md`; a genuine \(\beta_1>2w+2\) stops the upper-bound campaign and redirects work toward an infinite counterfamily.

3. **Verification is ten times slower than forecast.** Optimize the independent checker in compiled code and remeasure. Preserve its mathematical independence. Reduce optional diagnostic output before reducing verification. If the complete replay still exceeds the approved cap, stop before deployment.

Do not expand to width 60. The finite-width theorem and family proof already supply concrete endpoints.

## 6. Cluster deployment

Use job-name prefix **`sg5lin_`**.

Partition by width and offset prefix, adding multiplicity intervals where needed. Split tasks according to **both** measured checking time and output size:

- Target 10–20 minutes of node1 verification per task.
- At most 256 MiB retained certificate per task.
- One physical core and at most 1 GB RAM per worker.
- Choose one versus two hardware threads from measurements and verify affinity.

Use separate node1 and node2 worker arrays, with at most eight and six physical-core workers respectively. Workload accounting must use node2’s measured factor of approximately **0.27 node1-equivalent work per core-hour**.

Write temporary files on `/scratch`. Publish immutable certificate blocks atomically to `/shared`; publish a separate verified marker only after checking. Retain source versions, build commands, domain specification, certificates, checking logs and the complete census.

Repair stale-claim handling before launch. The existing remove/recreate takeover can race, and an `squeue` failure must not imply dead ownership. Duplicate execution may be tolerated only when immutable outputs are validated and compared.

**Proposed authorization ceilings, to be replaced by measured estimates at G3:**

- Search and certificate production: **10 node1-equivalent core-hours**.
- Complete replay: **200 node1-equivalent core-hours**.
- Calibration/restarts: **5 node1-equivalent core-hours**.
- Total retained output: **40 GB**.

These are caps, not predicted consumption. At 190 node1 core-hours/day, the upper cap is roughly one node1-day plus operational overhead.

Stop on any verification failure, independently confirmed violation, output-cap breach, or a sustained cost exceeding twice the approved projection. An incomplete width remains incomplete.

### Trimmed e6 companion

**Run it only as a separately gated secondary campaign.**

Its contribution is potentially completing the **quadratic** bound in embedding dimension six. It supplies no evidence for the five-generator linear theorem.

Restrict to widths \(5\le w\le39\), and remove multiplicities already covered by an independently checked algebraic bound. Widths 40–44 should not be swept merely for margin.

The historical model projects about **12.6 node1 search core-hours through 39 before trimming**, versus 38.1 through 44. However, untrimmed three-bit predecessor certificates through 39 would occupy roughly **159 GB before filtering**, exhausting the stated free storage.

Therefore approve e6 only after measuring the trimmed domain, with a separate ceiling of **100 node1-equivalent core-hours including verification and 40 GB retained output**. If it fails either ceiling, defer it. Algebraically skipped instances support the upper bound, not exact maxima or an extremizer classification.

Do not include the current month-scale e7 sweep.

## 7. Verification and Lean plan

The intended statement should preserve the existing Mathlib formulation:

```lean
theorem beta1_five_le_two_width_add_two
    (K : Type*) [Field K] (n : Fin 5 → ℕ)
    (hpos : 0 < n 0)
    (hmono : StrictMono n)
    (hgcd : Finset.univ.gcd n = 1)
    (hmin :
      ∀ i, n i ∉ AddSubmonoid.closure (n '' {j | j ≠ i}))
    (hwlo : 4 ≤ n 4 - n 0)
    (hwhi : n 4 - n 0 ≤ 40) :
    (RingHom.ker
      (MvPolynomial.aeval
        (fun i => (Polynomial.X : Polynomial K) ^ n i)).toRingHom).spanRank
      ≤ (2 * (n 4 - n 0) + 2 : ℕ)
```

This is a target declaration, not compiled code.

For the family, quantify over \(k\ge3,\ q\ge k-1\), define \(m=2kq+1\) and the displayed five generators, and state
\[
\operatorname{spanRank}(I_S)=(4k+2:\mathbb N).
\]

Port in this order:

1. **Finite-generator infrastructure:** factorizations, fibers, component supports and degree cutoff. Prefer a generic finite index type where straightforward. Estimate **2–4 person-days**.
2. **Existing upper bridge:** explicit binomial generators imply `spanRank ≤ betaFiber`.
3. **Certificate soundness:** predecessor trees, closure, candidate completeness and small-graph correspondence.
4. **First formal instance:** certify the upper bound for \(\langle13,14,16,18,19\rangle\), using ordinary kernel `decide`. Its candidate list has at most 65 entries; the arithmetic checker should need only thousands of small operations.
5. **First general structural result:** prove singleton-component counting and
   \[
   \beta_{\mathrm{fiber}}+p=5+N.
   \]
   Do not port `sigma_le_four` by replacing four with five.
6. **Reverse bridge:** establish `betaFiber ≤ spanRank`, needed for exact family equality. Estimate **2–5 person-days**.
7. **Symbolic family presentation and minimality:** the preferred main Lean endpoint. Budget **10–20 person-days after the full informal proof is stable**, including relevant bridge work.

Do not use the existing Cartesian-box enumeration of all factorizations as the computational checker.

For the first kernel benchmark, cap a single small certificate check at ten minutes and 2 GB RAM; measure proof size and independent NanoDa replay. No `native_decide` or `Lean.ofReduceBool`; permitted axioms remain `propext`, `Quot.sound`, and `Classical.choice`. Keep the checkout below 500 MiB; large replay exports belong outside it.

The complete computational theorem additionally requires formalizing periodicity and processing roughly \(10^8\) instances. Neither is presently cheap or implemented. A proved checker does not make that kernel workload disappear. Prefer the short family proof; pursue the finite computational Lean theorem only after a measured compression or transition-certificate strategy exists.

## 8. Gates

| Gate | Evidence required | Stop rule and cap | Decision |
|---|---|---|---|
| **G0 — status** | Dated primary-source audit; exact periodicity statement; family novelty search; corrected domain and decomposition | One working day. Stop novelty claims if already published; stop deployment if reduction remains unresolved | Astra audit; Ben selects scope |
| **G1 — laptop** | Tests 1–6; complete checked widths through 30; measured cost/storage table | 24 laptop core-hours. Any disagreement blocks escalation | Claude builds; independent Astra audits |
| **G2 — iteration** | Full family proof draft; response to adversary; repaired checker and revised projection | One working day plus five core-hours. No repeated optimization cycle without new evidence | Ben approves resulting scope |
| **G3 — deployment** | Reviewed census/checker soundness; measured manifest; restart test; full replay funded | At most 215 node1-equivalent core-hours and 40 GB for e5 | Ben explicitly authorizes |
| **G4 — claim** | Every required instance verified; coverage closed; reductions reviewed; family proof independently reconstructed; objections answered | No promotion with missing tasks or unresolved objections. Formalization gets its separate 10–20-day budget | Claude records status; Astra reviews; Ben approves release |

At G2, assign independent Astra roles explicitly: adversary for presentation minimality, independent prover for the Apéry argument, and methodology auditor for certificate/coverage soundness. At G4, use a fresh framing of the claim as required by the repository’s review protocol.

The family and finite-width bound require separate claim packets and status histories. Agreement between agents is not a substitute for the proofs and certificates.

## 9. Risks and what I am least sure about

1. **The sharp global counting inequality remains unproved.** The corrected decomposition isolates the issue, but does not establish \(N\le2w-3+p\).
2. **Family novelty remains provisional.** The presentation may overlap an unlocated parametrized monomial-curve result.
3. **Complete verification may dominate runtime.** The predecessor format resolves storage, not automatically the graph-processing cost.
4. **Finite computational Lean verification may be impractical.** Periodicity and kernel-scale enumeration are substantial additional work.
5. **The e6 companion may fail its certificate budget.** Search time alone is an inadequate feasibility measure.
6. **Existing infrastructure has correctness hazards:** wrong comparison bound, low-multiplicity omissions, unchecked nonprimitive stdin, and stale-claim races.

I am least sure about the route from the pair-antichain structure to the sharp **upper** bound. The family presentation is substantially better supported: it has explicit relations, a terminating spanning argument, a dimension proof of generation, and a boundary-aware minimality argument.

**Subagents used: 3** — independent family derivation; certification/infrastructure/Lean audit; literature and periodicity audit. The literature agent then independently attacked the new family proof. I reconciled their reports and caught the false singleton-contribution extension.

**CONFIDENCE: 0.88**