# Certificate checker (specification)

Input per instance: generators n₀ < … < n₄, m = n₀, and for each nonzero residue r a parent
generator index j(r) ∈ {1,…,4}. Checks: domain, gcd, minimality (exact for small m; automatic
for m > w); parent graph is a tree toward 0 (fuel-bounded traversal of ≤ m steps); A₀ = 0,
A_r = A_{p(r)} + n_{j(r)} with p(r) = (r + m − n_{j(r)} mod m) mod m; congruences; closure
A_{(r+nᵢ) mod m} ≤ A_r + nᵢ; candidate degrees C = {nᵢ + A_r} deduplicated; for each d ∈ C the
support graph (vertices i with nᵢ ≤ d and d − nᵢ ∈ S, edges i ≠ j with nᵢ + nⱼ ≤ d and
d − nᵢ − nⱼ ∈ S, membership x ∈ S ⇔ A_{x mod m} ≤ x) and Σ_d max(c_d − 1, 0).
Soundness lemmas: Apéry correctness, candidate completeness, graph correspondence (d > 0).
First instance: `Examples/Thirteen.lean`. Bulk certificates live outside the checkout
(`~/five-generator-betti-artifacts/`).
