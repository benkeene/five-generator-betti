# Development notes

| informal label (docs/PROOF.md) | Lean declaration | file | status |
|---|---|---|---|
| Theorem F | `FiveGenBetti.Family.spanRank_eq` | Family/Main.lean | admitted |
| generators | `FiveGenBetti.Family.gens` (+ five `rfl` value lemmas) | Family/Defs.lean | proved |
| strict monotonicity, gcd | `gens_strictMono`, `gens_gcd` | Family/Defs.lean | admitted |
| generic data | `GenData e`, `nu`, `fiber`, `cutoff`, `toricKer` | Defs.lean | defined |
| certificate | `Certificate.AperyCertificate` | Certificate/Defs.lean | defined |
| first instance | `Examples.thirteen`, `thirteenApery` | Examples/Thirteen.lean | data |
| Theorem W | `FiveGenBetti.Targets.beta1_five_le_two_width_add_two` | Targets/FiniteWidth.lean | admitted, outside Solution |

Conventions as in the template: `module`, `public import`, `@[expose] public section`; internal
names (`toricKer`, `Family.gens`) differ from Challenge's public names, which Solution restates.

Discharge order (scaffold plan §9): generic defs, fibers, cutoff, upper bridge → certificate
arithmetic and soundness → `thirteen_spanRank_le_fourteen` → family generator properties and
membership → normal-form bijection → singleton counting and antichain → lower bridge → family
reduction and generation → Apéry and quotient basis → graded cardinality lemma and reviewed
minimality → Solution wrapper and family comparator.
