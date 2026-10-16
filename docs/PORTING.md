# Porting record from PALOMAR-2026-10-07-000005 (`~/semigroup-betti`)

Source commit: aa266b8a7db2794e49a0053978852ade100d23da (working tree had uncommitted README,
metadata and correspondence edits; nothing from the working tree was copied).

Copied unchanged: `lean-toolchain`, `LICENSE`, `lake-manifest.json` (root name changed to
`fivegenbetti` only), `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb`,
`scripts/verify-comparator.sh`, `.github/workflows/ci.yml`; `.lake/packages` APFS-cloned.

Library reuse plan (scaffold plan §2 table; nothing ported yet):
| template file | action |
|---|---|
| Basic.lean | absorb into Defs |
| Defs.lean | generalize to `GenData e` (no offset fields) |
| Fiber.lean | generalize (max generator instead of `n 3`) |
| Bridge.lean | port the proof core; extract `toricKer_le_ideal_of_mono_sub_mem` |
| Critical.lean | port through `two_le_crit`; do NOT port `ncomp_sub_one_le`, `sigma_le_four` |
| Partition.lean | extract support lemmas; replace `IsSplit` by `HasPairComponent` |
| Antichain.lean | copy the abstract pair-antichain block |
| Exceptional.lean | extract generic pair-coordinate helpers only |
| Identities.lean, Arith.lean | not ported |
