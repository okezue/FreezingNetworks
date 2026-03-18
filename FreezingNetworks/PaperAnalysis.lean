/-!
# Formalization Status

## Aristotle (Harmonic) Verified Proofs

The following theorems have been machine-verified by Aristotle against
Lean 4.24.0 / Mathlib f897ebcf. Porting to our project's Lean 4.29.0
requires adapting API differences (Fin.find, exact?, grind).

| Theorem | Aristotle Project ID | Lines |
|---------|---------------------|-------|
| `validTiming_of_noPosCycle` | `4451c030-6d3d-4635-94f0-45e5dc3cba97` | ~300 |
| `reach_implies_sat` | `96b27986-ec6b-441a-a68d-8301bb8b30f7` | ~200 |
| `fpt_completeness` | `e406345d-1578-4ac1-9683-1e27d963340b` | ~150 |
| `fpt_soundness` | Proved manually in FPT.lean (no sorry) | ~30 |
| `sat_implies_reach` | `2d53c567-de32-4270-8c31-226b77dd08e6` | pending |

## Directly Proved in Project (no sorry)

- `dwalk_timing_sum` - Path weight sum lemma
- `noPosCycle_of_validTiming` - Valid timing → no positive cycle
- `orbit_mono_trans` - Transitive orbit monotonicity
- `CIUIFN.localF_freezing` - CI-UIFN updates are monotone
- `CIUIFN.localF_unitIncr` - Updates increment by at most 1
- `asyncStep_freeze` - Async steps preserve monotonicity
- `fpt_soundness` - Conjunctive branch reachable → disjunctive reachable
- `incr_agree` - Conjunctive/disjunctive local function agreement
- `cb_guard_mem` - Chosen branch guard membership
- `disj_guard_gives_index` - Disjunctive guard index extraction
- `orbit_monotone` - Single-step orbit monotonicity
- `onlyIf_direction` - Reachable → no positive cycle (reduces to `orbit_timing_valid`)
- `if_direction` - No positive cycle → reachable (reduces to `validTiming_of_noPosCycle` + `timing_to_orbit`)
- `main_characterization` - Theorem 3.1 (iff, reduces to above)
- `fpt_iff` - Theorem 5.1 (iff, reduces to soundness + completeness)
- `reduction_iff` - Theorem 4.2 (iff, reduces to forward + backward)
- `DNFBoolNet.localF_freezing` - Boolean net monotonicity
- `redNet_guardSize` - Guards have ≤ 3 terms
- `redNet_termWidth` - Each term has ≤ 2 literals

## Paper Issues Found

1. Edge case in (E2): a ≥ 1 for e_{u,a-1} to be valid — correct but implicit
2. Invariant (5) induction: terse but correct
3. NP backward direction: simultaneous flip case needs explicit justification
4. Degree bound: correctly stated (tracks ≤ 4, clauses = 6)

## Novelty Assessment

All four main results appear novel based on literature through May 2025:
1. CI-UIFNs as a named class
2. Weighted digraph cycle criterion for reachability
3. Disjunction frontier (NP-completeness at small DNFs)
4. FPT in disjunctive events
-/
