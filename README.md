# A039943 - attractors of the digit-square-sum map, kernel-verified in Lean 4

[![CI](https://github.com/USERNAME/a039943-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/USERNAME/a039943-lean/actions/workflows/ci.yml)

Machine-checked formalization of
[OEIS A039943](https://oeis.org/A039943): *"Every integer
eventually goes to one of these under the 'x goes to sum of
squares of digits of x' map."* (keywords `nonn,fini,full,base`;
offset `0,3`). Writing `sqSum n` for the sum of the squares of
the decimal digits of `n` and `iterateT k n` for its `k`-fold
iterate, this repository proves, for **every** natural number
`n`:

```lean
theorem A039943 (n : ℕ) :
  ∃ k, iterateT k n ∈ ATT039943

-- ATT039943 = [0, 1, 4, 16, 20, 37, 42, 58, 89, 145]
```

The existential means every orbit **reaches** the published
attractor set - not merely a numerical check on a range. The
set is the union of the fixed point `0`, the fixed point `1`
(the happy numbers, OEIS A007770) and the 8-cycle
`4 -> 16 -> 37 -> 58 -> 89 -> 145 -> 42 -> 20`.

## What is proved (kernel-checked, zero `sorry`)

- **Orbit dichotomy** (`reaches_S`, in `A007770`): every
  `n >= 1` reaches either `1` or the 8-cycle `CYC770`, by
  strong induction. Descent uses `sqSum_bound` (`n` with more
  than 3 digits satisfies `sqSum n <= 81 * digits < n`) plus
  two kernel `decide` certificates in `A007770Cert`:
  `cert_orbits770` (every `n` in `[1,99]` reaches `{1}` or the
  cycle in at most 30 steps) and `cert_descent770`
  (`sqSum n < n` on `[100,999]`).
- **Main theorem** (`A039943`, in `A039943`): corollary of the
  dichotomy - `cyc770_sub_att` maps each cycle member into the
  verbatim attractor list by `decide`; the case `n = 0` is the
  self-attracting fixed point.
- **Spec/audit layer**: `Spec_A039943` (pure `abbrev`
  statement `SpecPropA039943`, verbatim via `Nat.iterate` /
  `Nat.digits`, zero tactics), `Check_Spec_A039943` (closure
  `proven_spec_a039943 : SpecPropA039943` via the defeq bridge
  `iterateT_eq_nat`), and `Check_AntiVacuite_A039943` (N3:
  `sat943` satisfiability, anchors `anchor943_zero` /
  `anchor943_cycle`, ablation `ablation943 : 3` is not an
  attractor).

## Scope

- Mathematics: the attractor classification is classical
  (Porges 1945, Kordemsky 1955, Tanatar via the entry
  comments). What is certified here is the **machine
  verification by the Lean kernel** of the statement,
  conventions included; no proof novelty is claimed.
- The entry's data order is preserved verbatim in
  `ATT039943`; membership, not ordering, is the proved
  content.

## Status

- Lean toolchain `v4.35.0`, mathlib `v4.35.0` (pinned manifest)
- `lake build` - **zero `sorry`** (N6 zero-trust construct
  scan `scan_n6.py` clean on every shipped file)
- `#print axioms` - `[propext, Classical.choice, Quot.sound]`,
  the three standard axioms only. **No `native_decide`, no
  `sorryAx`.** `lake check --paranoid` replays the export in
  the independent checkers (CI).

## Contents

- `A046253Defs.lean` - shared digit-sum machinery
  (`digitPowerSum`, `genMultisets`, `digitsFuel`, `certSum`,
  `sortedNZ`, `certCheck`, bound `A046253_bound`)
- `A007770Defs.lean` - `sqSum`, `iterateT`, `inS`,
  `reachesS`, bounds `sqSum_le` / `bound_key770` /
  `sqSum_bound` / `sqSum_pos`
- `A007770Cert.lean` - kernel certificates `cert_orbits770`
  (`decide` on `[1,99]`, <= 30 steps) and `cert_descent770`
  (`decide` on `[100,999]`)
- `A007770.lean` - `CYC770`, bridges `inS_true` /
  `reachesS_true` / `iterateT_eq_nat`, dichotomy `reaches_S`,
  `theorem A007770`
- `A039943.lean` - `ATT039943`, `cyc770_sub_att`,
  `theorem A039943`
- `Spec_A039943.lean`, `Check_Spec_A039943.lean`,
  `Check_AntiVacuite_A039943.lean` - spec / closure /
  non-vacuity audit files
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` -
  pinned build configuration (all 8 modules in
  `defaultTargets`, the `lake check --paranoid` perimeter)
- `scan_n6.py` - N6 zero-trust scanner (state-machine
  comment/string filter, then forbidden-token search)
- `LICENSE` - Apache 2.0

## Reproduce (auditor check, < 2 min with warm cache)

```bash
lake exe cache get # fetch pinned mathlib oleans
lake build # builds all 8 libs, exit 0
lake check --paranoid # multi-kernel replay (leanchecker+nanoda+lean4lean)
python scan_n6.py # N6 zero-trust scan, exit 0 = no forbidden token
```

Expected `#print axioms` output on every audited declaration
(`A039943`, `cyc770_sub_att`, `ATT039943`,
`proven_spec_a039943`, `SpecPropA039943`, `sat943`,
`anchor943_zero`, `anchor943_cycle`, `ablation943`,
`A007770`, `reaches_S`, `iterateT_eq_nat`, `cert_orbits770`,
`cert_descent770`):

```
'<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Provenance

Developed under the DemosMathNT program (multi-session OEIS
conjecture formalization effort). The OEIS statement was
submitted verbatim to three independent oracles before
packaging (unanimous `VALIDE` on statement fidelity,
2026-11-07) - advisory verdicts; the proofs here are checked
by Lean. Attractor classification: Porges ("A set of eight
numbers", Amer. Math. Monthly 52 (1945), 379-382),
Kordemsky 1955, Tanatar. Kernel `decide` certificates
verified on the project runner (zero error, zero `sorry`).
