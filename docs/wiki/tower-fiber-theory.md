# The Tower–Fiber Formal Corpus (#232, O35–O63)

The connected machine-checked theory built around the Proximity Prize's open core,
spanning `ArkLib/Data/CodingTheory/ProximityGap/`. Every theorem below is axiom-clean
(`[propext, Classical.choice, Quot.sound]`, 0 sorry). The narrative ledger is
`DISPROOF_LOG.md` entries O35–O63; this page is the stable map.

## The files

| File | Contents |
|---|---|
| `DescentKernelLemma.lean` | Lemma K (`kernel_rigidity`), sharp `pattern_rigidity` (`2\|B\|+\|O₁\| ≥ 2κ`), `agreement_count`, `exists_glue_decomposition` — the descent program's single-level bookkeeping. |
| `C2CoreEliminationBound.lean` | 2026/858 Thm 38 machine-checked (`c2_core_bound`) with the minimal nondegeneracy proviso, plus the refutation of its literal `min` packaging (`thm38_min_bound_fails`, kernel-checked `ZMod 11` witness). |
| `NormalRankSharpThreshold.lean` | 2026/858 Thm 26 + Rem 27 (sharp rank threshold, both sides); deficient-triples-are-sunflowers; the cyclic/PTE deficiency mechanism; `equal_window_image`. |
| `TopDirectionLineCount.lean` | The decoupling theorem (`top_line_compat_iff`), Conjecture-41 count lower bound and kernel-checked violation witness (`conj41_violation_witness`), the point-fiber theorem (`point_compat_iff_esymm_zero`, `zero_fiber_filter_eq`), the coset construction (`coset_fiber_lower_bound`), generic tower rung (`mul_root_closure`). |
| `LamLeungTwoPow.lean` | Lam–Leung at p=2 (`vanishing_sum_antipodal`), the full tower theorem (`full_tower`) and converse (`closed_pow_sum_vanish`), the count (`tower_count`), the Newton bridge (`esymm_window_iff_psum_window`), general-word fold identities (`syndrome_fold`, `syndrome_fold_odd`), branch-mass conservation (`branch_mass_inequality`), window-weight tradeoff (`window_forces_weight`), and the capstones (`unit_syndrome_list_budget`, `two_sided_unit_syndrome_budget`). |

## The theory in one paragraph

On 2-power-torsion domains in characteristic zero (and over `F_p` above an explicit
cyclotomic-norm threshold — DISPROOF_LOG O49), the multi-symmetric fiber
`{S : e₁ = ⋯ = e_t = 0}` is **exactly** the unions of `μ_d`-cosets (`d` = smallest
2-power `> t`): `full_tower` + `closed_pow_sum_vanish` give the iff, `tower_count` gives
the `2^{O(1/η)}` budget, the Newton bridge identifies the esymm and power-sum forms, and
`zero_fiber_filter_eq` makes the fiber *equal* to a syndrome-side list at the unit
syndrome — composed in `unit_syndrome_list_budget` and pinned two-sidedly in
`two_sided_unit_syndrome_budget`. For general received words, the fold identities,
branch-mass conservation, and the window-weight tradeoff isolate the open remainder to
one object: the **branch-count distribution** down the squaring tower — equivalent to
S-two Conjecture 1 (ePrint 2026/532 App. A) on these domains.

## Conventions and gotchas (recurring learnings)

- Verify single files with `lake env lean <file>`; only `lake build <module>` when a
  cross-file import needs a fresh `.olean` (twice total in this corpus).
- `Finset.filter` instances: keep statements `open Classical in` consistently;
  instance mismatches surface as α-equivalent-but-rejected `calc`/`rw` steps — fix via
  `le_trans (le_of_eq _)` + `Finset.filter_congr`, or `convert` + `congr 1` + `ext`.
- `linarith` fails over general fields (not ordered): use `linear_combination`.
- Beta-redexes from `set`/lambda filters block `rw`: `simp only []` first.
- Newton identities were avoidable everywhere except the esymm⇔psum bridge itself
  (power-sum windows transfer through fold/fiber structure directly).
- Literature lives in `~/Desktop/math/` (Lam–Leung, Conway–Jones, Mann, Zannier,
  Aliev–Smyth, KPS/DKS Nullstellensätze, BCIKS/BCHKS/GG25/S-two/Chai–Fan/Kambiré).
