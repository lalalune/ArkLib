# wf407 / T24-pfree — the p-free invariant `c_r = E_r^∞/(r!·n^r)` and the defect gate

**Verdict: WALLED.** `c_r` is genuinely p-free, and the *ideal* p-free moment bound would close the
prize — but the moment arrow consumes the *char-p* energy `E_r(F_q) = E_r^∞ + D_r(q)`, and the defect
`D_r(q)` re-enters as an **arithmetic divisor condition** (`p | N(α)`), not a size condition, at
exactly the depth `r ≈ log q` the ideal bound needs. The lever **RE-LABELS the char-0 → char-p
transfer wall** (= the BGK / additive-energy / cyclotomic-norm-defect core); it does not move it.

Date: 2026-06-14. Honesty contract held — no fabricated closure.

## What was claimed (the thread)

The entire moment ladder factors through a p-INDEPENDENT invariant `c_r = E_r^∞/(r!·n^r)` of the
*complex* n-th roots. A concentration bound proven on this single p-free object would be
automatically p-uniform, dodging the per-prime structured-prime explosion. "p-uniform-from-p-free"
was named but never built.

## Part 1 — `c_r` IS exactly p-free; it equals the Bessel coefficient (CONFIRMED)

`E_r^∞ := #{(x,y)∈μ_n^{2r} : Σx = Σy over ℂ}` matches `E_r(F_q)` exactly at every tested prime in
the clean regime (probe `wf407_T24-pfree_cr_invariant.py`, all rows `char0==p? True`), and

  `E_r^∞ = (2r)!·besselCoeff(n/2, r)` exactly (matches in-tree `RungBesselEnergy.besselCoeff`).

Values: n=8 → c_1=1, c_2=21/16=1.3125, c_3=5/3=1.6667 (c_r GROWS, not "decreasing" — the
DISPROOF_LOG "c_r decreasing" refers to the *Bessel/Gaussian ratio* E_r^∞/E_r^Gauss ≤ 1, which IS
decreasing, and is the already-proven `RungBesselEnergy.bessel_energy_le_gaussian`).

## Part 2/4 — where the defect re-enters: ARITHMETIC, not size (the wall)

The moment arrow (`CharSumMomentDeepWall.charSum_le_of_moment`) is
`B^{2r} ≤ q·E_r(F_q)` with the **true** char-p energy. Split `E_r(F_q) = E_r^∞ + D_r(q)`, `D_r ≥ 0`.

**The defect onset is NOT size-monotone** (probe `wf407_T24-pfree_defect_structured.py`, Part 4A):
- n=8, r=3: smallest CLEAN prime = 113, but **p=137 and p=313 (both larger) carry defects** (D=240, 48).
- n=16, r=2: smallest CLEAN prime = 241, but **p=257 and p=337 carry defects** (D=192 each).
  (Note: p=337 is one of the very primes the thread cited for "p-free verified"; `c_r=E_r^∞` IS p-free
  there, but `E_r(F_337)` has a defect — confirming `c_r` is the wrong object for the arrow.)

**Exact mechanism (Part 4B, 100% match):** the defect primes are EXACTLY the odd prime factors
`q ≡ 1 mod n` of the norm set `{N(α)}` of sparse roots-of-unity differences `α = Σx − Σy`
(`≤ 2r` roots, `α ≠ 0` over ℂ). Measured defect primes `[17,41,73,89,97,137,313]` == norm-factor
primes, MATCH=True. So `D_r(q) > 0 ⟺ ∃ sparse α (≢ 0 over ℂ) with p | N(α)` — a **divisor condition**,
structurally identical to the Cheng-house / large-sieve / cyclotomic-norm-defect wall already in the
DISPROOF_LOG. A larger prime can divide a norm a smaller one misses ⟹ **no `∀ p ≥ P₀` p-uniform
statement is possible.**

## Part 3/5 — the lever is real-in-principle but blocked exactly at prize depth

- The IDEAL p-free bound `min_r (q·E_r^∞)^{1/2r}` (Gaussian top) reaches `√(n·log q)` at
  `r_opt ≈ log q`, ratio ≈ 1.42 (probe `wf407_T24-pfree_prize_regime.py`, Part 5C). So a *valid*
  p-free energy bound at depth `r_opt` WOULD close the prize — the lever is **not vacuous**.
- But the p-free value `E_r^∞` is provably wrong (defect on) at that depth: clean only for
  `r ≤ r_max ≈ 2 log_n p − 3 = O(1)` at prize `p ≈ n^5`, while `r_opt ≈ log q` grows; the ratio
  `r_opt / r_max ≈ a/2` (half the tower depth — same gap as `CharSumMomentDeepWall`). So the p-free
  object cannot be substituted for `E_r(F_q)` at prize depth.

## Lean brick (axiom-clean)

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/WF407_T24_PFreeDefectGate.lean` — five theorems,
audit `[propext, Classical.choice, Quot.sound]` only (pg-iterate EXIT 0, 162s):
- `moment_with_defect`: the honest arrow `B^{2r} ≤ q·E_r^∞ + q·D_r` (the defect made explicit).
- `pfree_bound_valid_of_no_defect`: `D_r = 0 ⟹ B^{2r} ≤ q·E_r^∞` (the lever fires only in the clean
  regime — where the wall is already crossed by `p > (2r)^{n/2}`).
- `pfree_gate`: the dichotomy — the bound is the p-free bound plus the gate `q·D_r`, vanishing iff
  `D_r = 0`. The entire p-uniformity question reduces to controlling the single arithmetic `D_r`.
- `pfree_no_size_threshold`: a defective prime forces `q·E_r^∞ < B^{2r}`, so no size-threshold
  p-free bound can hold (abstracted structured-prime obstruction).

The number-theoretic content (that `D_r > 0` at `r ≈ log q` for the prize prime) is the open wall,
carried as the `D_r` hypothesis and never discharged.

## Bottom line

Genuine new framing, definitively walled. `c_r` p-freeness is real but is the *wrong object*: the
arrow needs `E_r(F_q) = E_r^∞ + D_r`, and `D_r` is the exact char-0→char-p mod-q defect. The p-free
invariant is a clean way to *name* the wall (the gate `D_r`), not a way to dodge it. The same divisor
condition `p | N(α)` that walls Cheng-house and large-sieve walls this too.

## Artifacts
- `scripts/probes/wf407_T24-pfree_cr_invariant.py` (Part 1: p-freeness + Bessel)
- `scripts/probes/wf407_T24-pfree_bridge.py` (Part 2/3: defect re-entry + bridge test)
- `scripts/probes/wf407_T24-pfree_defect_structured.py` (Part 4: arithmetic non-monotonicity + norm mechanism)
- `scripts/probes/wf407_T24-pfree_prize_regime.py` (Part 5: ideal bound reaches target; defect on at prize depth)
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/WF407_T24_PFreeDefectGate.lean` (axiom-clean brick)
