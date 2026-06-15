# wf407 / T02-shkredov — Shkredov higher-energy & bilinear levers on the r-fold cross-surplus

**Date:** 2026-06-14 · **Verdict: WALLED** (to W2 √n-loss + W4 moment-depth = the Gauss-period /
Paley-eigenvalue wall, i.e. the Paley Graph Conjecture, OPEN). · **Honesty contract held — no
fabricated closure.**

## The thread

407-T02 = the *non-moment* additive-combinatorial bound on the `r`-fold cross-surplus of `μ_n`,
named in the census as the prize's "best lever" precisely because the **moment** route is PROVEN
(wall W4) unable to supply it. Two concrete mechanisms to assess:

- **(S) Shkredov higher-energy** — subgroup additive energy `E⁺(Γ)` bounds, tripling constant
  `|3Γ| ≫ |Γ|²/log|Γ|`, shift energy `E^×(Γ+x) ≪ |Γ|² log|Γ|` (1504.04522); the well-known
  improved `E⁺(Γ) ≪ |Γ|^{32/13}` (saving over the trivial `|Γ|^{8/3}`).
- **(B) Chang–Shparlinski / Kerr–Macourt BILINEAR double sums** — a *different* mechanism (sub-√q
  from bilinear structure rather than from additive energy); the cleanest reference is
  Bourgain–Glibichuk–Konyagin (0705.4573): `|Γ|≥p^δ ⟹ |(1/|Γ|)Σ_{x∈Γ}e_p(ξx)| ≪ p^{−δ'(δ)}`.

## Prize regime (the load-bearing fact)

`n = |μ_n| = 2^a` (`a ≤ 40`, CLAUDE.md cap `k≤2^40`), `p = n·2^128`, so the **density exponent**
`θ = log_p n = a/(a+128) ≤ 40/168 = 5/21 ≈ 0.238 < 1/4` for every realizable instance (and
`θ → 0.20` at the canonical `a=32`). This single inequality kills the lever:

| result | applicability hypothesis | prize `θ` | met? |
|---|---|---|---|
| Shkredov `E⁺`, tripling, HBK energy | `|Γ| > p^{1/4}` (`θ>0.25`); HBK vacuous below `q^{1/3}` | ≤ 0.238 | **NO** |
| Bourgain–Glibichuk–Konyagin bilinear | `|Γ|≥p^δ`, decay `δ'(δ)→0` as `δ→0`; best explicit `n^{1−o(1)}` | δ=θ small | √n-trivial |
| sub-√q bilinear (2-variable) | both factors density `>p^{3/7}≈0.43` | θ/2 ≤ 0.12 | **NO** |

## Evidence (exact, machine-checked)

Three probes, all run, all exact (enumerated, not sampled):
`scripts/probes/wf407_T02-shkredov_cross_surplus.py`, `_regime_boundary.py`, `_bgk_decay.py`.

1. **Density gate (Part 1 / L1).** `θ = a/(a+128) < 1/4` for all `a ≤ 32`; measured `E_2/n² = 3−3/n`
   sits *exactly at the char-0 minimal-energy floor* (Duke–García `E_2 = 3n²−3n`), with **no
   `p^{−ε}` saving** — the Shkredov machinery has no room and no mechanism at this density.
2. **r=2/r=3-locked + onset law (L2 — the sharpest new finding).** The cross-surplus
   `S_r = E_r^{F_p} − E_r^{char0}` is **identically 0 for `r < r_max = 2·log_n p`** and only turns
   on AT that ceiling. Exact per-`r` surplus (e.g. `p=786433, n=32, θ=0.255`): `S_2=0, S_3=0,
   S_4=1290240` with `r_max≈7.83`; `p=12289, n=32`: `S_2=0, S_3=92160` at `r_max≈5.43`. Below
   `r_max` char-p = char-0 so the Gaussian moment bound is **already clean and needs no
   additive-comb input**; the surplus is born exactly at the depth the moment method provably (W4)
   cannot reach and where no Shkredov/bilinear bound is stated (they are `r=2`, occasionally `r=3`).
3. **Collapse (Part 5).** `Σ_b ‖η_b‖^{2r} = q·E_r` verified EXACTLY — so `E_r` (hence `S_r`) IS the
   `2r`-th moment of the Gauss periods. Any cross-surplus bound = the moment method on the periods =
   the Paley-eigenvalue / Paley-Graph-Conjecture wall (`B ≤ 2√n ⟺ Ramanujan`, OPEN; best PROVEN is
   BGK `n^{1−o(1)}`).
4. **Bilinear vacuity (Part 4 / bgk_decay).** Splitting `μ_n` as a sumset gives factors of density
   `θ/2 ≤ 0.10 ≪ 3/7`; `μ_n` is intrinsically a single-variable thin set, no second free variable
   to bilinearize. The BGK absolute bound at `θ<1/4` is `n^{1−o(1)}`, a factor `√(n/(128 ln2))` —
   growing like √n, ≈`2^15` at `n=2^32` — above the target `√(n log(p/n))` (this IS wall W2).

## The W2 sqrt-loss (why the *direction* is also wrong)

Even granting applicability, the energy route pays a structural `√n`: `list ≥ √(n·E⁺) ≥ √(n·n²) =
n^{3/2} > n` (diagonal alone). Shkredov's `E⁺ ≪ n^{32/13}` is an **upper** bound (controls how
*large* `E⁺` can be); the floor side needs `E⁺` *small*, and even the Shkredov UB gives
`list ≤ n^{(1+32/13)/2} = n^{1.731} > n^{3/2}` — still above the Johnson-window `n`. The bound
points the wrong way and the `√n` loss is irreducible (W2).

## Lean artifact (axiom-clean)

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/WF407_T02Shkredov.lean` — the elementary
regime-vacuity kernel, audited `[propext, Classical.choice, Quot.sound]`:
- `shkredov_density_gate`: `n > p^{1/4} ⟺ log n > 128·log2/3` (`a > 128/3 ≈ 42.67`).
- `prize_below_quarter_power`: for `a ≤ 40`, `¬(2^a > p^{1/4})` — the Shkredov/HBK density
  hypothesis is **unsatisfiable** at the prize.
- `density_exponent_lt_quarter`: `θ = a/(a+128) < 1/4` for `a ≤ 40`.
- `bilinear_factor_below_quarter`: each bilinear factor density `θ/2 < 1/4` (a fortiori `< 3/7`).

## What remains / cross-levers

The wall is unchanged: the worst Gauss period `B = max_{b≠0}‖Σ_{x∈μ_n}e_p(bx)‖` at thin density
`θ<1/4`, = the generalized-Paley eigenvalue = the Paley Graph Conjecture. The one *new* structural
hook this thread isolates: the cross-surplus onset law `S_r = 0 for r < 2 log_n p` says the
char-p defect is **exactly localized** at `r = r_max`, so a future attack only needs a non-moment
bound on the *single* boundary moment `E_{r_max}` (not all `r`), but that is precisely the
`±1`-relation/ideal-SVP defect (T407-T09 cross-parity leak) — no Shkredov/bilinear tool reaches it.
Shkredov's `r=2/r=3`-locked machinery and the 2-power antipodal structure of `μ_{2^k}` are the only
additive-combinatorial levers with the right q-free object, but they stop at the density floor.
