# Grand unification: δ*-q-dependence = Q1-char-p-defect = additive coincidences of μ_n in F_p; and deployment-field cleanness, 2026-06-13

## The unification (verified)

Three things this session that looked separate are **one object**:

1. **δ\* q-dependence** (the prize wall): exact δ\* has no clean formula because the
   far-line incidence is q-dependent.
2. **Q1 char-p defect** (action-orbit): the crux "`e_1(S)=0 ⟹ S` antipodal" is true
   over ℚ (Lam–Leung) but FALSE in char p (480 spurious non-antipodal sum-zero
   subsets of μ_16 at p=97).
3. Both are the **additive-coincidence structure of `μ_n` in `F_p`**: the number of
   *spurious* additive relations `Σ_{s∈S} s ≡ 0 (mod p)` that do NOT hold in `ℤ[ζ_n]`.

When `n | p−1`, `μ_n ⊆ F_p`, so Frobenius acts trivially — there is **no Galois**;
the defect is purely arithmetic (which n-th roots collide additively mod p). This is
literally the additive-energy object behind δ\*. So the action-orbit char-p
difficulty and the δ\* wall are the same wall.

## The lever: single = floppy, simultaneous = rigid

A **single** elementary-symmetric relation (`e_1=0`, or one far-line direction's
incidence) is char-p **floppy** — q-dependent, the wall. But the **simultaneous**
system "`e_i=0` for all odd `i≤k`" is char-p **rigid** — field-independent (k=4 →
exactly 70=C(8,4); k=8 → 12870=C(16,8); full DPR count 8, exhaustive to k=8). The
extra constraints kill the spurious relations. This is the structural reason the
action-orbit *orbit count* (a simultaneous system) is well-behaved where the bare
*incidence* (single relation) is not.

## Deployment-field cleanness (NOVEL-C) — REFUTED at deployment scale (see update)

> UPDATE: workflow refuted this at deployment scale. Deployment fields are clean only to a
> crossover n (KoalaBear/BabyBear first dirty at n=4096=2^12; Goldilocks ~2^14); deployment
> uses n=2^20..2^27 >> crossover. Mechanism: size-4 spurious needs p|N(sum zeta^e), max norm
> ~2^{0.41n}, so p dirty once n >~ 2.4 log2 p. The defect DOES afflict deployment fields at
> scale. See unlock-workflow-synthesis-2026-06-13.md. The n<=32 cleanness below is a
> moderate-n artifact, NOT a deployment unlock.


The additive-coincidence defect is a **low-2-adicity** phenomenon. Norm bound: a
spurious `S` has `|Norm(Σs)| ≥ p` but `≤ |S|^{φ(n)} = |S|^{n/2}`, so the **minimal
spurious size ≥ p^{2/n}**.

| n | defect at p=97 (2-adic 5) | p=257 (8) | BabyBear (27) | KoalaBear (24) | Goldilocks (32) |
|---|---|---|---|---|---|
| 16 | 480 | 0 | **0** | **0** | **0** |
| 32 | 152768 | 16800 | **0** (sz≤6) | **0** | **0** |

**All actual deployment fields are CLEAN at n=16, 32** — char-0-like, so my Lam–Leung
crux *applies* and δ\* is at the clean value *for the fields that matter*, even though
it is q-dependent over arbitrary primes.

**Caveat (honest):** at n=16, `p^{2/16} ≈ 15 ≈ n` forces cleanness by tininess; at
deployment `n=2^20`, `p^{2/n} ≈ 1` so the norm bound is **vacuous**. The deployment
fields are clean at n=32 *beyond* the norm bound (BabyBear could have size-4 spurious
but has none), suggesting a deeper 2-adic reason — but cleanness at deployment `n`
(`2^20`–`2^30`) is **not enumerable** and remains open. So NOVEL-C is a genuine,
testable, promising direction — NOT a small-n mirage (clean beyond the norm bound),
NOT a proof (deployment-n untested).

## What this would unlock if it holds at deployment n

A **deployment-exact** resolution: δ\* is pinned at the clean value *for the
deployment fields* (high 2-adicity, which they need anyway to support smooth domains),
and the Q1 char-p crux holds there too — even though both are q-dependent over generic
primes. The open question becomes: **does the additive-coincidence defect of `μ_{2^m}`
in `F_p` vanish whenever `p`'s 2-adicity `v` exceeds some `f(m)`?** Threshold data: n=16
clean at `v≥7`; n=32 dirty even at `v=10` for small primes but clean for the big
deployment primes — so it is NOT a pure `v` threshold; the prime's full structure
matters. This is the precise, novel, attackable question.

Probes: `scripts/probes/probe_deployment_field_cleanness.py`,
`probe_dpr_lamleung.py` (char-uniformity sweep). Part of the comprehensive attack
workflow `wf_c255fea7-8cf` (Q1 char-p ×3, Q3/Q4, Q2, novel ×3).
