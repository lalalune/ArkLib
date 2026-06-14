# BCHKS Conjecture 1.12: a validated reduction to large prime factors of `2^p−1` (2026-06-13)

## What was asked
Goal: *prove BCHKS Conjecture 1.12 (or refute) and validate.*

**Conjecture 1.12 (BCHKS25, subgroup-sumset; formalized in
`ArkLib/Data/CodingTheory/ProximityGap/SubgroupSumsetConjecture.lean`).** For infinitely many
primes `q` there is `b ≤ 10·log₂ q` and a multiplicative subgroup `G ⊆ F_q^×` of order `b` whose
distinct-element `⌊b/2⌋`-fold sumset `{e₁+…+e_{⌊b/2⌋} : eᵢ∈G distinct}` has size `≥ q/10`. It
gates the proximity-prize **upper bracket** `δ* ≤ 1−ρ−1/log₂ n` (BCHKS25 Thm 1.13) for general
2-adic NTT fields; for Mersenne `q` it is unconditional (Remark 7.3).

## Honest verdict: the conjecture is OPEN — not proved, not refuted
The conjecture is a recognized open problem in additive number theory. Even its *sub-claim*
"infinitely many primes `q` with `ord_q(2) ≤ 10 log₂ q`" is unconditionally out of reach:

- The counting necessary condition `C(b,⌊b/2⌋) ≥ q/10` forces `b ≈ c·log₂ q` (`c ≳ 1`), so `G` is
  **always** a multiplicative subgroup of size `≈ log q`. Such a subgroup of order `b` exists iff
  `b ∣ q−1` — but for the **sumset** to reach a constant fraction one needs an additive-energy /
  anti-concentration bound for `G = μ_b` that is not known for any specific infinite family (the
  same Shkredov/Glibichuk–Konyagin wall as the `δ*` core).
- Refutation is unavailable: the Mersenne family witnesses it (so it is believed true), but the
  infinitude of Mersenne primes is itself open.

Per the CLAUDE.md honesty contract ("never fabricate a closure of the open core"), no proof or
refutation is claimed.

## What WAS proved and validated (the maximal honest contribution)
`ArkLib/Data/CodingTheory/ProximityGap/SubgroupSumsetLargeFactorReduction.lean` — a machine-checked
**conditional reduction**, axiom-clean (`propext, Classical.choice, Quot.sound`), real `lake build`
EXIT 0, zero warnings/`sorry`:

> **`subgroupSumsetConjecture_of_bigOrderTwoPrimeFactor`** :
> `BigOrderTwoPrimeFactorHyp → SubgroupSumsetConjecture`,

where **`BigOrderTwoPrimeFactorHyp`** = "for every `M` there is a prime `q > M` and a prime
`p ≥ 12` with `q ∣ 2^p − 1` and `2^p ≤ q^4`" — i.e. **`2^p − 1` has a prime factor `≥ 2^{p/4}`**
for infinitely many primes `p`. This hypothesis is **strictly weaker than the infinitude of
Mersenne primes** (it does NOT require `2^p − 1` prime, only one large prime factor), turning the
prose claim in `SubgroupSumsetConjecture.lean`'s docstring ("weaker than the infinitude of
Mersenne primes") into a precise theorem. The Mersenne special case is `bigOrderTwoPrimeFactor_of_
infinitelyManyMersenne` (`q = 2^p − 1` gives `q^4 ≥ 2^p`).

### Mathematical core (the structural advance)
`mem_sumsetDistinct_signedPowersF` — the **signed binary expansion over `F_q`** for *any* prime
`q ∣ 2^p − 1` (`p` prime, `p ≠ 2`), not just `q = 2^p − 1`. When `q ∣ 2^p − 1`, `2` has order
exactly `p` in `F_q^×`, so `G = ⟨−2⟩ = {±2^j : j<p}` has `2p` distinct elements, and its `p`-fold
distinct sumset is **all of `F_q`**: every `u` equals `2·∑_{i∈T} 2^i` where `T ⊆ [p)` are the
binary digits of `2^{p-1}·u` (a `p`-bit integer because `q < 2^p`). This ports the
`mem_sumsetDistinct_signedPowers` covering from the ring `ZMod (2^p−1)` to any prime quotient — the
content that makes a mere large *factor* (not the full Mersenne number) suffice. The log bound
`2p ≤ 10 log₂ q` follows from `2^p ≤ q^4` + `p ≥ 12` by `Nat.log` arithmetic.

### Numerical validation (`scripts/probes/probe_conj112_signed_covering_nonmersenne.py`)
The covering was verified on genuine **non-Mersenne** prime factors: `q∈{23,89}` of
`2^11−1=23·89`, `q∈{47,178481}` of `2^23−1`, `q∈{233,1103,2089}` of `2^29−1`, `q=223` of
`2^37−1`. For every one: `ord_q(2)=p`, `|G|=2p`, and the explicit signed-binary witness covers
**all** of `F_q` (`witness_bad=0`); the small cases (`q=23,89`) brute-force to full sumset `=q`.

## Why this is the right deliverable
The reduction isolates the *exact* open arithmetic input — a large prime factor of `2^p − 1` — and
proves everything *coding-theoretic / additive* around it unconditionally and axiom-cleanly. It
neither overstates (no fabricated closure) nor understates (it strictly improves the in-tree
Mersenne witness from `q=2^p−1` to any factor `q≥2^{p/4}`, and machine-checks the paper's "weaker
than Mersenne" remark). The residual is now a single, named, classical number-theory `Prop`
(`BigOrderTwoPrimeFactorHyp`), squarely on the documented largest-prime-factor-of-`2^p−1` wall
(Stewart's unconditional bounds are far below `2^{p/4}`).

Related: [[arklib-prize-equivalence-session]], `deltastar-bchks-exact-brackets-2026-06-13.md`.
