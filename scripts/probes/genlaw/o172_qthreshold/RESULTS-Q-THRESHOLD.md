# The q-threshold: production q is the WORST case, and r=3 holds for all n — proven

2026-06-13. Follow-on to O171. Question: O171 showed CensusDomination's deep-band #bad-scalar
count holds with margin at n=16 *faithful* prime; the fleet's DeepBandSaturationDischarge shows
it *fails* at small q. So there's a q-threshold — and the prize needs to know whether
production q (|F| up to 2²⁵⁶, ε\*=2⁻¹²⁸) is on the holds side. Opus 4.8, three legs,
adversarially verified (0.85, one wording correction applied).

## Verdict: PRODUCTION-HOLDS

**1. Production q is the WORST case, not a relief.** The deep-band #bad-scalar count as a
function of q has the char-0 algebraic count as its **supremum** (a *saturating envelope* —
NOT monotone; the small-q regime fluctuates, with measured strict drops, but nothing ever
exceeds the char-0 value). Below the threshold q\* the count is value-space-limited (#bad ≤
q−1) and CensusDomination fails by pigeonhole (= DeepBandSaturationDischarge / the O164
saturation regime). Above q\*, #bad equals the fixed char-0 count. **Consequence: production q
realizes the char-0 worst case exactly**, so wherever the char-0 count ≤ K, production holds —
the n=16/32 faithful evidence *transfers* to production (this resolves the q-transfer worry
O171 left open and the energy-vs-supply finding flagged).

The threshold: q\*(n,r) = √C(n,r+1) per band (central worst ~2^{n/2−O(log n)}); the A4
rigidity threshold for the exact char-0 value is 4^{n/2}=2ⁿ. Production q (2⁶⁴…2²⁵⁶) is far
above q\* for all prize-relevant n (n ≤ 256 by rigidity, n ≲ 512 by the √ bound).

**2. r=3 is PROVEN for all n** (modulo the already-landed A4 rigidity lemma). The high-freq
order-2-line deep-band count has an exact closed form:

> **#bad(r=3) = n·C(n/4, 2) + 1 = n²(n−4)/32 + 1**

verified at four scales digit-for-digit (n=16→97, n=32→897 [full 992-monomial sweep],
n=64→7681, config-count identity to n=256), reproducing O171's worst case. And it is ≤ K for
**all** n by the exact integer polynomial identity `K − #bad = (h−2)h(13h−16)/12 − 1 > 0`
(h=n/2≥4), margin → 5.33×. Derivation: the order-2 character line reduces aligned 4-sets to a
parity-split collinearity → antipodal pair-product condition → bad γ = −e₁ (the in-tree Vieta
pin); config count `n·C(n/4,2)` is a field-independent sum-class identity; distinctness is
A4CensusValue's `pair_sums_ne_modp` rigidity (proven, threshold 2ⁿ).

## Honest scope

- **r ≥ 4 is OPEN.** No clean closed form — the worst-case monomial family is divisor-dependent
  (x^{n/2} at r=3; the x^{n/4} family at r=4, where the x^{n/2} line degenerates to #bad=1),
  counts non-monotone (97,145,89,113,225,104). General-r ≤ K is MEASURED only (n=16 all 6
  bands 2.46×–20.1×; n=32 r=3 5.0×, r=4 33×) — this is the ExcessCensusLaw open analytic core.
- This is the demand-side #bad-SCALAR object; the literal alignable-SETS form remains FALSE
  (O171's lossy-overcount finding, retained: #align ≫ K at n=32/64).
- So: **r=3 demand bound proven all-n + production q = worst case** ⟹ the census route to δ\*
  is alive and r=3-closed at production; the remaining obligation is the general-r (r≥4)
  deep-band #bad-scalar bound — a single, sharply-named analytic target.

Reproduce: `r3_combinatorial.py`, `r3_derivation.py`, `closedform_fit.py`, `threshold.py`,
`production_verdict.py`; adversarial re-check in the O172 verify artifacts.
