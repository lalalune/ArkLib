# BUILT: the effective-Katz reduction layer (Lean, axiom-clean) + conductor program (2026-06-13)

The Katz/Rojas-León research (arXiv:2207.12439) makes the prize core a THEOREM as q→∞ (Gauss-sum joint
independence, monodromy = GL(1)^f, only Hasse-Davenport relations). The prize = the EFFECTIVE version at
fixed large q. This builds the Lean reduction layer for that program.

## BUILT (Lean, axiom-clean — `KatzEffectiveGaussSum.lean`, [propext,Classical.choice,Quot.sound])
- `EffectiveConductorBound G r K` : the Deligne/Weil discrepancy hypothesis — the cumulant deviates from
  the Wick value by ≤ the geometric error `K^r·√q` (K = conductor base of the r-fold convolution sheaf).
- `eta_pow_le_of_effectiveConductorBound` : single-frequency `‖η_b‖^{2r} ≤ Wick + K^r√q` (via proven `cumulant_eq`).
- `worstCaseIncompleteSumBound_of_effectiveConductorBound` : discharges the in-tree
  `WorstCaseIncompleteSumBound` at scale `(Wick + K^r√q)^{1/r}` — the effective analogue of the cumulant
  consumer, from the explicit conductor input. Feeds the proven downstream δ* chain.
- `effective_scale_le_two_mul_wick` : when the error is Wick-absorbed (`K^r√q ≤ Wick`), the effective
  scale ≤ `2^{1/r}·M_r` — the cumulant/floor scale up to `2^{1/r}→1`. Makes "K=O(1) ⟹ floor" explicit.

Chain `EffectiveConductorBound → WorstCaseIncompleteSumBound → (existing) → δ*` is now formal and
axiom-clean, with the conductor base K the SOLE named open input (the étale estimate).

## The conductor program (the remaining open input, quantified)
Measured (`probe_conductor_prize_regime.py`): effective conductor base in β≥4 is `K ≈ 1.28`, stable
across n,p,β. The absorption `K^r√q ≤ Wick` at r≈ln q is generous (Wick=q(2r-1)‼n^r carries n^r); K≈1.28
is comfortably inside. So the effective bound closes the prize floor IF the étale conductor estimate gives
K=O(1) — which Katz large-monodromy (full GL(1)^f, only HD) predicts asymptotically.

## Honest status
BUILT & axiom-clean: the effective-Katz reduction (conductor bound ⟹ δ* floor). The conductor base K is
carried as the explicit open Prop, NOT discharged. PROVEN asymptotically (Katz/Rojas-León, q→∞); the
effective K=O(1) at fixed q is the étale-cohomology estimate = the recognized open core, now in clean
geometric form (sheaf conductor) rather than additive-combinatorial BGK. No fabrication.
