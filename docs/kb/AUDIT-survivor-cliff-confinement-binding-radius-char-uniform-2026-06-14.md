
## UPDATE (constant-rate test COMPLETE — survivor HOLDS at ρ=1/2)
The decisive constant-RATE test (n=16, k=8, ρ=1/2, budget=n=16) is in:
- Binding radius a*=11 (δ*=0.312, IN-WINDOW: window (1−√ρ,1−ρ)=(0.293,0.5)).
- At a*=11: RAW far-line incidence (LD list size) = 4 AND orbit-collapsed count (MCA) = 4,
  and BOTH are CHAR-UNIFORM: char-p = char-0 = 4 for every prime {97,193,257,577,1153}.
- At a=10 (δ=0.375 > δ*): char-p EXCESS appears (char-0=132, q=97→136) — confined to δ>δ*.

So **cliff confinement holds at constant rate**: the in-window binding incidence is SMALL (4, not
exponential) and char-uniform; the char-p/BGK excess is confined to δ>δ* (already-rejected region).
This holds for BOTH the raw LD list size and the MCA orbit count at the binding radius.

## Sharpened reframing (what this buys, honestly)
- The char-sum √-cancellation wall (BGK/Paley) governs the SUP-NORM M and the char-p EXCESS at δ>δ*.
- **δ* itself is governed by the CHAR-0 binding-radius incidence, which is char-uniform** — a
  COMPUTABLE combinatorial count, NOT the character-sum wall. This is the genuinely-missed reframing.
- The char-0 binding-radius incidence = #(k+1)-subsets whose Lagrange interpolant agrees with the
  power word on ≥a* points = a vanishing-sums / additive-combinatorics count over 2-power roots of
  unity (the #400 antipodal/Mann structure), char-0 and computable.

## What remains open (the new, different core)
1. PROVE cliff confinement (binding-radius char-uniformity: char-p = char-0 at a*) — currently
   numerical at n=16, ρ∈{1/4,1/8,1/2} + constant-dim. Mechanism candidate: ring-hom monotonicity
   (scalars merge never split) + char-0 incidence already ≤ budget at a* ⟹ char-p can't cross.
2. COMPUTE the char-0 worst-direction binding-radius calibration as a function of (n,ρ): does it
   stay ≤ budget (~n) for in-window δ as n→∞? (n=16 gives 4 ≪ 16. Needs large-n.)
3. LD vs MCA: data shows raw LD list = orbit MCA count = 4 at a*, so the reframing covers BOTH
   grand challenges at this point — but the §5 LD↔MCA bridge being lossy is a SEPARATE concern that
   must be reconciled (the bridge loss may matter at larger n where raw ≠ orbit).

This is the most promising count-side lead the session has produced: it moves the prize OFF the BGK
char-sum wall and ONTO a char-0 combinatorial calibration. NOT a closure — a reframing + 3 open legs.
