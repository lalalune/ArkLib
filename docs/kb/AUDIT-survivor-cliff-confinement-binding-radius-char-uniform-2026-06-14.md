
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

## UPDATE (constant-rate test COMPLETE — survivor HOLDS at ρ=1/2)
Decisive constant-RATE test (n=16, k=8, ρ=1/2, budget=n=16):
- Binding radius a*=11 (δ*=0.312, IN-WINDOW: (1−√ρ,1−ρ)=(0.293,0.5)).
- At a*=11: RAW far-line incidence (LD list size) = 4 AND orbit-collapsed count (MCA) = 4, BOTH
  CHAR-UNIFORM: char-p = char-0 = 4 for every prime {97,193,257,577,1153}.
- At a=10 (δ=0.375 > δ*): char-p EXCESS appears (char-0=132, q=97→136) — confined to δ>δ*.
⟹ cliff confinement holds at constant rate; in-window binding incidence is SMALL (4, not exponential)
and char-uniform; char-p/BGK excess confined to δ>δ* (already-rejected). Covers BOTH raw LD and MCA.

## CROSS-CORROBORATION (concurrent swarm, independent p-INDEPENDENT method) + threshold sharpened to n³
docs/kb/deltastar-407-charfaithful-constant-rate-2026-06-14.md independently reaches the SAME
conclusion via a smarter method: solve the (k+1)×(k+1) linear system per (k+1)-subset for (g,γ) —
C(n,k+1) solves, independent of p — reaching n=32. Refinements to fold in:
- Char-invariance threshold at the δ*-CROSSING is **p ≫ n³** (not n²). Below it = "thin-prime pollution"
  that saturates. The PRIZE has p ≈ n·2^128 ≫ n³ for any n ≤ 2^42 (n³ ≤ 2^126 < p) ⟹ prize CLEARS with
  margin; confirmed to n=32 (ρ=1/4 and ρ=1/8).
- The char-DEPENDENT growth (char-p > char-0) is confined to **δ > δ* (near-capacity)**, where the
  clearing threshold is LARGER. This RESOLVES the earlier apparent contradiction with the point-count
  crossover doc (q*(n)~2^{Ω(n)}): that exponential threshold was measured at a=6 = a radius ABOVE δ*,
  i.e. exactly the near-capacity region. At the δ*-crossing the threshold is polynomial; above it it is
  large/exponential — but above δ* is already rejected, so it does not bind δ*.

## The SHARP new open core (much more specific than "prove BGK")
**Does the char-faithfulness prime threshold p*(n) AT THE δ*-CROSSING (binding radius) stay POLYNOMIAL
(≈ n³) as n→∞, or eventually blow up exponentially the way it does near capacity?**
- Polynomial ⟹ prize (p ≈ n·2^128) is char-determined, δ* OFF BGK — count-side closure.
- Exponential ⟹ for large prize n, p ≈ n·2^128 falls below p*(n) and BGK governs — wall confirmed.
Settling mechanism (the cliff-proof leg): binding-radius agreements ↔ RIGID vanishing relations over
Z[ζ_n] of HEIGHT ≤ poly(n) (Lam-Leung/Mann antipodal structure) ⟹ reduction mod p > poly(n) faithful;
near-capacity agreements are floppy (unbounded height). Proving the binding-radius height bound = poly(n)
is the concrete target. Verified to n=32; n=64 = C(64,9) solves is the current computational wall.
