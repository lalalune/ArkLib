# O172 — Adversarial verification of ClosedFormThreshold (#389, CF.md / qthreshold)

Independent re-derivation (own kernels, exact integer / faithful BabyBear).
Worktree /home/nubs/Git/ArkLib-232, synced 2026-06-13. taskset -c5 nice -19 ionice -c3, one heavy at a time.

## Checks run (all reproduced from scratch with cd_demand.c + cd_qindep.c)
- C1 CALIBRATION (n=16 mono sweep r=3..8): 97,145,89,113,225,104 — EXACT match, same maximizers. PASS.
- C2 n=32 r=3 FULL sweep: worst #bad=897 by (x^16,x^15) = closed form 32*C(8,2)+1. PASS.
- C2b n=64 r=3 stack (x^32,x^31): #bad=7681 = 64*C(16,2)+1. PASS (4th independent scale).
- DERIVATION r3_derivation.py (collinearity solve, full C(n,4)): 97/897 incl gamma=0. PASS.
- COMBINATORIAL r3_combinatorial.py: nonzero configs = n*C(n/4,2) = 96/896/7680/63488/516096 (n=16..256),
  field-independent. NOTE: the antipodal-product enumeration does NOT contain gamma=0 ("0 present? False");
  the +1 is the B=0 degenerate/linear family, confirmed present only in the full collinearity solve.
  The two scripts TOGETHER give 97; CF.md line 63-64 is correct but r3_combinatorial.py's "match? False"
  print is misleading in isolation. DOC NIT, not a math error.
- C3 r=3 BOUND: K-#bad = (h-2)h(13h-16)/12 - 1 > 0 for all h in [4,599] (exact integer), ->5.33x. PASS
  (modulo: not a landed .lean; config-count identity is computational n=16..256; rigidity = in-tree
  PairSumRigidityModP). Correctly tagged [PROVEN this pass, modulo landed rigidity].
- C4 SATURATION consistency: small-q side = DeepBandSaturationDischarge H1 (8*q^2 <= C(n,a0)), m=1,
  a0=k+m+1=r+1. Matches the report's q* ~ sqrt(C(n,a0)). PASS.

## THE ONE DEFECT (MAJOR, not fatal): q-monotonicity is FALSE as stated.
Independent prime sweep, n=16 r=7 worst stack (x^10,x^15), a0=8 (adversary/o172_qsweep_n16r7.txt):
  p:    17  97 113 193 241 257 337 353 401 433 449 577 593 641 673 769 881 929  BB
  #bad: 17  97 113 161 161 177 209 161 161 193 177 209 225 209 209 225 225 225 225
NON-MONOTONE: 3 violations (337->353: 209->161; 433->449: 193->177; 593->641: 225->209).
=> CF.md Sec 2 / production_verdict.py "#bad(q) is MONOTONE NON-DECREASING in q" is FALSE.
BUT: max over the whole sweep = 225 = char-0 limit; EVERY sampled value <= char-0; it saturates at 225.
=> the load-bearing CONCLUSION ("worst case over q is the char-0/faithful limit; production q realizes
   the worst case, not a relief") is empirically SUPPORTED. Only the MECHANISM wording is wrong:
   replace "monotone non-decreasing" with "non-monotone with char-0 supremum (saturating envelope)".
   The production verdict is conservative either way (char-0 count 225 <= K=1024, 4.55x).

## Honest-negative cross-check (retained, correct): #alignable >> K at every scale
  n=32 r=3: #align=35960 > K=4480; n=64 r=3: #align=79600 > K=39680. The obligation is #bad-SCALAR.
  Report carries this correctly.

## NET
Headline numerics all reproduce. r=3 closed form + its <=K bound are real (3-4 exact scales + identity).
Production verdict direction holds. The single correctable overclaim is the monotonicity wording, on
which the verdict superficially leans but does not actually depend (envelope argument suffices). SOUND
with one MAJOR wording fix.
