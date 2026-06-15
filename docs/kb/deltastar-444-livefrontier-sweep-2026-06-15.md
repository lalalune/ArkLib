# #444 live-frontier sweep (6-agent workflow + adversarial verify) — 2026-06-15

0 closures; 1 cleanup overturning a committed false-refutation; 9 fresh dead-ledger entries.
Comment: lalalune/ArkLib#444 issuecomment-4705637815. Probes pushed `de40196bf`.

## ★ Q1 d=32 CLEANUP (verified) — overturns committed false refutation
`probe_407_close_actionorbit_{VERDICT,q1_dichotomy}.py` claimed "d=32: 192-384 primitive pts 100%
VIOLATE ⇒ (*)_32 FAILS ⇒ Q1 fails ⇒ orbit count not O(1)." **FALSE.** Exact MITM reconstruction
(`probe_444_q1_d32_cleanup.py`): T0 char-0 `V_d^prim`(p_1=0) empty 0/0/0 d=8/16/32 (half-basis ℚ-indep
= Lam-Leung); T1 char-p per-prime 32-64 ≈ 3^16/p = 41 pigeonhole; **T2 cross-prime 0/64 survive mod
p2∧p3∧p4** ⇒ coincidental mod-p noise, NOT structural. So (*)_32 does NOT fail; d≥16 self-similarity
intact. The char-p "primitive points" ARE the BHBI {−1,0,1}-relation failures; non-survival = why
BHBI-at-prize is a pigeonhole artifact (reconfirms §8 from the Q1 angle). Cleanup, not a prize advance
(char-0-vacuous Lam-Leung ⇒ no O(1) orbit bound at prize ⇒ Action-Orbit still collapses to BGK).

## Lead (a) moment-step deeper r — REDUCE-TO-WALL
Exact law `1 − g(r,n) ≈ r/n` (g(r)=(A_{r+1}/A_r)/((2r+1)n), DC-subtracted; reproduces board g(2)=0.9363,
g(3)=0.9063 @n=32). g decreases monotonically in r; at r*~4log2(n), margin r*/n→0, g(r*)→1⁻ = BGK
knife-edge at EVERY rung (NOT r=2-specific — corrects earlier reading). Rule-3: thin==neg-closed-random
(thickness-invariant); 1−g~r/n is the generic leading correction to pure Wick, not a 2-power signature.
`probe_444_step_deep.py`. g(r*)<1 = same M<√(2n log p) finite-n fact; r*~120 @ n=2^30 unreachable.

## Lead (b) #bad/budget deeper bands — quantitative REFUTED-by-verification
Attacker's "polynomial floor-collapse" (r=3 ratio 0.0558@n16) = under-search artifact anchored to line
(4,2). Genuine worst lines: 0.2165 (n16, (9,2)), 0.2002 (n32, (17,2)) ⇒ ratio FLAT ~0.20-0.24 across
r=2,3, NOT collapsing; #bad~n^3.21 tracks budget ~n^3.32. Qualitative (q-indep, thickness-invariant,
bounded<<1) survives; "deeper=stronger floor" refuted.

## Lead (c) over-det growth law — DOUBLE refutation, reclassified Johnson-region
(1) board's `s*−k=n/4 ⇒ δ*=3/4−ρ` REFUTED. (2) attacker's "s*−k=3 constant" ALSO false (used forbidden
correlated dir x^{n/2}=±1); genuine dirs n=32 k=2 s=k+3 give I≈80-90≫32 ⇒ s*−k≥4; Rust+GPU s*=5,7,7,11
plateau-then-jump. "Exceeds-Johnson" track has agreement s*=5 const ⇒ 5/n→0 min-distance-edge, char-0/
thickness-invariant, δ*−δ_J→0 ⇒ Johnson-region object, NOT beyond-Johnson floor. Genuine hinge (s*−k
bounded for n>16?) brute-infeasible past n=16.

## Conjecture round 2 C11-C20 — 9 REFUTED/reduce-to-wall, 1=wall (C13=moment step)
C11 mult-energy asym (thin==thick); C12 Hasse-Davenport descent M(2n)²≤2M(n)² (R=3.58>2); C13 Turán-
Newton power-sum (=moment step, SURVIVES-AS-WALL); C14 subspace-evasive discrepancy (Erdős-Turán of M);
C15 dual-BCH support (d_⊥≈k+1⇒Johnson, q·E₂-reducible); C16 derandomized autocorr (Wiener-Khinchin needs
unknown phases, circular); C17 Elekes-Szabó (T=#{x+y∈μ_n}=0 exactly, vacuous); C18 effective Chebotarev
(p≡1 mod n totally-split, zero info); C19 mult-shift covariance (group tautology); C20 collective L4
windowed-mass (single-peak M² dominates, no LINEAR window decouples). 3 kill-mechanisms: thickness-
invariance / group-tautology / M-in-disguise. C20 sharpens rule-5e: closure needs NONLINEAR phase-aware
aggregate not telescoping to Wick = the open √-cancellation.

## Substrate: IPR closed form PR=(qn−n²)²/(qE−n⁴), 3 axiom-clean theorems, thickness-invariant diagnostic
(prose "PR≈q/(3n)" corrected → PR≈q/3, factor-n; q·E₂-reducible = §8-capped, not an open-core lever).

CORE OPEN. Only surviving lever = collective/nonlinear BGK aggregate (rule-5e); every linear/L²/spectral
object reduces to q·E_r (capped √n/Johnson). [[arklib-444-canonical-dossier]]
