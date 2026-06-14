# I(δ) q-stability + the clean/dirty crossover — NOT a closure (refines NOVEL-C) (2026-06-14, wakesync)

## The mechanism (VERIFIED, ground truth)
The far-line incidence I(δ) = Σ_{far stacks} #{bad scalars at agreement τ} — the quantity δ* depends on —
is CHARACTERISTIC-INDEPENDENT for primes q above a bad-prime threshold **T(τ) = (2k)^{2k/(τ−k)}**.
Verified (probe_qstability_incidence.py): n=16,k=4,τ=6 (r=τ−k=2): I(δ) varies for q<(2k)^4=4096, then
STABILIZES to I=1040 for EVERY q>4096 tested (4129,4721,8161,12289,16193,65537). The threshold matches
the norm bound exactly: a spurious config needs p^r ∣ N(f(ζ)) (Galois conjugates), |N|≤(2k)^{2k} ⟹ bad
primes ≤ (2k)^{2k/r}, r = agreement excess τ−k.

## The SCALING — why this does NOT close the prize (the honest refutation)
δ* sits at the BINDING radius where I(δ)=budget=q·ε*=n, i.e. the window top δ*=1−ρ−η*, η*=Θ(1/log n).
There the agreement excess is r* = η*·n = Θ(n/log n), so the bad-prime threshold is
  **T* = (2k)^{2k/r*} = (2k)^{2ρ/η*} = n^{Θ(ρ log n)}.**
Clean (I char-indep at prize q) ⟺ T* < q=n^β ⟺ **η* > 2ρ/β.** Since η*=Θ(1/log n) shrinks while 2ρ/β is
constant, this FAILS past a crossover **n ~ e^{β/2ρ}**: ≈2^15 (ρ=1/4), ≈2^7.6 (ρ=1/2). (probe_deltastar_crossover.py)
Table (β=5.27): ρ=1/4,c=1: clean to 2^16, DIRTY at 2^20,2^30 (T=2^301≫q=2^158). ρ=1/4,c=3: clean to 2^30.
ρ=1/2,c=1: DIRTY everywhere (even 2^12). 
PRIZE n=2^30 is FAR past the crossover:
  • ρ=1/2: dirty for all reasonable constants ⟹ δ* q-DEPENDENT ⟹ the WALL.
  • ρ=1/4: dirty unless the δ* gap constant c > 2ρ/β·... ≈ 2–3 (= the exact-constant question = the wall).
So the toy n=16 stabilization is a SUB-CROSSOVER artifact; the prize is past it. This is EXACTLY the swarm's
NOVEL-C crossover (n~2^12–2^14; mechanism size-4 spurious p∣N, dirty when n≳2.4 log₂p) — now with a clean
QUANTITATIVE form: clean ⟺ η* > 2ρ/β, threshold T=(2k)^{2ρ/η*}, crossover n~e^{β/2ρ}.

## Net (honest)
Pursued the q-stability lead hard: VERIFIED that I(δ) is char-independent above the norm-bound threshold
T=(2k)^{2k/(τ−k)} (genuine mechanism, ground truth). But the SCALING shows that at the binding window-top
δ* the threshold T*=n^{Θ(log n)} EXCEEDS the prize q for n past a crossover ~2^{15} (ρ=1/4) / 2^{7.6}
(ρ=1/2) — so the prize δ* IS q-dependent = the BGK/Paley wall, confirming (and quantifying) NOVEL-C.
NOT a closure. The toy stabilization was sub-crossover. Contribution = the clean crossover law
(clean ⟺ η*>2ρ/β) tying the bad-prime threshold to the δ* gap. Probes committed.
