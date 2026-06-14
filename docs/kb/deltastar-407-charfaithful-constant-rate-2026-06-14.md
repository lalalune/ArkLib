# δ\* window char-faithfulness extended to CONSTANT RATE (n=16,32), with the thin-prime/near-capacity split (#407, 2026-06-14)

**Status: a genuine adversarial attack that FAILED TO REFUTE — char-faithfulness of the δ\*-crossing
holds at constant rate n=16 (ρ=1/4) and n=32 (ρ=1/8) for p≫n³; the only char-dependence is
thin-prime pollution (p<n³) that saturates. NOT a closure.**

## What was attacked
The freshest closed conjecture (`δ* = Kambiré edge, char-faithful in the window`, lalalune 08:06)
has ONE open input: **window characteristic-faithfulness** = the worst-direction far-line incidence
`I(δ)` at the prize prime equals the q-independent char-0 value. All prior verification was at
**k=2 = constant DIMENSION** (the regime where `I(w*)=n` exactly is the *proven* granularity
structure with margin 0). The prize is **constant RATE** `k=ρn`. The poster's own caveat: "n=32
faithful does NOT cross into the prize regime; feasibility rests on the constant-rate extrapolation."

This note attacks exactly that gap: char-faithfulness at genuine **constant rate**.

## Method (`probe_charinv_largep_n16.py`, `probe_charinv_constrate_n32.py`)
Exact monomial-pencil far-line incidence `I_pencil(δ)` over `μ_n ⊊ F_p*` (proper subgroup, p≡1 mod n),
far pencils `(a,b)` with `a,b ≥ k`, `≠ n/2`. Computed **without per-γ enumeration** (so large primes
are cheap): for each `(k+1)`-subset `A`, solve the `(k+1)×(k+1)` linear system for `(g,γ)`
(`g(ζ^i)=ζ^{ib}+γζ^{ia}`, `i∈A`), then compute the true agreement of that γ. `I(w)=#{distinct γ:
agreement ≥ w}`. This is `C(n,k+1)` solves, **independent of p** — so primes from thin (`p<n³`) to
`p ≫ n³` (the prize-faithful direction; the prize has `p≈n·2^128 ≫ n³`) are all reachable.

## Findings

### 1. The small-prime char-dependence is THIN-PRIME POLLUTION (p < n³)
n=16, k=4, pencil (6,7), band w=6: I = `32, 0, 48, 32` for p = 97,193,257,337 (all `< n³=4096`) —
erratic, char-dependent. But for `p ≫ n³` (4129…557057): I = `0,0,0,0,0` — **stable**. The erratic
behavior is confined to `p < n³`, exactly outside the prize regime.

### 2. The δ\*-CROSSING band is CHARACTERISTIC-INVARIANT at constant rate, p≫n³
- **n=16, k=4 (ρ=1/4)**: pencil (5,7) crossing band w=6 → `[23,23,23,23,23]` (p=4129…557057);
  pencil (9,11) w=6,7 → `[8,8,8,8,8]`. Char-invariant.
- **n=32, k=4 (ρ=1/8)**: pencil (9,13) crossing band w=7 → `[13,18,18,18]` (stabilizes at 18 < budget
  32 for p>>n³); w≥9 → 0. pencil (5,7) crossing at w=7 → 0. The δ\* **location** is char-stable.

⟹ The observable signature of the **rigid (r=k/2)** framing (δ\* char-independent), NOT the floppy
(r=1, q-dependent/BGK) framing, holds at the δ\*-crossing for n=16 and n=32 at genuine constant rate.

### 3. NEW: near-capacity bands grow with p (slower-clearing pollution), but saturate and stay ABOVE δ\*
n=32, pencil (5,7), band w=6 (δ=0.812, near capacity 0.875): I = `121,228,288,295` for
p=40961…1179649. This GROWS — but (a) strongly saturating (deltas 107→60→7, → ~300), (b) the
*fraction* I/p → 0 (0.003→0.00025), so NOT q-proportional, (c) strictly above δ\* (already in the
failure region, I ≫ budget). Interpretation: near capacity the mod-p sumset coincidences clear more
slowly, so the thin-prime-pollution threshold is larger than n³ near capacity — but the band still
appears to char-stabilize, just at a larger p. This near-capacity growth is INVISIBLE at n=16 and
emerges at n=32 — the first constant-rate sighting of the capacity-approach structure.

## Honest verdict
A real attack that **failed to refute** char-faithfulness: the δ\*-crossing incidence is
char-invariant at constant rate (n=16 ρ=1/4, n=32 ρ=1/8) for p≫n³, extending the evidence from
constant-dimension (all prior k=2) to genuine constant rate, in the prize-faithful prime direction.
This pushes the `r=k/2 (rigid)` vs `r=1 (floppy/BGK)` question toward **rigid** at the δ\*-crossing.

**Residual (unchanged in ultimate difficulty):** (a) only n≤32; the asymptotic n→∞ constant-rate
behavior is computationally walled (n=64 k=8 = C(64,9) solves, infeasible). (b) The near-capacity
char-dependent growth region (finding 3) saturates at n=32 but its large-n behavior — whether the
slow-clearing region ever reaches the δ\*-crossing as n→∞ — is exactly where the BGK wall would live.
So this is positive evidence for the closed conjecture's open input, not a proof of it.

Probes: `scripts/probes/probe_charinv_constrate_n16.py`, `probe_charinv_largep_n16.py`,
`probe_charinv_constrate_n32.py`.
