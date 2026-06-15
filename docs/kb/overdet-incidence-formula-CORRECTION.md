# CORRECTION: the over-determined incidence MAX is cubic ~ (extremal dir (n/2, n/2−1)), not (n/2−1)² — #407

**What was wrong.** Earlier notes (`deltastar-incidence-cliff-pindependence.md`, `overdet-incidence-pindependence-proof.md`)
illustrated the over-determined incidence with the value `(n/2−1)²` (49 at n=16, k=2, s=4). That was a
**few-direction sample that MISSED the extremal direction** — exactly the under-sampling caveat flagged at the time.

**The correct value (full-direction search, `probe_407_overdet_full_direction_max.py`).** At n=16, k=2, s=4 the
TRUE max over all far monomial directions is **97**, attained at direction **(a,b) = (8, 7) = (n/2, n/2−1)** (the
extremal direction involves the antipodal element `n/2 = log-half`). Across n=8,12,16,20,24,28 the over-determined
max is **9, 37, 97, 201, 361, 589** — a **CUBIC in n** (second differences are arithmetic, step 12), not the
quadratic `(n/2−1)²`.

**What is UNAFFECTED.**
- **p-INDEPENDENCE (the proven key lemma): intact.** The exactness `over-det incidence = char-0` holds per-direction
  for all odd p≡1 mod n (proper subgroup), incl Fermat — the proof (cyclotomic resultant = 2-power) is
  direction-agnostic, and `max over directions` of p-independent values is p-independent. Verified: the value 97 is
  also exact across primes.
- **The DECOUPLING: intact.** `97 ≫ budget~16 ≪ under-det Θ(C(n,k+1))`, so the binding `s*` is still always
  over-determined ⟹ δ* p-independent. Cubic-vs-quadratic only changes WHERE `s*` sits, not the decoupling.

**What this changes.** The δ* VALUE / threshold asymptotics: with the over-det max cubic `~n³` at `s=k+2` (not
`~n²`), the binding `s*` (where the max drops to budget `~n`) is at larger s than the naive estimate, so the earlier
inline δ* values (e.g. 0.6875 at n=16,k=2) were **over-estimates**. The true δ* needs the full-direction over-det
incidence curve crossing budget. This is the army's FORMULA/COMPUTE/FLOORMATCH job (still open item #2): derive the
cubic (and its s-dependence), find `s*(n,k)`, and compare `δ* = (n−s*)/n` to the floor `1−ρ−Θ(1/log n)`.

**Extremal direction is structurally meaningful:** (n/2, n/2−1) — the antipodal/half-index. Worth following: the
worst far direction is NOT the low-exponent `x^k` (the prior #407 assumption) but the antipodal-pair direction.
