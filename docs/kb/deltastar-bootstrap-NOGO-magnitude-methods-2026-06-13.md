# NO-GO: magnitude/sup-norm bootstrap CANNOT close the gate — only direct collision-counting can (2026-06-13)

Tests whether the standard self-improving route — bound `M_r = Σ_{b≠0} η_b^{2r}` by splitting `b` into
magnitude bands (`L²` mass + a base sup-norm bound `B ≤ B₀`) — can reach the Gaussian baseline
`p·(2r−1)!!·n^r` that the Markov bridge needs at `r ≈ ln p`. Bound used (optimized over threshold `T`):
`M_r ≤ T^{2r−2}·pn + (pn/T²)·B₀^{2r}`. Prize regime `log₂p=192, log₂n=30, r=ln p=133`
(`scripts/probes/probe_bootstrap_nogo.py`):

| base case `B₀` | bootstrap `M_r` | Gaussian | verdict |
|---|---|---|---|
| Weil `√p` (2^96) | 2^25566 | 2^5062 | FAILS |
| subgroup `√(np)` (2^111) | 2^29526 | 2^5062 | FAILS |
| half-way `p^{1/4}n^{1/2}` (2^63) | 2^16854 | 2^5062 | FAILS |
| **prize target `√(2n ln p)` (2^19)** | **2^5245** | 2^5062 | **FAILS by ~180 bits** |

## The structural conclusion
The bootstrap **fails even when fed the prize target as its own base case.** So the obstruction is NOT
a weak base case — it is the **method**: a magnitude-band split keeps only `|η_b|` sizes and the `L²`
mass, discarding the *cancellation* among the `η_b`. The Gaussian baseline's `(2r−1)!!` factor IS that
cancellation (only genuine matchings survive in the balanced-tuple count `E_r`); a two-band magnitude
argument cannot manufacture it and loses a multiplicative slack that dwarfs the target.

**Eliminated (per the "throw away what won't work" directive):** every analytic route that proves the
prize via a sup-norm / character-sum *magnitude* bound on `η_b` and then powers up — Weil, Burgess-type,
Gauss-sum size, dyadic pigeonhole, Rudin/Λ(2r) via sup-norm. None can reach `r ≈ ln p`.

**The ONLY surviving route:** prove cleanness of `M_r` by **directly counting spurious mod-`p`
collisions** among `r`-fold sums `Σ g^{e_i} ≡ Σ g^{e'_j}` of the geometric sequence `{g^e}` — i.e. show
the count of non-genuine balanced `2r`-tuples is `o(`Gaussian`)` for `r` up to `ln p`. This is the
combinatorial (counting) form of BCHKS Conj 1.12, and it is where the difficulty genuinely lives:
the cyclotomic norm/height gives no obstruction (no teeth at large `n`), so it is a pure anti-concentration
count with no known handle. **Still open. No closure claimed — this narrows the attack surface, it does
not cross the gate.**
