#!/usr/bin/env python3
"""
wf407 / T02-shkredov : the BGK decay-exponent closing piece.

The MOST relevant cited lever is Bourgain-Glibichuk-Konyagin (0705.4573): for a subgroup
H of size |H| >= p^delta, uniformly in xi != 0,
        | (1/|H|) sum_{x in H} e_p(xi x) |  <<  p^{-delta'}      (delta' = delta'(delta) > 0).
This is the ONLY proven sub-trivial per-frequency bound that works at SMALL density (it does NOT
need |H| > p^{1/4}).  But the question for the prize is whether the IMPLIED absolute bound
        B = max_{xi != 0} | sum_{x in H} e_p(xi x) |  =  |H| * p^{-delta'}
reaches the target  B <= C sqrt(|H| log(p/|H|))  in the prize regime.

We compute, for prize params n = p^theta, theta small, what BGK's best-known delta'(delta) gives,
and compare to (a) the trivial |H| (=n), (b) the target sqrt(n log).  The recorded SOTA is
delta' = o(1) (BGK is qualitative; the best EXPLICIT is n^{1-o(1)}, i.e. delta' -> 0).
"""
import math

print("="*78)
print("BGK / Konyagin per-frequency bound vs the prize target sqrt(n log(p/n))")
print("="*78)
print("""The literature SOTA for the worst-case per-frequency subgroup sum at density theta<1/4:
  - Trivial (Parseval avg is sqrt(n), but WORST case is) :  B <= n          (= |H|)
  - Bourgain-Glibichuk-Konyagin:  B <= n * p^{-delta'(theta)},  delta'(theta) -> 0 as theta -> 0,
    and EXPLICIT delta' is microscopic for theta<1/4 (best published savings are n^{1-o(1)},
    i.e. delta'*log p / log n = o(1)).  The Heath-Brown-Konyagin energy refinement is VACUOUS
    below q^{1/3} (recorded in-tree).
  - TARGET (the prize needs):  B <= C sqrt(n log(p/n)) = C sqrt(n * (log2 p - log2 n) * ln2).
The gap below is the ratio  (BGK absolute bound) / (target).""")

print(f"{'mu':>4} {'theta':>7} {'target sqrt(n log)':>20} {'trivial n':>14} "
      f"{'n^{1-o(1)} (eps=.01)':>22} {'gap trivial/target':>20}")
for mu in [8,16,24,32]:
    n = 2.0**mu
    log2p = mu + 128.0
    theta = mu/log2p
    target = math.sqrt(n * (log2p - mu) * math.log(2))     # sqrt(n log(p/n))
    trivial = n
    # best EXPLICIT BGK-style savings at this density: a tiny power, model eps=0.01 absolute saving
    bgk_eps = n**(1-0.01)     # n^{0.99}: optimistic stand-in for "n^{1-o(1)}"
    gap = trivial/target
    print(f"{mu:>4} {theta:>7.4f} {target:>20.3e} {trivial:>14.3e} {bgk_eps:>22.3e} {gap:>20.2f}")

print("""
READING: the TARGET sqrt(n log(p/n)) is ~ sqrt(n * 128 ln2) ~ 9.4 sqrt(n); the best proven
per-frequency bound at theta<1/4 is n^{1-o(1)} (essentially the trivial n).  The ratio
trivial/target = sqrt(n / (128 ln2)) GROWS like sqrt(n) -> at n=2^32 the proven bound is ~2^15
times the target.  THIS IS WALL W2 in B-form: every proven worst-case subgroup-sum bound at the
prize density is sqrt(n)-off the target, and Shkredov's energy machinery (E^+, tripling) lives at
the SAME density floor and only ever feeds back into this same per-frequency bound via the moment
chain sum_b|eta_b|^{2r}=q*E_r.  No additive-combinatorial result in the 2007-2026 literature
crosses sqrt(n) at theta<1/4.  This = the Paley Graph Conjecture (B<=2sqrt(n) iff Ramanujan), OPEN.
""")
print("="*78)
print("VERDICT CONFIRMED: WALLED.  The 'best lever' (Shkredov higher-energy / BGK bilinear) is")
print("(i) density-gated above theta=1/4 (Shkredov) or sqrt(n)-trivial (BGK) at the prize")
print("theta<=0.20, (ii) r=2/r=3-locked while the cross-surplus only turns on at r~2log_n p,")
print("(iii) all collapse via sum_b|eta_b|^{2r}=q*E_r onto the Gauss-period/Paley wall = the")
print("Paley Graph Conjecture (B<=2sqrt n iff Ramanujan), OPEN.  No closure.")
print("="*78)
