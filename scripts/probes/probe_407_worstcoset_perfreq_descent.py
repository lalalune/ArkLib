#!/usr/bin/env python3
"""
probe_407_worstcoset_perfreq_descent.py  (#444 -- the surviving NON-MOMENT residual)

THE SURVIVING HOPE (c.1263 verdict, board-wide): "the surviving hope is NOT a moment/cancellation
argument at all (both parities adverse) -- it must be a PER-FREQUENCY / STRUCTURAL estimate that
does NOT pass through the period MOMENTS."

Every prior per-frequency probe is either (a) the sup constant R=M/sqrt(n log m) stratified by
v2(INDEX m) (probe_supnorm_2adic_stratify), or (b) the worst-FREQUENCY half-coset alignment (REFUTED
c.287: thickness-monotone, carries no worst-freq info). UNPROBED: a per-frequency MULTIPLICATIVE
DESCENT of the worst-coset period itself,
    eta_{b*}(mu_n)  vs  eta_{?}(mu_{n/2}),
i.e. does the worst-coset period at level n RELATE STRUCTURALLY to a period at level n/2 (a
per-frequency tower recursion), WITHOUT averaging over b? A clean descent eta_{b*}(mu_n) =
f(eta(mu_{n/2})) with |f| contractive would give M(n) <= contraction * M(n/2) -> sqrt-type growth
by induction, a NON-MOMENT proof shape. We test whether such a per-frequency relation EXISTS and is
THINNESS-ESSENTIAL (rule 3) before any formalization.

KEY STRUCTURE: mu_n = mu_{n/2} u h*mu_{n/2} (h a generator coset rep, h^2 in mu_{n/2}). So for ANY b:
    eta_b(mu_n) = eta_b(mu_{n/2}) + eta_{b'}(mu_{n/2})   where the 2nd is the shifted coset sum.
This is EXACT and per-frequency (no average). The question: at the WORST b*, are the two half-coset
periods (i) phase-aligned (|eta_{b*}(mu_n)| ~ 2*|half|, NO cancellation -- bad, the c.287 refutation),
or (ii) is there a SIGNED structural relation that, iterated, contracts? We measure, at the exact
worst-coset b* (argmax over cosets), the ratio
    rho*(n) := |eta_{b*}(mu_n)| / max_b |eta_b(mu_{n/2})|     (per-frequency tower transfer ratio)
A per-frequency descent proof needs rho*(n) BOUNDED < 2 (sub-doubling) AND thinness-essential
(rho*_thick >= rho*_thin, i.e. thin contracts MORE). If rho* -> 2 (full doubling) OR is thickness-
invariant, the per-frequency descent is dead (the only remaining non-moment route closes).

Exact real periods eta_b = sum_{x in mu_n} cos(2pi b x / p) (mu_n negation-closed => real). PROPER
mu_n (m=(p-1)/n>1, NEVER n=q-1). Worst coset = argmax over coset reps b in {g^0..g^{m-1}} of |eta_b|.
Multi-prime incl. non-Fermat. Thick control: composite non-2-power n with its index-2 subgroup.
"""
import math, sys
from collections import defaultdict


def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d * d <= x:
        if x % d == 0: return False
        d += 2
    return True


def next_prime_cong1(n, lo):
    p = lo + (1 - lo % n) % n
    if p < lo: p += n
    while not is_prime(p):
        p += n
    return p


def factor(x):
    f = set(); d = 2
    while d * d <= x:
        while x % d == 0: f.add(d); x //= d
        d += 1
    if x > 1: f.add(x)
    return f


def primitive_root(p):
    fac = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise ValueError


def subgroup(p, n):
    """proper order-n subgroup mu_n = <h>, h=g^m, m=(p-1)/n>1 (never n=q-1)."""
    m = (p - 1) // n
    assert m > 1, "PROPER subgroup"
    g = primitive_root(p)
    h = pow(g, m, p)
    return [pow(h, j, p) for j in range(n)], g, m


def period(b, S, p, w):
    return sum(math.cos(w * ((b * x) % p)) for x in S)


MAXSCAN = 20000  # cap coset-rep scan; for larger m, sample uniformly (worst-coset estimate)


def worst_coset(S, p, g, m, w):
    """max |eta_b| over coset reps b = g^0..g^{m-1} (period depends only on coset b*mu_n).
    For m>MAXSCAN, scan a uniform stride sample (sup is a LOWER bound on the true max)."""
    best = -1.0; barg = 1
    if m <= MAXSCAN:
        b = 1
        for c in range(m):
            v = abs(period(b, S, p, w))
            if v > best:
                best = v; barg = b
            b = (b * g) % p
    else:
        stride = m // MAXSCAN
        gstride = pow(g, stride, p)
        b = 1
        for c in range(MAXSCAN):
            v = abs(period(b, S, p, w))
            if v > best:
                best = v; barg = b
            b = (b * gstride) % p
    return best, barg


def run(n, p, label):
    w = 2 * math.pi / p
    Sn, g, m = subgroup(p, n)
    # half subgroup mu_{n/2} = <h^2>
    h = Sn[1]
    Shalf = [pow(h, 2 * j, p) for j in range(n // 2)]
    Mn, bn = worst_coset(Sn, p, g, m, w)
    # worst over mu_{n/2}: its coset structure has index (p-1)/(n/2) = 2m reps; reuse g
    Mh, bh = worst_coset(Shalf, p, g, 2 * m, w)
    rho = Mn / Mh if Mh > 0 else float('inf')
    # the per-freq half-coset split at the worst b* of mu_n: eta_{b*}(mu_n) = A + B
    A = period(bn, Shalf, p, w)
    hb = h  # coset rep: mu_n \ mu_{n/2} = h*mu_{n/2}
    Bset = [(hb * x) % p for x in Shalf]
    B = period(bn, Bset, p, w)
    align = (A * B) / (abs(A) * abs(B)) if (A and B) else 0.0  # +1 aligned, -1 anti
    norm = math.sqrt(n * math.log(m)) if m > 1 else 1.0
    print(f"  [{label}] n={n} p={p} m={m}: M(n)={Mn:.3f} b*={bn} | M(n/2)={Mh:.3f} | "
          f"rho*=M(n)/M(n/2)={rho:.4f} | half-split A={A:.2f} B={B:.2f} align={align:+.3f} | "
          f"R=M/sqrt(n ln m)={Mn/norm:.3f}", flush=True)
    return rho, align


def main():
    print("=" * 90)
    print("PER-FREQUENCY worst-coset tower transfer rho*(n) = |eta_b*(mu_n)| / max_b|eta_b(mu_{n/2})|")
    print("  descent proof needs rho* BOUNDED < 2 (sub-doubling) AND thin contracts MORE (rule 3).")
    print("  align = sign(A*B) of the two half-coset periods at b*: +1 = NO cancellation (c.287 wall).")
    print("=" * 90)

    print("\n-- THIN: mu_n = 2-power subgroup, prize primes (incl. non-Fermat) --")
    for mu in (4, 5, 6, 7):
        n = 2 ** mu
        for beta in (4.0, 4.5):
            p = next_prime_cong1(n, int(n ** beta))
            fermat = bin(p - 1).count('1') == 1
            run(n, p, f"thin b={beta}{'/nf' if not fermat else ''}")

    print("\n-- THICK CONTROL (rule 3): composite non-2-power n, its index-2 subgroup --")
    for n in (12, 24, 20, 40):
        for beta in (4.0,):
            p = next_prime_cong1(n, int(n ** beta))
            try:
                run(n, p, f"thick b={beta}")
            except Exception as e:
                print(f"  [thick] n={n} p={p}: skip ({e})")

    print("\nREADING: if thin rho* -> 2 OR rho*_thin >= rho*_thick (thin doubles MORE / same), the")
    print("per-frequency descent is DEAD -- the worst coset doubles without thin-advantaged contraction,")
    print("and the last non-moment route closes. If thin rho* < 2 AND < thick, a live per-freq descent.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
