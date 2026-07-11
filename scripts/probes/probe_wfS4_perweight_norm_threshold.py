"""
#444 lane wf-S4 — the per-weight Stickelberger norm transfer threshold w_min >= p^{2/n}, measured.

A spurious config T (antipodal-free signed weight-w subset of mu_n) is spurious mod p iff
p | N_{Q(zeta_n)/Q}(sigma_T). The Galois group G = (Z/n)^* of order phi(n) = n/2 permutes the n/2
conjugates of sigma_T; each conjugate is a sum of w unit-modulus roots so |conj| <= w (triangle
ineq). Hence |N| = prod |conj| <= w^{n/2}, and a spurious config (N != 0, p | N) forces
  p <= |N| <= w^{n/2}   i.e.   w >= p^{2/n}.

This probe measures the true smallest collision weight w_min(n, beta) and compares it to the
Galois norm bound p^{2/n}. The point: the bound is SOUND but the exponent 2/n COLLAPSES at prize
scale (p^{2/n} = n^{2 beta / n} -> 1 as n grows at fixed beta), so the certificate is vacuous at
the prize while the deep moment band needs weight 2r ~ 2 beta ln n -> infinity.

Reference embedding (Galois-reduced search): by the t=1 coset structure a config lands in SOME
split prime iff its Galois orbit hits the fixed reference prime P_1 (ev: zeta -> h, h a primitive
n-th root mod p). So test sum eps_i h^{a_i} == 0 mod p over antipodal-free signed configs.
"""
import itertools, math


def is_prime(m):
    if m < 2:
        return False
    if m % 2 == 0:
        return m == 2
    i = 3
    while i * i <= m:
        if m % i == 0:
            return False
        i += 2
    return True


def prime_factors(n):
    f = set(); d = 2
    while d * d <= n:
        while n % d == 0:
            f.add(d); n //= d
        d += 1
    if n > 1:
        f.add(n)
    return f


def find_prime_beta(n, beta):
    t = max(n + 1, int(round(n ** beta)))
    p = t + (1 - t) % n
    while p % n != 1 or not is_prime(p):
        p += n
    return p


def prim_root_n(p, n):
    pf = prime_factors(n)
    for g in range(2, p):
        h = pow(g, (p - 1) // n, p)
        if pow(h, n, p) == 1 and all(pow(h, n // q, p) != 1 for q in pf):
            return h
    raise RuntimeError("no primitive n-th root")


def wmin(n, beta, wmax):
    """Smallest weight w (1..wmax) with a signed antipodal-free vanishing sum mod p; else None."""
    p = find_prime_beta(n, beta)
    h = prim_root_n(p, n)
    half = n // 2
    vals = [pow(h, a, p) for a in range(half)]  # half-set reps; +- = antipodal-free signed
    for w in range(1, wmax + 1):
        for combo in itertools.combinations(range(half), w):
            base = [vals[i] for i in combo]
            for signbits in range(1 << (w - 1)):  # fix first sign +
                s = base[0]
                for j in range(1, w):
                    s += (-base[j] if (signbits >> (j - 1)) & 1 else base[j])
                if s % p == 0:
                    return w, p
    return None, p


def main():
    print("=" * 92)
    print("wf-S4: measured w_min(n,beta) vs Galois norm bound p^{2/n} (= n^{2beta/n})")
    print("  certificate proves: NO spurious config of weight < p^{2/n}.  deep band weight ~ 2*beta*ln n.")
    print("=" * 92)
    print(f"{'n':>4} {'beta':>5} {'p':>10} {'w_min':>7} {'p^(2/n)':>9} {'2*beta*ln n':>12}  verdict")
    for n in [8, 16, 32]:
        wmax = 8 if n <= 8 else (7 if n == 16 else 6)
        for beta in [2.0, 3.0, 4.0]:
            wm, p = wmin(n, beta, wmax)
            bound = p ** (2.0 / n)
            depth = 2 * beta * math.log(n)
            wstr = str(wm) if wm is not None else f">{wmax}"
            ok = "BOUND-RESPECTED" if (wm is None or wm >= bound) else "VIOLATION(!!)"
            vac = "VACUOUS@prize" if bound < 2 else ""
            print(f"{n:>4} {beta:>5.1f} {p:>10} {wstr:>7} {bound:>9.3f} {depth:>12.2f}  {ok} {vac}")
    print("=" * 92)
    print("READING: p^{2/n} -> 1 as n grows (fixed beta), so the Galois/Stickelberger norm")
    print("  certificate covers only weight < ~1 at prize scale, while the deep band needs weight")
    print("  2*beta*ln n -> infinity. The norm route is SOUND but VACUOUS at the prize (the wall).")
    # prize-scale numeric witness
    n, beta = 2 ** 30, 4.0
    expo = 2 * beta * math.log(n) / n
    print(f"\nPRIZE SCALE n=2^30 beta=4: exponent 2*beta*ln n / n = {expo:.3e},")
    print(f"  p^(2/n) = exp(that) = {math.exp(expo):.10f}  (certifies only weight < ~1)")
    print(f"  deep band weight 2*beta*ln n = {2*beta*math.log(n):.2f}  (far beyond reach)")


if __name__ == "__main__":
    main()
