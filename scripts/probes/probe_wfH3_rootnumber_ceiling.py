#!/usr/bin/env python3
"""
Lane H3 (#444): is M(n) = max_b |eta_b| a special L-value reachable by subconvexity?

Verifies, with EXACT integer/algebraic structure (high-precision complex; errors are pure
floating-point ~1e-13, the identity is exact over Q(zeta)):

  (1) The L-function dictionary:  eta_b = (1/m) * sum_{chi in X_m} conj(chi)(b) * tau(chi),
      where X_m = the m = (p-1)/n characters TRIVIAL on mu_n, and |tau(chi)| = sqrt(p) EXACT.
      => eta_b = (sqrt(p)/m) * sum_{chi in X_m} conj(chi)(b) * eps(chi),  eps(chi)=tau/sqrt(p), |eps|=1.

  (2) The worst-b "root-number phase sum" |sum_chi conj(chi)(b) eps(chi)| lives in [sqrt(m), m]:
      sqrt(m)  = full square-root cancellation -> |eta| ~ sqrt(p/m) = sqrt(n) = Johnson/RMS.
      m        = trivial (coherent) -> |eta| ~ sqrt(p) = the VACUOUS Weil/completion bound (n<sqrt q).
      The prize wants |eta| <= C sqrt(n log m): sqrt-cancellation up to a sqrt(log m) defect.

  (3) Family-conductor mismatch (the dual of n<sqrt q): m = q/n = q^{(beta-1)/beta} = q^{3/4} at
      beta=4, ABOVE the Garcia-Young thin-coset window [q^{1/3}, q^{1/2}].

VERDICT: REDUCES-TO-FENCE (F2/F0). Subconvexity bounds |L(1/2,chi)| (the L-VALUE SIZE); the prize
cancellation lives in the modulus-1 root-number PHASE eps(chi), invisible to |L|-bounds. The
phase cancellation IS the open BGK/Paley wall.
"""
import cmath, math
try:
    import sympy
except ImportError:
    raise SystemExit("needs sympy: pip install sympy")


def check(n, p):
    g = sympy.primitive_root(p)
    m = (p - 1) // n
    gmu = pow(g, m, p)
    mu = []
    x = 1
    for _ in range(n):
        mu.append(x); x = x * gmu % p
    ep = lambda t: cmath.exp(2j * math.pi * (t % p) / p)
    eta = lambda b: sum(ep(b * x % p) for x in mu)
    dlog = {}
    x = 1
    for a in range(p - 1):
        dlog[x] = a; x = x * g % p
    def chi(k, t):
        t %= p
        return 0j if t == 0 else cmath.exp(2j * math.pi * (k * dlog[t]) / (p - 1))
    def tau(k):
        return sum(chi(k, t) * ep(t) for t in range(1, p))
    # identity max error over b
    iderr = max(
        abs(eta(b) - (1.0 / m) * sum(chi(n * j, b).conjugate() * tau(n * j) for j in range(m)))
        for b in range(1, min(p, 9))
    )
    # tau modulus flatness
    taunorm = max(abs(tau(n * j)) for j in range(1, m)) if m > 1 else abs(tau(0))
    # worst-b M and the phase-sum it corresponds to
    M = bestb = 0.0
    for b in range(1, p):
        v = abs(eta(b))
        if v > M: M = v; bestb = b
    phasemax = M / (math.sqrt(p) / m)
    return dict(m=m, iderr=iderr, taunorm=taunorm, sqp=math.sqrt(p),
                M=M, phasemax=phasemax, sqm=math.sqrt(m))


if __name__ == "__main__":
    print("(1) L-function dictionary  eta_b = (1/m) sum_{chi in X_m} conj(chi)(b) tau(chi),  |tau|=sqrt(p):")
    print(f"{'n':>3} {'p':>4} {'m':>3} {'id_err':>9} {'|tau|':>8} {'sqrt p':>8} {'M(n)':>8} {'M/sqrt n':>9} {'phase':>7} {'[sqrt m, m]':>14}")
    for n, p in [(8,17),(8,41),(8,73),(8,89),(16,97),(16,193),(16,257),(32,193),(32,257),(4,13),(4,29)]:
        if (p - 1) % n: continue
        r = check(n, p)
        inrange = "yes" if r['sqm'] - 1e-9 <= r['phasemax'] <= r['m'] + 1e-9 else "NO"
        print(f"{n:>3} {p:>4} {r['m']:>3} {r['iderr']:>9.1e} {r['taunorm']:>8.4f} {r['sqp']:>8.4f} "
              f"{r['M']:>8.4f} {r['M']/math.sqrt(n):>9.4f} {r['phasemax']:>7.3f} "
              f"[{r['sqm']:.2f},{r['m']}] {inrange}")

    print("\n(3) Family size m=q/n vs Garcia-Young thin-coset window [q^{1/3}, q^{1/2}]:")
    for beta in (3, 4, 5):
        e = (beta - 1) / beta
        flag = "INSIDE" if 1/3 <= e <= 1/2 else "ABOVE (too thick: dual of n<sqrt q)"
        print(f"  beta={beta}: m ~ q^{e:.4f}  -> {flag}")

    print("\nVERDICT: REDUCES-TO-FENCE F2/F0.")
    print(" - |tau(chi)| = sqrt(p) EXACT (flat); subconvexity on |L(1/2,chi)| gives ZERO modulus info.")
    print(" - modulus-only (triangle) bound => |eta| <= sqrt(p) = VACUOUS completion bound (n<sqrt q).")
    print(" - prize cancellation lives in the modulus-1 phase eps(chi); = the open BGK/Paley wall.")
