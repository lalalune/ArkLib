import numpy as np
from sympy import primitive_root as pr

# Probe: validate the period-histogram tail-count bridge on a PROPER 2-power subgroup mu_n < F_p*.
# Claim: #{b!=0 : |eta_b|^2 > T} * T^r  <=  sum_{b!=0}|eta_b|^{2r}  = q*E_r - n^{2r}.
# Also confirm non-vacuity (filter nonempty near prize threshold T ~ n).

def test(p, n):
    g = pr(p)
    assert (p - 1) % n == 0, f"{n} does not divide {p-1}"
    h = pow(g, (p - 1) // n, p)          # generator of mu_n
    G = set()
    x = 1
    for _ in range(n):
        G.add(x); x = (x * h) % p
    G = sorted(G)
    assert len(G) == n
    w = np.exp(2j * np.pi / p)
    Gy = np.array(G)
    eta = np.zeros(p, dtype=complex)
    for b in range(p):
        eta[b] = np.sum(w ** ((b * Gy) % p))
    sq = np.abs(eta) ** 2
    assert abs(eta[0].real - n) < 1e-6   # eta_0 = n
    nz = sq[1:]                          # b != 0
    results = []
    for r in [1, 2, 3, 4]:
        S = np.sum(nz ** r)              # sum_{b!=0} |eta_b|^{2r}
        for Tfac in [1.0, 2.0, 4.0]:
            T = Tfac * n
            cnt = int(np.sum(nz > T))
            lhs = cnt * (T ** r)
            ok = lhs <= S + 1e-6
            results.append((r, Tfac, cnt, lhs, S, ok))
    return results, nz.max()   # FAR max (b != 0); the b=0 principal term |eta_0|^2 = n^2 is
                               # excluded (it is the DC term the cumulant identity subtracts).

cases = [(193, 16), (449, 64), (769, 16), (3329, 64), (7937, 64), (12289, 64)]
for (p, n) in cases:
    try:
        res, mx = test(p, n)
        beta = np.log(p) / np.log(n)
        print(f"\n=== p={p} n={n} beta={beta:.2f}  FAR max_(b!=0)|eta|^2={mx:.1f}  (n={n}, n^2={n*n}) ===")
        allok = all(r[5] for r in res)
        for r, Tf, cnt, lhs, S, ok in res:
            if Tf in (1.0, 2.0):
                print(f"  r={r} T={Tf}*n: #bad={cnt:3d}  lhs={lhs:.3e} <= S={S:.3e}  {ok}")
        print(f"  ALL inequalities hold: {allok}")
    except Exception as e:
        print(f"p={p} n={n}: SKIP ({e})")
