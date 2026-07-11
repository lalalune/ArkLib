import numpy as np, sympy
from collections import defaultdict
# DCWickBound G r  <=>  q*E_r^p  <=  q*(2r-1)!!*n^r + n^{2r}.
# Char-0 (mu_{2^k}) PROVEN: E_r^0 <= (2r-1)!!*n^r  (gaussianEnergyBound_dyadic).
# CLEAN conditional transfer brick (this probe's target):
#    q*(E_r^p - E_r^0)  <=  n^{2r}     ==>   DCWickBound G r  (char p).
# Measures excess := q*(E_r^p - E_r^0) vs slack n^{2r} in the THIN prize regime to r~log q.
# E_r = sum_v mult(v)^2 over the r-fold sumset.  Sparse dict convolution (no n^r enumeration).
# E_r^0 via a no-wraparound huge prime P0 >> n^(r+1) (mu_n lifted): there E_r^P0 = E_r^char0.

def Er_modp(p, r, mu_p):
    cur = defaultdict(int)
    for a in mu_p:
        cur[a % p] += 1
    for _ in range(r - 1):
        nxt = defaultdict(int)
        for v, c in cur.items():
            for a in mu_p:
                nxt[(v + a) % p] += c
        cur = nxt
    return sum(c*c for c in cur.values())

def dblfac(m):
    out = 1
    while m > 1:
        out *= m; m -= 2
    return out

def mu_modp(n, p):
    g = sympy.primitive_root(p); m = (p-1)//n
    return [pow(g, (m*s) % (p-1), p) for s in range(n)], m

print("Conditional DC-Wick transfer:  excess := q*(E_r^p - E_r^0)  vs  slack n^{2r}.")
print("excess <= slack  ==>  DCWickBound holds in char p.  (PROPER thin mu_n, p~n^beta, NEVER n=q-1)")
print("E_r^0 via no-wraparound huge prime P0 >> n^{r+1}.\n")

for n in [8, 16]:
    for p in [3329, 12289, 786433]:
        if (p - 1) % n: continue
        beta = np.log(p)/np.log(n); lnq = np.log(p)
        mu_p, m = mu_modp(n, p)
        assert len(set(mu_p)) == n and m > 1   # proper thin subgroup, never full group
        rmax = min(8, int(lnq) + 2)
        rows = []
        for r in range(1, rmax+1):
            need = n**(r+1) * 4
            P0 = int(sympy.nextprime(need))
            while (P0 - 1) % n: P0 = int(sympy.nextprime(P0))
            mu0, _ = mu_modp(n, P0)
            E0 = Er_modp(P0, r, mu0)
            Ep = Er_modp(p, r, mu_p)
            excess = p * (Ep - E0)
            slack = n ** (2*r)
            holds = excess <= slack
            dcw_margin = p * dblfac(2*r-1) * n**r + n**(2*r) - p * Ep
            rows.append((r, excess, slack, holds, dcw_margin, E0, Ep))
        print(f"n={n} p={p} beta={beta:.2f} (need r~{lnq:.0f}):")
        for r, ex, sl, h, dm, E0, Ep in rows:
            print(f"   r={r}: E0={E0} Ep={Ep} excess={ex:.3e} slack={sl:.3e} excess<=slack? {h} | DCWick margin={dm:+.3e}")
        print()
