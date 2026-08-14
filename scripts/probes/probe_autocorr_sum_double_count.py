# Exact multiplicative-autocorrelation double-count over a finite field F_p*:
#   sum_{rho in F_p*} |S cap rho*S| = r^2   (each (a,b) in SxS gives a UNIQUE rho = a*b^{-1})
#   => sum_{rho != 1} |S cap rho*S| = r^2 - r = r*(r-1)   EXACT, field-universal, sign-free.
# This is the EXACT total that the pencil max-M Cauchy-Schwarz route only ever uses the MAX of.
# Verified on PROPER thin subgroups mu_n in F_p* (never n=q-1), multiple primes incl p>n^3 + Fermat 257.
import random

def subgroup(p, n):
    if (p - 1) % n:
        return None
    e = (p - 1) // n
    for a in range(2, p):
        g = pow(a, e, p)
        S = [pow(g, j, p) for j in range(n)]
        if len(set(S)) == n:
            return S
    return None

ok = True
configs = [(17, 8), (41, 8), (73, 8), (97, 16), (193, 16), (257, 16), (4129, 16), (40961, 16)]
for (p, n) in configs:
    mu = subgroup(p, n)
    if mu is None:
        continue
    muL = sorted(set(mu))
    for trial in range(8):
        r = random.randint(2, n)
        S = set(random.sample(muL, r))
        # full sum over ALL rho in F_p* (rho ranges over the whole field group, not just mu)
        tot_all = 0
        for rho in range(1, p):
            rhoS = set((rho * x) % p for x in S)
            tot_all += len(S & rhoS)
        tot_nontriv = tot_all - r  # subtract rho=1 term (|S cap S| = r)
        expect = r * (r - 1)
        if tot_all != r * r or tot_nontriv != expect:
            print(f"MISMATCH p={p} n={n} r={r}: tot_all={tot_all} (exp {r*r}) tot_nontriv={tot_nontriv} (exp {expect})")
            ok = False
print("ALL EXACT (sum_{rho!=1}|S cap rho S| = r(r-1))" if ok else "FAILED")
