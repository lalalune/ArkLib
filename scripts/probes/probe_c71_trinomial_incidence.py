#!/usr/bin/env python3
"""
PROBE (#444 C71 residual, route-B 3-term strata): what is the SHARP mu_n-incidence law for a
GENUINE TRINOMIAL direction  f = X^i - c1 X^j - c2 X^k  (i>j>k, c1,c2 in mu_n nonzero)?

The binomial case reduced to a pure power equation x^{i-j}=c => exactly gcd(i-j,n) roots
(MultiplicativeRigidity.binomial_agree_card, ALREADY in tree). The trinomial does NOT reduce to a
single power equation. We test candidate NON-orbit, field/thickness-universal polynomial-method
upper bounds on  #{x in mu_n : f(x)=0}:

  (DEG)   #roots <= i - k                 [degree of the dehomogenised X^{i-k} - c1 X^{j-k} - c2]
  (SPARSE3) #roots <= 2*(i-k) ... NO; test the sparse/Descartes-style claims:
  (GCDSUM) #roots <= gcd(i-j,n) + gcd(j-k,n)   [naive union-of-binomials guess -- test if it even holds]
  (DEGN)  #roots <= min(i-k, n)            [trivial group-size cap]

Rules: PROPER thin mu_n = 2^a (a=2,3,4); p == 1 mod n with (p-1)/n >= 2 (NEVER n=q-1);
multi-prime incl p > n^3 and Fermat 257. We enumerate ALL genuine trinomial directions with
exponents < n (deg f < n prize regime) and c1,c2 in mu_n.
"""
import itertools, math

def roots_in_mun(p, n, exps, coeffs, gen_pow):
    # mu_n = {gen_pow^t : t in 0..n-1}, the order-n subgroup of F_p^*
    mun = [pow(gen_pow, t, p) for t in range(n)]
    cnt = 0
    i, j, k = exps
    c1, c2 = coeffs
    for x in mun:
        # f(x) = x^i - c1 x^j - c2 x^k  mod p
        val = (pow(x, i, p) - c1 * pow(x, j, p) - c2 * pow(x, k, p)) % p
        if val == 0:
            cnt += 1
    return cnt

def subgroup_gen(p, n):
    # find a generator of the unique order-n subgroup: g0^((p-1)/n) for a primitive root g0
    # crude primitive root finder
    def is_primitive(g):
        seen = set(); x = 1
        for _ in range(p-1):
            x = (x*g) % p
            seen.add(x)
        return len(seen) == p-1
    g0 = None
    for cand in range(2, p):
        if is_primitive(cand):
            g0 = cand; break
    return pow(g0, (p-1)//n, p)

def main():
    # (p, n) with p == 1 mod n, (p-1)/n >= 2, NEVER n = q-1
    cases = [
        (13, 4), (41, 8), (73, 4), (97, 8), (193, 16),
        (257, 16),   # Fermat, p>n^3? 16^3=4096 no -> below; structured
        (521, 8),    # p > n^3 = 512
        (4129, 16),  # p > n^3 = 4096
    ]
    deg_ok = sparse_ok = gcdsum_ok = True
    worst = []
    for (p, n) in cases:
        if (p - 1) % n != 0: 
            continue
        if (p - 1) // n < 2:
            continue
        g = subgroup_gen(p, n)
        mun = [pow(g, t, p) for t in range(n)]
        maxr = 0; maxinfo = None
        # all genuine trinomials i>j>k, exps < n, c1,c2 in mu_n
        for i, j, k in itertools.combinations(range(n), 3):
            i, j, k = max(i,j,k), sorted([i,j,k])[1], min(i,j,k)
            for c1 in mun:
                for c2 in mun:
                    r = roots_in_mun(p, n, (i, j, k), (c1, c2), g)
                    deg = i - k
                    gcdsum = math.gcd(i - j, n) + math.gcd(j - k, n)
                    if r > deg: deg_ok = False
                    if r > gcdsum: gcdsum_ok = False
                    if r > maxr:
                        maxr = r; maxinfo = (i, j, k, c1, c2, deg, gcdsum)
        worst.append((p, n, maxr, maxinfo))
        print(f"p={p:5d} n={n:3d}: max #roots over all genuine trinomials = {maxr}  "
              f"(deg cap i-k, gcdsum cap) at {maxinfo}")
    print()
    print(f"(DEG)    #roots <= i-k        : {'HOLDS' if deg_ok else 'FAILS'}")
    print(f"(GCDSUM) #roots <= g(i-j,n)+g(j-k,n): {'HOLDS' if gcdsum_ok else 'FAILS'}")

if __name__ == "__main__":
    main()
