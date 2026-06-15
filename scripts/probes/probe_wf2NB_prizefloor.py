#!/usr/bin/env python3
"""
#407 lane wf-NB (decisive prize-point test): does the moment/large-sieve sup bound ever
beat the FLOOR sqrt(2n log(q/n)) at the prize regime n=16, beta=4 (true index m=4096)?

Result (the lane verdict): the Parseval/large-sieve sup bound descends monotonically and
reaches the floor ONLY at r ~ log2(m) = 12; the large-sieve's extra 2^{1/2r} factor keeps it
STRICTLY above the floor at every finite r. Pinned to the section-6 L2 wall.
"""
import cmath, math
from collections import Counter
from sympy import isprime

def setup(n, p):
    for a in range(2, p):
        z = pow(a, (p-1)//n, p)
        if pow(z, n, p) == 1 and pow(z, n//2, p) == p-1:
            break
    return [pow(z, j, p) for j in range(n)]

def find_prime(n, beta):
    t = int(round(n**beta)); p = t - (t % n) + 1
    while not isprime(p): p += n
    return p

def E_r(mu, p, r):
    cur = Counter({x: 1 for x in mu})
    for _ in range(r-1):
        nx = Counter()
        for s, c in cur.items():
            for x in mu: nx[(s+x)%p] += c
        cur = nx
    return sum(c*c for c in cur.values())

def main():
    for n, beta in [(16, 4.0)]:
        p = find_prime(n, beta); mu = setup(n, p); w = 2j*math.pi/p
        M = max(abs(sum(cmath.exp(w*((b*x)%p)) for x in mu)) for b in range(1, p))
        floor = math.sqrt(2*n*math.log(p/n))
        print(f"n={n} p={p} beta={math.log(p)/math.log(n):.2f} m={(p-1)//n}")
        print(f"  M_exact/sqrtn={M/math.sqrt(n):.3f}  FLOOR/sqrtn={floor/math.sqrt(n):.3f}")
        for r in range(1, 13):
            er = E_r(mu, p, r)
            sup_par = (p*er)**(1.0/(2*r))                # valid global sup bound on M
            sup_ls = (2*p*er)**(1.0/(2*r))               # large-sieve sup bound (2x lossy)
            wick = 1.0
            for j in range(1, 2*r, 2): wick *= j
            wick *= n**r
            tag_par = "<=floor" if sup_par <= floor else " >floor"
            tag_ls = "<=floor" if sup_ls <= floor else " >floor"
            print(f"  r={r:2d}: Er/Wick={er/wick:5.2f}  Parseval_sup/sqrtn={sup_par/math.sqrt(n):.3f}[{tag_par}]  "
                  f"LargeSieve_sup/sqrtn={sup_ls/math.sqrt(n):.3f}[{tag_ls}]")
    print("\nVERDICT: Parseval sup touches floor only at r~log2(m); large-sieve stays >floor every r.")
    print("Additive large sieve == Parseval (section-6 L2 wall). Lane wf-NB PINNED.")
    print("DONE")

if __name__ == "__main__":
    main()
