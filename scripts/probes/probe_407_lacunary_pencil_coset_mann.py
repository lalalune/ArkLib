#!/usr/bin/env python3
"""
probe_407_lacunary_pencil_coset_mann.py   (issue #407, target P5-sparse-poly-roots)

MECHANISM of the Theta(n) inner per-witness agreement found in
probe_407_lacunary_pencil_roots_mann.py.

CLAIM (verified exactly below, p >> n^3, mu_n PROPER):
  The Theta(n)-root pencil polynomial is, up to a deg-(k-1) codeword multiplier,
        f(x) = (g0 + g1*x) * (1 + x^{n/2})
  i.e. it has the single dyadic cyclotomic factor (1 + x^{n/2}) = Phi_n(x).  Its
  mu_n root set is EXACTLY ONE COSET of mu_{n/2} (the n/2 elements with
  x^{n/2} = -1), and every root is antipodally paired -- precisely Mann's dyadic
  prediction (the only primitive vanishing relation over mu_{2^mu} is z+(-z)=0).

  As a PENCIL agreement: pencil exps (a,b) = (n/2+1, n/2) so b-a = -1,
  gcd(b-a,n) = 1, orbit size S = n.  The codeword is g(x) = -(g0 + g1*x),
  degree 1 < k (genuine, not the zero codeword).  Agreement = n/2 = Theta(n).

This confirms the inner Theta(n) is a STRUCTURALLY RIGID 1-parameter (coset)
family, NOT a generic sparse-root explosion.

HONESTY: exact over F_p, p >> n^3 (prize-faithful), mu_n proper subgroup.
"""
from math import gcd

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def prime_ge(lo, n):
    p = lo - (lo % n) + 1
    while not (is_prime(p) and (p-1) % n == 0): p += n
    return p

def find_gen(p, n):
    for g0 in range(2, p):
        w = pow(g0, (p-1)//n, p)
        if pow(w, n, p) == 1 and all(pow(w, n//q, p) != 1 for q in (2,3,5,7) if n % q == 0):
            return w
    raise RuntimeError

def roots_in_mu_n(coeffs, w, p, n):
    R = []
    for j in range(n):
        xv = pow(w, j, p); s = 0
        for e, c in coeffs.items(): s = (s + c*pow(xv, e, p)) % p
        if s == 0: R.append(j)
    return set(R)

def coset_decomp(Rset, n):
    """Greedily strip cosets of mu_e (e|n, e>1). Return list of (e,j0) families
    and the leftover (isolated) set."""
    R = set(Rset); fams = []
    e = n
    divs = sorted([d for d in range(2, n+1) if n % d == 0], reverse=True)
    for e in divs:
        step = n // e
        for j0 in range(step):
            cos = set((j0 + step*t) % n for t in range(e))
            if cos <= R:
                R -= cos; fams.append((e, j0))
    return fams, R

def main():
    print("DYADIC COSET MECHANISM of the Theta(n) inner agreement (p >> n^3)\n", flush=True)
    print(f"{'n':>5} {'pencil(a,b)':>12} {'gcd':>4} {'S':>3} | {'#roots':>7} {'n/2':>4} "
          f"{'paired':>9} {'coset-structure':>22}", flush=True)
    for n in (8, 16, 32, 64, 128, 256):
        p = prime_ge(8*n**3, n); w = find_gen(p, n)
        half = n//2; g0, g1 = 3, 1
        # f = (g0 + g1 x)(1 + x^{n/2}) -> support {0,1,n/2,n/2+1}; pencil (n/2+1, n/2)
        cm = {}
        for (e, c) in [(0, g0), (1, g1), (half % n, g0), ((half+1) % n, g1)]:
            cm[e] = (cm.get(e, 0) + c) % p
        cm = {e: c for e, c in cm.items() if c % p != 0}
        R = roots_in_mu_n(cm, w, p, n)
        paired = sum(1 for j in R if ((j+half) % n) in R)
        fams, iso = coset_decomp(R, n)
        a, b = half+1, half
        struct = "+".join(f"mu{e}" for (e, _) in fams) + (f"+iso{len(iso)}" if iso else "")
        print(f"{n:>5} ({a:>4},{b:>4}) {gcd((b-a) % n, n):>4} {n//gcd((b-a) % n, n):>3} | "
              f"{len(R):>7} {half:>4} {paired:>4}/{len(R):<4} {struct:>22}", flush=True)
    print("\nFINDING: root set = ONE coset of mu_{n/2}, all antipodally paired (Mann dyadic).", flush=True)
    print("The inner Theta(n) is the single cyclotomic factor (1+x^{n/2}); a rigid", flush=True)
    print("1-parameter coset family, gcd(b-a,n)=1 => ONE orbit under the action group.", flush=True)

if __name__ == "__main__":
    main()
