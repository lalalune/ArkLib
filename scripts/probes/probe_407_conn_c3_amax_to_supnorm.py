#!/usr/bin/env python3
"""
#407 C3 (part 3) — does the count-driven energy upper bound  E_r <= a_max^0 * n^r  give a
NON-TRIVIAL bound on the SUP-NORM M = max_{b!=0}|eta_b|, the actual prize quantity?

Established (part 2): in the non-saturated/prize regime,
    a_max(c) is q-INDEPENDENT and equals the char-0 max multiplicity a_max^0,
    and  E_r = E_r^0 (char-0 energy)  exactly.
So  E_r <= a_max^0 * n^r  is a q-independent upper bound on the energy.

THE SUP-NORM CHAIN. From the exact Fourier identity
    A_r := E_r - n^{2r}/p = (1/p) * sum_{b != 0} |eta_b|^{2r}  >=  (1/p) * M^{2r}.
=>  M^{2r} <= p * A_r = p*(E_r - n^{2r}/p) = p*E_r - n^{2r}.
This has an explicit factor of p (q). With E_r <= a_max^0 * n^r:
    M^{2r} <= p*a_max^0*n^r - n^{2r}.       (***)
For the prize p=n^beta this is  M^{2r} <~ n^{beta} * a_max^0 * n^r,  giving
    M <= (n^beta a_max^0)^{1/2r} * n^{1/2} = n^{1/2} * (n^beta a_max^0)^{1/2r}.
As r -> inf this -> n^{1/2}*1 = sqrt(n) (the TRUE order ~ sqrt(n log) but with the wrong log).
BUT for a SINGLE fixed r the factor (n^beta)^{1/2r} = n^{beta/2r} INFLATES the bound (q-DEPENDENT!).
So the *energy* bound on M carries an irreducible factor n^{beta/2r}: it is q-DEPENDENT and only
becomes sqrt-order as r-> infinity. THIS IS THE MOMENT METHOD and it is exactly the BGK wall.

THE HONEST QUESTION C3 ASKS: does the COUNT a_max^0 (q-independent) help AT ALL?
Two things to measure:
  (Q1) How does a_max^0 SCALE with n (fixed r) and with r (fixed n)? Does the energy bound
       E_r <= a_max^0 n^r match the char-0 Wick (2r-1)!! n^r (the TRUE sqrt-cancellation energy),
       or is it weaker (capping at a Johnson-like value)?
       Specifically: a_max^0 vs (2r-1)!! (the Wick energy is sum a^2 = (2r-1)!! n^r, and
       a_max^0 <= sqrt(E_r^0) = sqrt((2r-1)!! n^r) by a^2<=E. Is a_max^0 ~ (2r-1)!! or ~ sqrt?).
  (Q2) Compare M (computed exactly for small n,p) to the energy bound (***) and to sqrt(2n ln p).
       Does the count-driven energy bound ever BEAT the trivial M<=n or the Wick M<=sqrt(2n ln p)?
"""
import sys, itertools, math
from collections import Counter
from sympy import isprime, primitive_root

def first_prime_1modn(n, lo):
    p = lo - (lo % n) + 1
    if p <= lo: p += n
    while not isprime(p): p += n
    return p

def primitive_nth_root(n, p):
    g = primitive_root(p)
    return pow(g, (p - 1)//n, p)

def char0_coord(exps, n):
    half = n//2; v = [0]*half
    for e in exps:
        e %= n
        if e < half: v[e]+=1
        else: v[e-half]-=1
    return tuple(v)

def char0_a(n, r):
    a = Counter()
    for tup in itertools.product(range(n), repeat=r):
        a[char0_coord(tup, n)] += 1
    return a

def dfact(k):
    res=1
    while k>0: res*=k; k-=2
    return res

def exact_supnorm(n, p):
    """M = max_{b!=0} |eta_b|, eta_b = sum_{x in mu_n} e_p(b x).  By symmetry eta_b depends on the
    coset b*mu_n; compute |eta_b|^2 = sum_{x,y} cos(2pi b(x-y)/p)."""
    import cmath
    w = primitive_nth_root(n, p)
    roots = [pow(w,j,p) for j in range(n)]
    best = 0.0
    seen = set()
    # eta_b only depends on b up to mult by mu_n and the value; just scan a representative set.
    # Scan all b in 1..p-1 is too big for large p; scan b over the n cosets reps won't capture all.
    # For moderate p scan all b; cap.
    if p <= 20000:
        for b in range(1, p):
            s = 0j
            for x in roots:
                ang = 2*math.pi*(b*x % p)/p
                s += complex(math.cos(ang), math.sin(ang))
            m = abs(s)
            if m > best: best = m
    else:
        best = None
    return best

def main():
    print("="*100)
    print("C3 part 3: does count-driven a_max^0 give a NON-TRIVIAL sup-norm bound, or is it the moment wall?")
    print("="*100)

    print("\n(Q1) a_max^0 scaling: char-0 max multiplicity vs Wick energy (2r-1)!! n^r and sqrt(E^0).")
    print(f"{'n':>5} {'r':>3} {'a_max^0':>9} {'E_r^0':>12} {'(2r-1)!!n^r':>14} {'sqrt(E^0)':>10} "
          f"{'a0/(2r-1)!!':>11} {'a0/n^(r-1)':>10}")
    rows = []
    for mu in [3,4,5]:
        n = 2**mu
        for r in [2,3,4]:
            if n**r > 5_000_000: continue
            a0 = char0_a(n, r)
            am = max(a0.values()); E0 = sum(v*v for v in a0.values())
            wick = dfact(2*r-1)*n**r
            print(f"{n:>5} {r:>3} {am:>9} {E0:>12} {wick:>14} {math.sqrt(E0):>10.1f} "
                  f"{am/dfact(2*r-1):>11.2f} {am/n**(r-1):>10.3f}")
            rows.append((n,r,am,E0,wick))

    print("\n  Interpretation: the energy upper bound E_r <= a_max^0 * n^r is TIGHT vs Wick iff")
    print("  a_max^0 * n^r ~ (2r-1)!! n^r, i.e. a_max^0 ~ (2r-1)!!. If a_max^0 << (2r-1)!! the count")
    print("  bound is WEAKER than the true (Wick) energy; if ~ it recovers Wick (good but already known).")

    print("\n(Q2) exact M vs energy-derived bound vs Wick sqrt(2n ln p). [small p only]")
    print(f"{'n':>5} {'r':>3} {'p':>8} {'M(exact)':>9} {'M_eng=(pE-n^2r)^(1/2r)':>22} "
          f"{'sqrt(2n ln p)':>13} {'n':>5}")
    for mu in [3,4]:
        n=2**mu
        for p in [first_prime_1modn(n, 200), first_prime_1modn(n, 2000)]:
            M = exact_supnorm(n,p)
            if M is None: continue
            for r in [2,3]:
                if n**r > 2_000_000: continue
                a0 = char0_a(n,r); E0=sum(v*v for v in a0.values())
                # energy bound on M: M^{2r} <= p*E0 - n^{2r}  (using E_r=E0 in non-sat regime)
                val = p*E0 - n**(2*r)
                M_eng = val**(1.0/(2*r)) if val>0 else float('nan')
                wickbnd = math.sqrt(2*n*math.log(p))
                print(f"{n:>5} {r:>3} {p:>8} {M:>9.3f} {M_eng:>22.3f} {wickbnd:>13.3f} {n:>5}")

if __name__ == "__main__":
    main()
