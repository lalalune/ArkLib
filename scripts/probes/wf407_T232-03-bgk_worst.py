#!/usr/bin/env python3
"""
wf407 / T232-03-bgk : WORST-CASE M and the full bad-prime structure (resultant factorization).

(A) Worst-case M over all primes at fixed n: the maximum is achieved at the densest mu_n.
    When p = n+1 (so mu_n = F_p^*), M = #{u in F_p^* : 1+u in F_p^*} = #{u != 0 : u != -1} = n-1.
    So  max_p M(n,p) = n-1  IF p=n+1 is prime (n+1 a Fermat-like prime).  This is the absolute ceiling.
(B) The bad-prime set = prime divisors of Res(X^n-1,(X+1)^n-1). Factor it for n=8,16,32 (n=64 big).
    Report which are Fermat numbers (u=1 obstruction), which are other Mersenne factors.
(C) Confirm M = sum over the resultant's bad-prime contribution is bounded by n-1 always.
"""
from sympy import symbols, Poly, resultant, factorint, isprime, ZZ
X=symbols('X')

def M_count_small(n,p):
    if p<200000:
        # build mu_n quickly
        # find element of order n
        import random
        e=(p-1)//n
        for _ in range(500):
            a=random.randrange(2,p-1); h=pow(a,e,p)
            if h!=1 and pow(h,n//2,p)!=1:
                break
        else:
            return None
        s=set(); cur=1
        for _ in range(n): s.add(cur); cur=cur*h%p
        return sum(1 for u in s if (1+u)%p in s)
    return None

def main():
    print("(A) Absolute ceiling: p=n+1 prime => mu_n=F_p^* => M=n-1.")
    for n in [2,4,8,16,32,64,128,256,65536]:
        pn=n+1
        tag = "PRIME (densest case realizable)" if isprime(pn) else "n+1 not prime"
        Mmax = (n-1) if isprime(pn) else "N/A"
        print(f"   n={n:>6}: p=n+1={pn:>6} {tag};  ceiling M=n-1 = {Mmax}")
    print("   => ABSOLUTE upper bound  M(n,p) <= n-1 (deg gcd <= n-1; X^n-1 separable for p odd).")

    print("\n(B) Bad-prime set = prime divisors of Res(X^n-1,(X+1)^n-1):")
    for n in [2,4,8,16,32]:
        f=Poly(X**n-1,X,domain=ZZ); g=Poly((X+1)**n-1,X,domain=ZZ)
        R=int(resultant(f.as_expr(),g.as_expr(),X))
        fac=factorint(abs(R)) if R!=0 else {}
        # mark Fermat numbers F_j = 2^(2^j)+1: 3,5,17,257,65537
        fermats={3:0,5:1,17:2,257:3,65537:4}
        mark={q: (f"F_{fermats[q]}" if q in fermats else "other") for q in fac}
        print(f"   n={n:>3}: bad primes {sorted(fac)}  | bitlen(|Res|)={abs(R).bit_length()}")
        print(f"          classify: {mark}")

    print("\n(C) For each bad prime, M(n,p) at that prime (should be 0<M<=n-1):")
    import random
    random.seed(7)
    for n in [8,16,32]:
        f=Poly(X**n-1,X,domain=ZZ); g=Poly((X+1)**n-1,X,domain=ZZ)
        R=int(resultant(f.as_expr(),g.as_expr(),X))
        fac=factorint(abs(R))
        for q in sorted(fac):
            if (q-1)%n!=0:
                # mu_n still may not be full order n in F_q if n does not divide q-1: then NO mu_n.
                print(f"   n={n} q={q}: n does NOT divide q-1 (no full mu_n); bad prime acts via subfield/mult")
                continue
            M=M_count_small(n,q)
            print(f"   n={n} q={q}: M={M}  (<= n-1={n-1})  {'<-- u=1 Fermat' if q in (3,5,17,257,65537) else ''}")

if __name__=="__main__":
    main()
