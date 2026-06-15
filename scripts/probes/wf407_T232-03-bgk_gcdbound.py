#!/usr/bin/env python3
"""
wf407 / T232-03-bgk : the RIGOROUS algebraic magnitude bound on M.

M = #{u in F_p : u^n=1 and (1+u)^n=1} = #common roots of  f=X^n-1 and g=(X+1)^n-1  in F_p.
=> M <= deg gcd(f,g) over F_p.  Also g - f = (X+1)^n - X^n - 0 ... let's see exact degree drop.
   (X+1)^n - 1 - (X^n - 1) = (X+1)^n - X^n = n X^{n-1} + ... (degree n-1).
So every common root of f,g is a root of h1 := (X+1)^n - X^n, deg n-1.
Iterate: common roots of f and h1; h1 has degree n-1. The resultant / gcd chain bounds M.

KEY structural facts to MEASURE exactly:
  (i)  deg gcd(X^n-1, (X+1)^n-1) over F_p  -- and M <= that.
  (ii) Over C (char 0): gcd = 1 always (M=0). The gcd jumps only mod special primes.
  (iii) Connect deg-gcd to the resultant Res(X^n-1,(X+1)^n-1): char p | this resultant <=> gcd>0.
       This resultant = prod over roots, its prime factors are EXACTLY the bad primes.
       Magnitude of M at a bad prime p = multiplicity structure of p in the resultant / valuation.

We also test the central magnitude question with an INDEPENDENT bound:
   Weil bound for the curve x+y=c on (mu_n)^2: writing x=t^{(p-1)/n}, this is a fibered
   character-sum; |M - n^2/p| <= (n-1)*sqrt(p)/... -> for n^2 << p, M is forced by an arithmetic
   (gcd/resultant), NOT analytic, mechanism. Confirm M is bounded by an n-only quantity via gcd.
"""
from sympy import primerange, GF, Poly, symbols, gcd as sgcd
from sympy import ZZ

X = symbols('X')

def deg_gcd_mod_p(n, p):
    """deg of gcd(X^n-1, (X+1)^n-1) over F_p, computed with sympy GF."""
    dom = GF(p)
    f = Poly(X**n - 1, X, domain=dom)
    g = Poly((X+1)**n - 1, X, domain=dom)
    d = sgcd(f, g)
    return d.degree()

def M_count(n,p):
    # count roots u in F_p of both
    cnt=0
    for u in range(p):
        if pow(u,n,p)==1 and pow((u+1)%p,n,p)==1:
            cnt+=1
    return cnt

def main():
    print("M  vs  deg gcd(X^n-1,(X+1)^n-1) mod p   (M <= deg gcd; equality measures multiplicity)")
    print(f"{'n':>4} {'p':>7} {'M':>4} {'deg_gcd':>8}  note")
    print("-"*54)
    samples=[(8,17),(8,41),(8,73),(16,17),(16,97),(16,257),(32,97),(32,193),(32,257),
             (64,193),(64,257),(64,641),(64,7937),(128,257),(128,769)]
    for n,p in samples:
        if (p-1)%n:
            # still may have roots if n | order though we need mu_n full; skip if n does not divide p-1
            pass
        try:
            dg=deg_gcd_mod_p(n,p)
        except Exception as e:
            dg=f"err:{e}"
        M=M_count(n,p)
        note = "M=deg_gcd" if M==dg else ("M<deg_gcd (multiplicity)" if isinstance(dg,int) and M<dg else "")
        print(f"{n:>4} {p:>7} {M:>4} {str(dg):>8}  {note}")

    print("\nResultant prime-factor structure (the EXACT bad-prime set + the magnitude):")
    print("Res(X^n-1,(X+1)^n-1) over Z, factored -> bad primes are its prime divisors.")
    from sympy import resultant, factorint
    for n in [2,4,8,16]:
        f=Poly(X**n-1,X,domain=ZZ); g=Poly((X+1)**n-1,X,domain=ZZ)
        R=resultant(f.as_expr(), g.as_expr(), X)
        R=int(R)
        fac=factorint(abs(R)) if R!=0 else {}
        print(f"   n={n}: Res = {R}, |Res| factor = {fac}")

if __name__=="__main__":
    main()
