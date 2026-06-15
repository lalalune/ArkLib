# CORE OBSTRUCTION TEST: Gross-Koblitz pins the p-ADIC unit of tau via Gamma_p.
# The floor is ARCHIMEDEAN |.|_inf. Does the Gamma_p / p-adic data determine the complex phase?
#
# Sharpest diagnostic: the ONE case where Gamma_p (via reflection Gamma_p(x)Gamma_p(1-x)=+-1) DOES
# pin the COMPLEX phase exactly is the QUADRATIC Gauss sum (chi = Legendre symbol, m=2):
#   tau(quadratic) = sqrt(p) if p=1 mod 4, i*sqrt(p) if p=3 mod 4  (Gauss's theorem, sign+phase EXACT)
# This is the in-tree QuadraticGaussSumMagnitude success. For HIGHER order m, the sign/phase is NOT
# determined by a clean Gamma_p reflection -- it requires the full Gross-Koblitz product over digits,
# whose ARCHIMEDEAN realization is an arbitrary embedding C_p -> C (NON-canonical).
#
# TEST 1: confirm m=2 phase is rigidly +-1 / +-i (Gamma_p reflection works).
# TEST 2: for m>2, show the complex phase arg(tau) is NOT a function of the p-adic valuation data
#         (Stickelberger digits), i.e. two primes with same Stickelberger digit-pattern give
#         DIFFERENT complex phases => p-adic data underdetermines archimedean phase.
import math, cmath
def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True
def primroot(p):
    fac=set(); mm=p-1; d=2
    while d*d<=mm:
        if mm%d==0:
            fac.add(d)
            while mm%d==0: mm//=d
        d+=1
    if mm>1: fac.add(mm)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a
def quad_gauss(p):
    s=sum(cmath.exp(2j*math.pi*(x*x%p)/p) for x in range(p))
    return s

print("TEST 1: quadratic Gauss sum phase (Gamma_p reflection EXACTLY pins this)")
print("p    p%4   tau/sqrt(p) (should be 1 if p=1mod4, i if p=3mod4)")
for p in [5,13,17,29,37,7,11,19,23,31]:
    g=quad_gauss(p)
    print(f"{p:<5}{p%4:<6}{g/math.sqrt(p):.4f}")

print()
print("TEST 2: for m=3 (cubic), is complex arg(tau) determined by p mod (small)?")
print("Two primes p=1 mod 3 with same residue class structure -> compare arg(tau_1)")
def cubic_taus(p):
    # need 3 | p-1
    g0=primroot(p)
    dlog=[0]*p; cur=1
    for t in range(p-1):
        dlog[cur]=t; cur=cur*g0%p
    ep=[cmath.exp(2j*math.pi*x/p) for x in range(p)]
    # character of order 3
    s=sum(cmath.exp(2j*math.pi*dlog[x]/3)*ep[x] for x in range(1,p))
    return s
print("p     arg(tau_cubic)/pi   tau/sqrt(p)")
for p in range(7,200):
    if isprime(p) and p%3==1:
        t=cubic_taus(p)
        print(f"{p:<6}{cmath.phase(t)/math.pi:<18.4f}{t/math.sqrt(p):.4f}")
