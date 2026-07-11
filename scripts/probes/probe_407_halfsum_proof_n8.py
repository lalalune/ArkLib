# For each antipodal-free sign pattern: alpha=sum u, beta=sum u^3 in Z[zeta_8].
# Bad primes = primes p where the degree-1 prime 𝔭 (zeta->h) divides BOTH alpha and beta.
# Compute the resultant Res(A,B) over Z[z]/Phi  AND the field norms; factor odd parts.
import sympy as sp
from itertools import product
z=sp.symbols('z')
Phi=sp.Poly(sp.cyclotomic_poly(8,z),z)   # z^4+1
def alpha_beta(eps):
    A=[0,0,0,0]; B=[0,0,0,0]
    for j in range(4):
        A[j]+=eps[j]
        e=(3*j)%8; s=1
        if e>=4: e-=4; s=-1
        B[e]+=s*eps[j]
    return sp.Poly(A[0]+A[1]*z+A[2]*z**2+A[3]*z**3,z), sp.Poly(B[0]+B[1]*z+B[2]*z**2+B[3]*z**3,z)
def fieldnorm(P):
    # N(P(zeta)) = Res_z(Phi, P) / lc(Phi)^deg  ; Phi monic so = Res(Phi,P)
    return int(sp.resultant(Phi.as_expr(), P.as_expr(), z))
allbad=set()
for eps in product([1,-1],repeat=4):
    A,B=alpha_beta(eps)
    if A.is_zero or B.is_zero:
        print(f"  {eps}: alpha or beta = 0 in Z[z] (char-0 antipodal relation; not a primitive U)"); continue
    Na=abs(fieldnorm(A)); Nb=abs(fieldnorm(B))
    g=sp.gcd(Na,Nb)
    # common prime ideal of degree 1 dividing both => p | resultant of A,B modulo Phi
    R=sp.resultant(A.as_expr(),B.as_expr(),z)   # eliminates z; common root => p|R (but ignores Phi)
    # refine: ideal (A,B,Phi) cap Z generator:
    Gz=sp.groebner([A,B,Phi],z,order='lex',domain='QQ')
    # content of certificate: clear denominators of the '1' representation is hard; use gcd(Na,Nb) odd part as the bound
    odd=g
    while odd%2==0: odd//=2
    print(f"  {eps}: N(a)={Na}, N(b)={Nb}, gcd={sp.factorint(g)}, gcd_ODD_part={odd}")
    if odd>1: allbad.add(odd)
print()
print("ODD common-norm factors across all patterns (upper bound on odd bad primes):", allbad if allbad else "NONE")
print("=> if NONE, n=8 has NO odd bad prime => Half-Sum Lemma PROVEN for n=8 (only char-2 degenerate).")
