# SHARPER cut: Q(zeta_{2^m}) for m>=3 contains Q(zeta_8) = Q(i, sqrt2) = Q(sqrt(-1),sqrt(2)).
# A primitive 2^m-th root g (m>=3) in F_p gives zeta_8 = g^{2^{m-3}}, so F_p contains i AND sqrt2.
# F_p contains sqrt2 iff 2 is a QR mod p iff p == +-1 mod 8. F_p contains i iff p==1 mod 4.
# Both => p == 1 mod 8. So for m>=3, ANY prime carrying mu_{2^m} has p==1 mod 8 (density 1/4 cut),
# and generally p==1 mod 2^min(m,?) ... actually p==1 mod 2^m is the FULL embedding condition.
# The NONTRIVIAL content: the s2s law refines to "norms are also of the form a^2-2b^2 (Q(sqrt2)) and
# a^2+2b^2 (Q(sqrt-2))" simultaneously -> bad primes must SPLIT in all three quadratic subfields.
# But for PRIZE primes p==1 mod 2^m this is automatic. The real cut is for SUB-prize / extension-field
# collisions (ord_n(p)>1). Test: do the weight-4 norm odd divisors split in Q(sqrt2) & Q(sqrt-2)?
import sympy as sp
from sympy import symbols, resultant, cyclotomic_poly, factorint, Poly
from itertools import combinations, product
x=symbols('x')

def legendre(a,p): return pow(a%p,(p-1)//2,p)

for m in [4,5]:
    n=2**m;half=n//2;Phi=Poly(cyclotomic_poly(n,x),x)
    odd=set()
    for combo in combinations(range(1,n),3):
        exps=(0,)+combo
        if any(abs(a-b)==half for a,b in combinations(exps,2)):continue
        for signs in product([1,-1],repeat=3):
            sg=(1,)+signs
            R=Poly(sum(s*x**e for e,s in zip(exps,sg)),x)
            if R.is_zero:continue
            N=abs(int(resultant(R.as_expr(),Phi.as_expr(),x)))
            for pr in factorint(N):
                if pr!=2:odd.add(pr)
    odd=sorted(odd)
    print(f"=== n={n} ===")
    # for each odd prime divisor, check: is it ==1 mod 4? ==+-1 mod 8 (2 is QR)? ==1 mod 8?
    for p in odd:
        m4=p%4; m8=p%8
        two_qr = (legendre(2,p)==1)  # 2 is QR
        i_in = (legendre(p-1,p)==1)  # -1 QR
        print(f"  p={p:5d} mod4={m4} mod8={m8} 2isQR={two_qr} -1isQR={i_in} mod{n}={p%n}")
