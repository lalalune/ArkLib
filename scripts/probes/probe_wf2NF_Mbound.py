import math
from sympy import isprime, primitive_root
from collections import Counter

def subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S=[]; x=1
    for _ in range(n):
        S.append(x); x=(x*h)%p
    return S

# eta_b = sum_{x in S} e_p(b x). M = max_{b!=0} |eta_b|.
# Moment identity: sum_b |eta_b|^{2r} = q * E_r(S). For r=2: sum_b |eta_b|^4 = q*E2.
# Including b=0: eta_0 = n, contributes n^4. So sum_{b!=0}|eta_b|^4 = q*E2 - n^4.
# M^4 <= sum_{b!=0}|eta_b|^4 = q*E2 - n^4.  => M <= (q*E2 - n^4)^{1/4}.
# With E2 = 3n^2-3n, q~n^4: M <= (n^4 * 3n^2)^{1/4} = (3)^{1/4} n^{6/4} = n^{1.5} * 3^.25
# So r=2 energy gives M <= ~n^{1.5}. The FLOOR is sqrt(n)=n^0.5. Johnson-ish.
print(f"{'n':>5} {'p':>12} {'M_true':>9} {'M_true/sqrtn':>12} {'r2bound':>10} {'r2/sqrtn':>9} {'sqrt(n)':>8}")
for n in [8,16,32,64,128,256]:
    p=n**4
    while not (isprime(p) and (p-1)%n==0): p+=1
    S=subgroup(p,n)
    # compute M_true exactly via Gauss periods (small n only)
    if n<=256:
        import cmath
        best=0
        # only need max over coset reps; just brute b=1..min(p,..) is too big. Use that |eta_b| depends on coset of b under mu_n. m=(p-1)/n cosets.
        g=primitive_root(p)
        m=(p-1)//n
        for c in range(min(m,4000)):
            b=pow(g,c,p)
            val=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in S)
            a=abs(val)
            if a>best: best=a
        Mtrue=best
    E2=3*n*n-3*n
    r2=(p*E2 - n**4)**0.25
    print(f"{n:>5} {p:>12} {Mtrue:>9.3f} {Mtrue/math.sqrt(n):>12.4f} {r2:>10.2f} {r2/math.sqrt(n):>9.3f} {math.sqrt(n):>8.3f}")
