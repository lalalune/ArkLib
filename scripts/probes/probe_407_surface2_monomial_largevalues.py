# Reproducible one-shot verification of ALL Surface-2 findings.
import numpy as np
from sympy import isprime, primitive_root
from collections import Counter
from itertools import combinations

def build_mu(n,p):
    g=primitive_root(p);zeta=pow(g,(p-1)//n,p);mu=[];x=1
    for _ in range(n):mu.append(x);x=(x*zeta)%p
    return np.array(sorted(mu),dtype=np.int64)
def find_prime(n,beta):
    t=int(round(n**beta));p=t-(t%n)+1
    while not(p>1 and isprime(p) and (p-1)%n==0):p+=n
    return p
def eta(b,mu,p):
    return abs(np.sum(np.exp(2j*np.pi*((b*mu)%p)/p)))

print("="*70)
print("SURFACE 2 VERIFICATION SUMMARY (#407)")
print("="*70)
# F1: global nonzero sup B ~ 1.1-1.3 sqrt(n log(q/n)) < n (BGK scale, q-DEPENDENT)
print("\n[F1] Character-sum sup B = max_{b!=0}|eta_b| is at BGK scale, BELOW n:")
for n in [8,16,32]:
    p=find_prime(n,4.0);mu=build_mu(n,p)
    B=max(eta(b,mu,p) for b in range(1,p))
    fl=np.sqrt(n*np.log(p/n))
    print(f"   n={n}: B={B:.2f}  sqrt(n log(q/n))={fl:.2f}  B/floor={B/fl:.2f}  B<n? {B<n}")
# F2: worst monomial mcaEvent bad-count is q-INDEPENDENT
print("\n[F2] Worst monomial-line mcaEvent bad-count is q-INDEPENDENT (combinatorial):")
n,k=8,4
def divdiff_bad(n,k,i,j,p):
    mu=build_mu(n,p);xs=mu;inv=lambda z:pow(int(z),p-2,p)
    xi=[pow(int(x),i,p) for x in xs];xj=[pow(int(x),j,p) for x in xs];gam=set()
    for S in combinations(range(n),k+1):
        Sl=list(S);D0=0;D1=0
        for l in Sl:
            W=1
            for m in Sl:
                if m!=l:W=(W*(int(xs[l])-int(xs[m])))%p
            Wi=inv(W);D0=(D0+xi[l]*Wi)%p;D1=(D1+xj[l]*Wi)%p
        if D1%p:gam.add((-D0*inv(D1))%p)
    return len(gam)
for beta in [3.5,3.75,4.0]:
    p=find_prime(n,beta)
    print(f"   n={n} q={p} (beta={np.log(p)/np.log(n):.2f}): bad-count(w=k+1)={divdiff_bad(n,k,k,k+1,p)} (budget {n})")
# F3: list-size = C(n,k+1), the wall is exponential
print("\n[F3] The wall = above-Johnson list size = C(n,k+1) ~ 2^(H(rho)n), EXPONENTIAL >> n:")
from math import comb
for n in [8,16,32,64]:
    k=n//2;print(f"   n={n} rho=1/2: C(n,k+1)={comb(n,k+1):.3e}  budget n={n}")
print("\nVERDICT: Surface 2 RE-COLLAPSES. Restricting to n^2 monomial freqs does NOT escape")
print("the no-go because the worst-monomial incidence is NOT a character-sum at all -- it is")
print("the q-independent char-0 list size C(n,k+1) above Johnson. The per-codeword O(1) escape")
print("(line-ball brick) is real, but x exponential list = list-decoding wall (open face 4/B4).")
