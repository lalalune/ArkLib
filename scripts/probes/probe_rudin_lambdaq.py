"""
The Rudin / Lambda(q) harmonic-analysis route: eta_b = sum_{x in mu_n} e_p(bx) is an n-sparse trig poly in b.
The prize ||eta||_{L^q(b)} ~ sqrt(q)*sqrt(n) at q=log m IS a Lambda(q) / Rudin inequality for the frequency
set mu_n. Rudin: for a SIDON set S, ||sum a_s e(s b)||_q <= sqrt(q) ||a||_2. mu_n is 'Sidon-except-negation'
(E_2=3n^2-3n vs Sidon 2n^2-n; excess n^2-2n = antipodal). Test: is ||eta||_q <= C sqrt(q) sqrt(n)?
Compute the L^q norm of eta over b for growing q, and the Lambda(q) constant ||eta||_q / (sqrt(q) sqrt(n)).
"""
import math
def isprime(m):
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return m>1
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n: return [pow(h,i,p) for i in range(n)]
for n,p in [(16,65537),(32,1048609)]:
    S=subgroup(p,n)
    g=2
    while pow(g,(p-1)//2,p)==1: g+=1
    m=(p-1)//n
    etas=[abs(sum(math.cos(2*math.pi*(pow(g,j,p)*x%p)/p) for x in S)) for j in range(m)]
    print(f"n={n} p={p} m={m}: Lambda(q) constant ||eta||_q/(sqrt(q) sqrt(n)) for growing q:")
    for q in (2,4,8,16,2*int(math.log(m))):
        lq=(sum(e**q for e in etas)/m)**(1/q)
        const=lq/(math.sqrt(q)*math.sqrt(n))
        print(f"   q={q}: ||eta||_q={lq:.3f}, /sqrt(q n)={const:.4f}")
    M=max(etas)
    print(f"   ||eta||_inf=M={M:.3f}; sqrt(2 log m)*sqrt(n)={math.sqrt(2*math.log(m))*math.sqrt(n):.3f}; M/that={M/(math.sqrt(2*math.log(m))*math.sqrt(n)):.4f}")
print()
print("=> if Lambda(q) const is BOUNDED (~const) for all q, mu_n is a Lambda(q) set with const C => Rudin")
print("   gives M=||eta||_inf <= C sqrt(n log m) = THE PRIZE. The prize = mu_n is Lambda(q) uniformly = BGK.")
