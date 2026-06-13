# Understand the +6n: decompose E(μ_{2n}) by the A/B parity pattern (A=μ_n, B=ζμ_n).
# Also test T7: does E_3 (sixth moment) satisfy a clean doubling recursion too?
import sympy
from collections import Counter
def musub(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p)
    return [pow(h,j,p) for j in range(n)]
def E2(G,p):
    r=Counter((a+b)%p for a in G for b in G); return sum(v*v for v in r.values())
def E3(G,p):  # 6th moment: #{a+b+c=d+e+f}
    r=Counter((a+b+c)%p for a in G for b in G for c in G); return sum(v*v for v in r.values())
for m in range(3,7):
    n=2**m; n2=2*n
    target=n2**3
    p=None
    for cand in range(target-target%n2+1,target*2,n2):
        if sympy.isprime(cand): p=cand;break
    Gn=musub(n,p); G2n=musub(n2,p)
    # decompose E2(G2n) by parity: how many of the 4 elts are in B=odd powers
    g=sympy.primitive_root(p); h2=pow(g,(p-1)//n2,p)
    B=set(pow(h2,2*j+1,p) for j in range(n)); A=set(pow(h2,2*j,p) for j in range(n))
    pat=Counter()
    for a in G2n:
        for b in G2n:
            s=(a+b)%p
            for c in G2n:
                d=(s-c)%p
                if d in A or d in B:
                    key=tuple(sorted([x in B for x in (a,b,c,d)]))
                    pat[sum(key)]+=1
    e2n,en=E2(G2n,p),E2(Gn,p)
    print(f"n={n}: E2(n)={en} E2(2n)={e2n} =4E+6n? {e2n==4*en+6*n}; parity counts(by #inB)={dict(pat)}")
    if m<=5:
        e3n,e3_2n=E3(Gn,p),E3(G2n,p)
        print(f"      E3(n)={e3n} E3(2n)={e3_2n} ratio={e3_2n/e3n:.3f} (E3 doubling?)")
