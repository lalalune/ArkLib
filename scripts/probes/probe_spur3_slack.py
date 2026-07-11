from collections import defaultdict
import sympy, math
def subgroup_residues(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p)
    return [pow(h,i,p) for i in range(n)]
def e3_count(sub,p):
    T3=defaultdict(int)
    for a in sub:
        for b in sub:
            ab=(a+b)%p
            for c in sub: T3[(ab+c)%p]+=1
    return sum(cnt*T3[(-s)%p] for s,cnt in T3.items())

# Spur_3(p) = E3_charp - char0_value.  char0 = 15n^3-45n^2+40n.
# slack bound (P2-Slack at r=3): Spur_3 <= ceiling - Z = 15n^3 - (15n^3-45n^2+40n) = 45n^2-40n.
# QUESTION: does Spur_3(p) EVER exceed 45n^2-40n?  (would REFUTE slack route at r=3)
# Also: at prize scale p~n^4, is Spur_3 = 0?
for a in [2,3,4]:
    n=2**a
    char0=15*n**3-45*n**2+40*n
    slack=45*n**2-40*n   # = ceiling - Z
    ceiling=15*n**3
    maxspur=0; maxspur_p=None; violate=[]
    p=n+1; tested=0
    bound = max(3*n**4, 200000) if n<=16 else 2*n**4
    # cap work for n=16: only go to ~n^4
    if n==16: bound = 2*n**4   # ~131072
    while p<=bound:
        if sympy.isprime(p) and p>2:
            sub=subgroup_residues(n,p)
            if len(set(sub))==n and p-1!=n:
                e=e3_count(sub,p)
                spur=e-char0
                tested+=1
                if spur>maxspur: maxspur=spur; maxspur_p=p
                if spur>slack: violate.append((p,spur))
        p+=n
    # also confirm at prize scale p ~ n^4
    print(f"n={n}: char0={char0} ceiling={ceiling} slack(=ceiling-Z)={slack}")
    print(f"   tested {tested} primes up to {bound}. max Spur_3 = {maxspur} at p={maxspur_p} (slack allows {slack})")
    print(f"   Spur_3 > slack EVER? {'YES -> REFUTES' if violate else 'NO -> slack route holds for all tested p'}; {('first violations: '+str(violate[:5])) if violate else ''}")
    print(f"   max_Spur/slack = {maxspur/slack:.3f}")
