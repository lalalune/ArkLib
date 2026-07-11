# Independent cross-check of the swarm's "INERT energy E(mu_n)=3n(n-1) UNCONDITIONAL"
# claim (n | p+1, mu_n lives in F_{p^2}). Different regime + code path from the split case.
# F_{p^2} = F_p[t]/(t^2 - nr), nr a non-residue. Element (a,b)=a+bt.
from collections import Counter
def is_prime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
def nonresidue(p):
    for a in range(2,p):
        if pow(a,(p-1)//2,p)==p-1: return a
    raise RuntimeError
def f2_mul(A,B,p,nr):
    a,b=A; c,d=B
    return ((a*c+b*d*nr)%p, (a*d+b*c)%p)
def f2_add(A,B,p):
    return ((A[0]+B[0])%p,(A[1]+B[1])%p)
def f2_pow(A,e,p,nr):
    R=(1,0)
    while e: 
        if e&1: R=f2_mul(R,A,p,nr)
        A=f2_mul(A,A,p,nr); e>>=1
    return R
def mu_n(p,n):
    nr=nonresidue(p); order=p*p-1
    assert order%n==0
    # find a generator of F_{p^2}^* then raise to order/n; brute search small base
    import itertools
    for a in range(0,p):
        for b in range(1,p):
            g=(a,b)
            # check order is p^2-1 by testing it's not a proper-divisor power... cheap: check g^(order/q)!=1 for prime q|order
            ok=True
            for q in set(f for f in range(2,order+1) if order%f==0 and is_prime(f)):
                if f2_pow(g,order//q,p,nr)==(1,0): ok=False; break
            if ok:
                h=f2_pow(g,order//n,p,nr)
                S=set(); x=(1,0)
                for _ in range(n): S.add(x); x=f2_mul(x,h,p,nr)
                if len(S)==n: return sorted(S),nr
    raise RuntimeError("no generator")
def energy(S,p):
    c=Counter()
    for A in S:
        for B in S: c[f2_add(A,B,p)]+=1
    return sum(v*v for v in c.values())
print("INERT energy E(mu_n) over F_{p^2}, n|p+1 — claim: =3n(n-1) UNCONDITIONAL (no threshold)\n")
for n in (8,16):
    tgt=3*n*(n-1); print(f"n={n}: target 3n(n-1)={tgt}")
    found=0; p=3
    while found<4:
        if is_prime(p) and (p+1)%n==0 and p>=n//2:
            try:
                S,nr=mu_n(p,n); E=energy(S,p)
                print(f"   p={p:>4} (inert, p+1={p+1}) E={E}  {'= 3n(n-1) ✓' if E==tgt else f'≠ {tgt} (surplus {E-tgt})'}")
                found+=1
            except Exception as ex:
                pass
        p+=1
