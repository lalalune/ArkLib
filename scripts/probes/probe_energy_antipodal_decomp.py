# Cross-check lalalune's "energy quadruples are antipodally balanced" (85a4c4920) + the
# exact decomposition of E(mu_n)=3n(n-1). Use a clean large prime (p>>n^2.5) as char-0
# proxy (verified E=3n(n-1) there). Classify each ordered (a,b,c,d), a+b=c+d:
#   DIAGONAL: {a,b}={c,d} as multisets  -> count should be 2n^2 - n
#   NON-DIAG: the rest -> count n(n-2); claim: each is ANTIPODALLY balanced, i.e.
#             {a,b} and {c,d} are both antipodal pairs (b=-a, d=-c) with equal sum (=0).
from collections import Counter
def is_prime(x):
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return x>1
def subgroup(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p); s,x=set(),1
        for _ in range(n): s.add(x); x=x*h%p
        if len(s)==n: return sorted(s)
    return None
def clean_prime(n):
    base=int(n**3.5); p=base+((1-base)%n)
    while not(is_prime(p) and (p-1)%n==0): p+=1
    return p
for n in (8,16,32):
    p=clean_prime(n); H=subgroup(p,n); Hs=set(H)
    neg={a:(p-a)%p for a in H}            # -a (in mu_n since n even, -1 in mu_n)
    E=diag=nondiag=anti=0
    for a in H:
        for b in H:
            s=(a+b)%p
            for c in H:
                d=(s-c)%p
                if d in Hs:
                    E+=1
                    if {a,b}=={c,d}: diag+=1
                    else:
                        nondiag+=1
                        # antipodal: both pairs sum to the same s AND are antipodal pairs
                        if b==neg[a] and d==neg[c]: anti+=1
    tgt=3*n*(n-1)
    print(f"n={n} p={p}: E={E} (target {tgt} {'✓' if E==tgt else 'MISMATCH'}) | "
          f"diagonal={diag} (2n^2-n={2*n*n-n} {'✓' if diag==2*n*n-n else '✗'}) | "
          f"non-diag={nondiag} (n(n-2)={n*(n-2)} {'✓' if nondiag==n*(n-2) else '✗'}) | "
          f"non-diag antipodal={anti}/{nondiag} {'ALL ✓' if anti==nondiag else 'NOT ALL'}")
