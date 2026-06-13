def is_prime(p):
    if p<2: return False
    for d in range(2,int(p**0.5)+1):
        if p%d==0: return False
    return True
def prime_factors(n):
    fs=set(); d=2
    while d*d<=n:
        while n%d==0: fs.add(d); n//=d
        d+=1
    if n>1: fs.add(n)
    return fs
def subgroup(p,n):
    for g in range(2,p):
        if pow(g,n,p)==1 and all(pow(g,n//q,p)!=1 for q in prime_factors(n)):
            return [pow(g,i,p) for i in range(n)]
    return None
def excess(p,n):
    G=subgroup(p,n)
    if G is None or len(set(G))!=n: return None
    from collections import Counter
    r=Counter()
    for a in G:
        for b in G: r[(a+b)%p]+=1
    return sum(v*v for v in r.values())-(3*n*n-3*n)
# REFUTATION: is excess * p / n^4 bounded? And excess/n^2 -> 0 as n^2/p -> 0?
maxC=0; maxCcase=None
rows=[]
for p in range(11,5000):
    if not is_prime(p): continue
    for n in range(6, int((p-1)**0.5)+1, 2):
        if (p-1)%n: continue
        e=excess(p,n)
        if e is None: continue
        C = e*p/(n**4)   # excess ~ C n^4/p
        if C>maxC: maxC=C; maxCcase=(p,n,e,round(C,2))
        rows.append((n*n/p, e/(n*n), C, p, n))
print(f"REFUTATION TEST: max(excess*p/n^4) = {maxC:.3f} at (p,n,excess,C)={maxCcase}")
print(f"  -> conjecture excess<=C*n^4/p {'SURVIVES (bounded)' if maxC<10 else 'REFUTED (grows)'}")
print(f"\nexcess/n^2 vs n^2/p (binned): should ->0 as n^2/p->0")
import collections
bins=collections.defaultdict(list)
for ratio_np, exc_n2, C, p, n in rows:
    b=round(ratio_np,1)
    bins[b].append(exc_n2)
for b in sorted(bins):
    v=bins[b]
    print(f"  n^2/p ~ {b:.1f}:  mean excess/n^2 = {sum(v)/len(v):.3f}  max = {max(v):.3f}  (count {len(v)})")
