# wfH-L4 (fast, exact-where-it-counts): Is the worst-b excess of M(n) LINEAR (U^2 = the eta_b
# = energy = the wall) or a genuine NON-LINEAR (quadratic/U^3) obstruction the GTZ inverse
# theorem would detect as NEW?
#
# Search with numpy complex128 (fast) for argmax; the load-bearing COLLAPSE claim is then
# checked with EXACT INTEGER subgroup arithmetic (no float): squaring folds mu_n onto mu_{n/2}.
import numpy as np, math
def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True
def primroot(p):
    fac=set(); m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a
def subgroup(p,n):
    g=pow(primroot(p),(p-1)//n,p); return [pow(g,i,p) for i in range(n)]

def run(n, beta):
    target = n**beta
    p = ((target)//n)*n + 1
    while p < target or not isprime(p): p += n
    roots = np.array(subgroup(p,n), dtype=np.int64)
    w = np.exp(2j*math.pi*np.arange(p)/p)  # zeta^r table
    # LINEAR: max_b |sum_x zeta^{b x}|
    bestM=-1.0; argb=None
    for b in range(1,p):
        ph=(b*roots)%p
        s=w[ph].sum()
        v=abs(s)
        if v>bestM: bestM=v; argb=b
    # QUADRATIC: max_{c!=0,b} |sum_x zeta^{c x^2 + b x}|
    sq=(roots*roots)%p
    bestQ=-1.0; argbc=None
    for c in range(1,p):
        cqs=(c*sq)%p
        for b in range(0,p):
            ph=(cqs+b*roots)%p
            s=w[ph].sum()
            v=abs(s)
            if v>bestQ: bestQ=v; argbc=(c,b)
    sn=math.sqrt(n)
    # EXACT structural check: image of squaring on mu_n
    sqset=sorted(set(int(x) for x in sq))
    half=subgroup(p, n//2) if n>=2 else [1]
    halfset=sorted(set(int(x) for x in half))
    fold_ok = (sqset==halfset)  # mu_n^2 == mu_{n/2} exactly (integer set equality)
    return p,bestM,bestQ,bestM/sn,bestQ/sn,argb,argbc,fold_ok,len(sqset)

if __name__=="__main__":
    # quadratic loop O(p^2 * n); keep p modest. beta lowered for larger n.
    cases=[(4,4),(8,4),(8,3),(16,2),(16,3),(32,2)]
    print("# x->x^2 folds mu_n 2-to-1 onto mu_{n/2}: a 'quadratic' phase on mu_n is a LINEAR phase on the folded subgroup.")
    for n,beta in cases:
        p,M,Q,Mr,Qr,argb,argbc,fold_ok,imgsz=run(n,beta)
        print(f"n={n:3d} b={beta} p={p:7d} | M={M:.4f}({Mr:.3f}vn,b={argb}) | "
              f"Q={Q:.4f}({Qr:.3f}vn,(c,b)={argbc}) | Q/M={Q/M:.4f} | "
              f"mu_n^2==mu_(n/2)?{fold_ok} |img|={imgsz}", flush=True)
