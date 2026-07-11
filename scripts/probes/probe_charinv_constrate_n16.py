import itertools, math
def isp(x):
    if x<2:return False
    d=2
    while d*d<=x:
        if x%d==0:return False
        d+=1
    return True
def proot(p,n):
    for c in range(2,p):
        h=pow(c,(p-1)//n,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    return None
def maxagree(p,n,k,a,b,subsets,invcache):
    z=proot(p,n)
    pts=[pow(z,i,p) for i in range(n)]
    out={}
    for g in range(p):
        w=[(pow(z,(i*b)%n,p)+g*pow(z,(i*a)%n,p))%p for i in range(n)]
        best=0
        for T in subsets:
            # interpolate deg<k through (pts[i],w[i]) i in T, eval at all pts, count matches
            cnt=0
            xs=[pts[i] for i in T]; ys=[w[i] for i in T]
            for ii in range(n):
                X=pts[ii]; tot=0
                for i in range(k):
                    num=ys[i]; den=1
                    for j in range(k):
                        if j!=i:
                            num=(num*(X-xs[j]))%p; den=(den*(xs[i]-xs[j]))%p
                    tot=(tot+num*pow(den,p-2,p))%p
                if tot==w[ii]: cnt+=1
            if cnt>best:best=cnt
            if best==n:break
        out[g]=best
    return out
def run(n,k,primes,pencils):
    print(f"=== n={n} k={k} rho={k/n} far pencils a,b>=k, !=n/2 ===")
    subsets=list(itertools.combinations(range(n),k))
    for (a,b) in pencils:
        g=math.gcd(b-a,n);S=n//g
        print(f" pencil({a},{b}) gcd(b-a,n)={g} S={S}:")
        prof={}
        for p in primes:
            ma=maxagree(p,n,k,a,b,subsets,None)
            band={w:sum(1 for x in ma if ma[x]>=w) for w in range(k+1,n+1)}
            prof[p]=band
            # normalize by p to see if I/p (fraction) or absolute char-invariant
            print(f"   p={p}: I per band w={list(range(k+1,n+1))}: {[band[w] for w in range(k+1,n+1)]}")
        # char-invariance check: compare bands across primes (absolute)
        bands=range(k+1,n+1)
        inv_abs=all(len({prof[p][w] for p in primes})==1 for w in bands)
        print(f"   --> ABSOLUTE char-invariant across primes? {inv_abs}")
run(8,2,[73,89,97,113],[(2,3),(2,5),(3,5),(5,6),(5,7),(6,7)])
print()
run(16,4,[97,193,257,337],[(5,6),(5,7),(6,7),(9,11)])
