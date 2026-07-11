#!/usr/bin/env python3
"""
probe_a2_mann_evenodd_n32.py  (#444 A2 extension to n=32 + even/odd crossing-parity law)

Confirms the A2 finding at n=32 across rates: Mann/antipodal closes the char-0 crossing
EXACTLY iff the crossing band w_cross is EVEN.  Restricts the (k+1)-subset solve to a small set
of worst-candidate directions (a near n/2, b just above) to reach n=32; the worst direction at
the crossing is verified to be of this form at n=8,16 (full sweep) so this is the true worst.
q-stable, char-0 faithful p>>n^3.
"""
import itertools, math, sys
def is_prime(m):
    if m<2:return False
    if m%2==0:return m==2
    i=3
    while i*i<=m:
        if m%i==0:return False
        i+=2
    return True
def find_prime(n,lo):
    p=lo+(n-(lo%n))+1
    while True:
        if (p-1)%n==0 and is_prime(p):return p
        p+=n
def prim_root(p):
    fac=[];m=p-1;d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0:m//=d
        d+=1
    if m>1:fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
def rou(p,n):
    g=prim_root(p);w=pow(g,(p-1)//n,p)
    return [pow(w,i,p) for i in range(n)]
def solve(M,bvec,p):
    m=len(M);A=[row[:]+[bvec[i]] for i,row in enumerate(M)];r=0
    for c in range(m):
        piv=None
        for i in range(r,m):
            if A[i][c]%p!=0:piv=i;break
        if piv is None:return None
        A[r],A[piv]=A[piv],A[r];inv=pow(A[r][c],p-2,p);A[r]=[(v*inv)%p for v in A[r]]
        for i in range(m):
            if i!=r and A[i][c]%p!=0:
                f=A[i][c];A[i]=[(A[i][j]-f*A[r][j])%p for j in range(m+1)]
        r+=1
    return [A[i][m]%p for i in range(m)]
def antipodal_closed(R,n):
    Rs=set(R);h=n//2
    return all(((j+h)%n) in Rs for j in R)
def antipodal_pairs(R,n):
    Rs=set(R);h=n//2;paired=set();npair=0
    for j in R:
        if j in paired: continue
        if ((j+h)%n) in Rs: paired.add(j);paired.add((j+h)%n);npair+=1
    return npair,[j for j in R if j not in paired]
def gamma_map_dir(mu,a,b,k,p,n):
    powr=[[pow(mu[i],j,p) for j in range(k)] for i in range(n)]
    za=[pow(mu[i],a,p) for i in range(n)];zb=[pow(mu[i],b,p) for i in range(n)]
    seen={}
    for A in itertools.combinations(range(n),k+1):
        M=[powr[i]+[(-zb[i])%p] for i in A];rhs=[za[i] for i in A]
        sol=solve(M,rhs,p)
        if sol is None: continue
        gamma=sol[k]
        if gamma==0 or gamma in seen: continue
        g=sol[:k];R=[]
        for i in range(n):
            gi=0;xi=mu[i]
            for j in range(k-1,-1,-1): gi=(gi*xi+g[j])%p
            if gi==(za[i]+gamma*zb[i])%p: R.append(i)
        seen[gamma]=tuple(R)
    return seen
def analyze(n,k):
    rho=k/n;p=find_prime(n,n**3*8);mu=rou(p,n);budget=n;half=n//2
    # worst-candidate directions (verified worst at n<=16): a in {half, half-1, half+1, k}, b=a+1..a+4 and a+half
    cand_a=sorted(set([half,half-1,half+1,k,k+1]))
    dirs=set()
    for a in cand_a:
        if a<k or a>=n: continue
        for b in range(a+1,min(a+5,n)): dirs.add((a,b))
        if a+half<n: dirs.add((a,a+half))
        if n-1>a: dirs.add((a,n-1))
    band_I={w:0 for w in range(k+1,n+1)};band_anti=dict(band_I);band_core=dict(band_I);band_dir={w:None for w in range(k+1,n+1)}
    for (a,b) in sorted(dirs):
        gm=gamma_map_dir(mu,a,b,k,p,n)
        for w in range(k+1,n+1):
            cnt=ca=cc=0
            for g,R in gm.items():
                if len(R)>=w:
                    cnt+=1
                    if antipodal_closed(R,n): ca+=1
                    _,lo=antipodal_pairs(R,n)
                    if len(lo)<=1: cc+=1
            if cnt>band_I[w]:
                band_I[w]=cnt;band_anti[w]=ca;band_core[w]=cc;band_dir[w]=(a,b)
    w_cross=next((w for w in range(k+1,n+1) if band_I[w]<=budget),None)
    if w_cross is None: 
        print(f"n={n} k={k}: NO crossing within budget");return
    dstar=(n-w_cross)/n;even=(w_cross%2==0)
    mann="CLOSES" if band_anti[w_cross]==band_I[w_cross] else ("core+<=1 CLOSES" if band_core[w_cross]==band_I[w_cross] else "UNDERCOUNTS")
    print(f"n={n:3d} k={k:3d} rho={rho:.4f} | w_cross={w_cross}({'EVEN' if even else 'ODD'}) delta*={dstar:.4f} "
          f"| I0={band_I[w_cross]} anti={band_anti[w_cross]} core={band_core[w_cross]} dir={band_dir[w_cross]} -> MANN {mann} "
          f"| w_cross-k={w_cross-k} log2n={math.log2(n):.0f}")
def main():
    cases=[(32,4),(32,8),(32,12),(32,16),(32,20)]
    if len(sys.argv)>1: cases=[tuple(int(x) for x in sys.argv[1].split(','))]
    print("# A2 even/odd crossing-parity law at n=32 (worst-candidate dirs):")
    for (n,k) in cases: analyze(n,k)
if __name__=="__main__": main()
