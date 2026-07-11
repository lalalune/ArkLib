"""
EXHAUSTIVE p-sensitive invariant exploration (#444).
Question: is there ANY p-sensitive invariant X(p) controlling the binding m* / distinct-gamma count D*
that is NOT the magnitude M=max|eta_b| (the wall)? For n=2^mu the periods eta_b are REAL (since -1 in mu_n),
so the "archimedean phase" reduces to a SIGN. Enumerate p-sensitive invariants, compute across several
primes at fixed n, and test: (a) does the binding D* VARY with p? (b) if it does, what p-sensitive invariant
tracks it? (c) does that invariant reduce to M?

p-sensitive invariants tested (for fixed n, varying p):
  M       = max_{b!=0} |eta_b|                         (THE magnitude / wall)
  signvec = sign pattern of (eta_b)                    (the real "phase" / root-number sign)
  v2gap   = #{b : v_ell(eta_b - eta_round) anomalous}  (2-adic / valuation datum, moment-blind)
  badidx  = does p divide a small cyclotomic norm (Spur_2/3 spurious vanishing)
  valdist = sorted |eta_b| value distribution (the spectral measure)
  Dstar   = distinct-gamma count at the over-det binding radius  (the m* object)
"""
import itertools, math, cmath
def isprime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43):
        if m%q==0: return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in(1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def primes1modn(n,lo,cnt):
    out=[];p=lo+(n-lo%n)+1
    while len(out)<cnt:
        if p%n==1 and isprime(p):out.append(p)
        p+=n
    return out
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n:
            return [pow(h,i,p) for i in range(n)]
def periods(p,n,S):
    """eta_b = sum_{x in S} e_p(b x), REAL for 2-power n. Return list over b=0..p-1? too big.
    Instead over a transversal: eta depends on b through the coset b*mu_n. Compute over all b in 1..p-1
    is p~10^6 too big; compute over a sample/the distinct values via coset reps."""
    # eta_b is constant on cosets b*mu_n; there are (p-1)/n distinct nonzero values. Enumerate coset reps.
    seen=set(); reps=[]
    for b in range(1,p):
        cb=min((b*s)%p for s in S)  # canonical coset rep
        if cb in seen: continue
        seen.add(cb); reps.append(b)
        if len(reps)>= (p-1)//n: break
    # compute eta_b for each rep (real part suffices; it's real)
    etas=[]
    for b in reps:
        val=sum(math.cos(2*math.pi*(b*x % p)/p) for x in S)
        etas.append(val)
    return etas
def forced_gamma_count(p,n,S,k,a,b):
    ra,rb=a-k,b-k
    if ra<0 or rb<0: return None
    def hr(R,r):
        dp=[0]*(r+1);dp[0]=1
        for x in R:
            for j in range(min(r,len(dp)-1),0,-1):
                dp[j]=(dp[j]+x*dp[j-1])%p
        return dp[r]
    vals=set()
    for R in itertools.combinations(S,k+1):
        hb=hr(R,rb)
        if hb==0:continue
        vals.add((-hr(R,ra)*pow(hb,p-2,p))%p)
    return len(vals)

n=16; k=n//4
primes=primes1modn(n,50*n**4,6)
print(f"n={n} k={k}; primes p=1 mod {n}, p>n^4:")
print(f"{'p':>9} {'M=max|eta|':>11} {'#signs(-)':>9} {'valdist[top3]':>22} {'Dstar(bind r=5)':>15} {'Dstar(r=3)':>11}")
rows=[]
for p in primes:
    S=subgroup(p,n)
    etas=periods(p,n,S)
    aet=[abs(e) for e in etas]
    M=max(aet)
    nneg=sum(1 for e in etas if e<-1e-9)
    top3=sorted(aet,reverse=True)[:3]
    # binding distinct-gamma at deep fold r=5 (where it crossed budget) and r=3
    D5=forced_gamma_count(p,n,S,k,k+5,k)
    D3=forced_gamma_count(p,n,S,k,k+3,k)
    rows.append((p,M,nneg,top3,D5,D3))
    print(f"{p:>9} {M:>11.4f} {nneg:>9} {str([round(x,2) for x in top3]):>22} {str(D5):>15} {str(D3):>11}")
print()
print("ANALYSIS:")
Ms=[r[1] for r in rows]; D5s=[r[4] for r in rows]; D3s=[r[5] for r in rows]
print(f"  M (magnitude) VARIES with p: {min(Ms):.3f}..{max(Ms):.3f}  (range {max(Ms)-min(Ms):.3f})  => p-SENSITIVE")
print(f"  Dstar(r=5) across p: {D5s}  => {'p-INDEPENDENT' if len(set(D5s))==1 else 'p-DEPENDENT'}")
print(f"  Dstar(r=3) across p: {D3s}  => {'p-INDEPENDENT' if len(set(D3s))==1 else 'p-DEPENDENT'}")
print(f"  sign-count(neg) across p: {[r[2] for r in rows]}  => {'p-INDEP' if len(set(r[2] for r in rows))==1 else 'p-DEP'}")
