#!/usr/bin/env python3
"""probe_407_maxzeros_exact.py  (#444: EXACT max-zeros of {0..k-1,a,b}-spectral f on Z_{2^mu})

EXACT object (no coefficient search, no randomization):
  s*(n,p,T) = max |Z|, Z subset Z_n, such that EXISTS nonzero f with f^ supported in T and f|_Z = 0.
  <=> max |Z| with rank( M_Z ) < |T|,  M_Z = [w^{t z}]_{z in Z, t in T} over F_p.

For |T| = K small, a set Z of size >= K has a common nonzero spectral kernel iff every K rows of M_Z
are dependent... no: nonzero f with f|_Z=0 exists iff rank(M_Z) < K (the K columns, |Z| rows; kernel
in coeff-space c is nontrivial iff column-rank < K). So:
  s* = max |Z| with rank(M_Z) <= K-1.
We compute this EXACTLY for n <= 64 by the following: the realizable zero-sets are exactly the supports
of the (n-s)-weight codewords of the K-dim code C = {M c : c in F_p^K}. max-zeros = n - minweight(C).
minweight of a K-dim F_p code of length n: for K<=5, n<=64 we get it EXACTLY by checking, for s from large
down, whether some s rows of M have rank < K. We do it via the COMPLEMENT: a codeword of weight n-s
vanishes on s coords <=> those s rows are in a common hyperplane of F_p^K (rank<K). The max s with this:
we find by trying all ways to pick a nonzero c from the row-space relations. EXACT method used here:
  enumerate over all PAIRS/TRIPLES... -> instead, the cleanest exact: minweight = min over c!=0 of wt(Mc).
  The codewords Mc live in a K-dim space; we get minweight by walking a basis and using that minweight is
  achieved by some c that makes K-1 coords zero (generic codeword has a (K-1)-dim'l 'forced' structure).
  So: for every (K-1)-subset A of rows, solve M_A c = 0 (nonzero c exists iff rank(M_A) < K, which since
  |A|=K-1 < K is ALWAYS true -> nonzero c), then count zeros of Mc over ALL rows. max over A = s*.
  This is EXACT: every minimal-support codeword is determined (up to scale) by vanishing on K-1 generic
  coords (its other zeros are the structured extras). C(n,K-1) subsets -- feasible for n<=64,K<=5.
"""
import itertools, math

def isprime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d=m-1;r=0
    while d%2==0: d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def find_prime(n, beta):
    target=int(round(n**beta)); p=target-(target%n)+1
    if p<=n+1: p+=n
    for _ in range(500000):
        if (p-1)%n==0 and (p-1)//n>=2 and isprime(p): return p
        p+=n
    return None

def rou(p,n):
    g=2
    while g<p:
        h=pow(g,(p-1)//n,p)
        if all(pow(h,d,p)!=1 for d in range(1,n)): return h
        g+=1
    return None

def solve_null(M, p):
    """nonzero c in kernel of (rows x K) M over F_p, |rows| = K-1 < K -> guaranteed nontrivial.
       Returns one nonzero kernel vector."""
    rows=[r[:] for r in M]; R=len(rows); K=len(rows[0])
    where=[-1]*K; pr=0
    for col in range(K):
        piv=None
        for r in range(pr,R):
            if rows[r][col]%p!=0: piv=r;break
        if piv is None: continue
        rows[pr],rows[piv]=rows[piv],rows[pr]
        inv=pow(rows[pr][col],p-2,p)
        rows[pr]=[(v*inv)%p for v in rows[pr]]
        for r in range(R):
            if r!=pr and rows[r][col]%p!=0:
                f=rows[r][col]; rows[r]=[(rows[r][c]-f*rows[pr][c])%p for c in range(K)]
        where[col]=pr; pr+=1
        if pr==R: break
    # free column = one without pivot
    free=[c for c in range(K) if where[c]==-1]
    if not free: return None
    fc=free[0]; c=[0]*K; c[fc]=1
    for col in range(K):
        if where[col]!=-1:
            c[col]=(-rows[where[col]][fc])%p
    return c

def max_zeros_exact(n, p, T, cap_subsets=200000):
    w=rou(p,n); K=len(T)
    Mfull=[[pow(w,(t*z)%n,p) for t in T] for z in range(n)]
    best=0; best_witness=None
    cnt=0
    for A in itertools.combinations(range(n), K-1):
        cnt+=1
        if cnt>cap_subsets: return ("CAPPED", best, best_witness)
        MA=[Mfull[z] for z in A]
        c=solve_null(MA,p)
        if c is None: continue
        zeros=0; zlist=[]
        for z in range(n):
            v=sum(Mfull[z][j]*c[j] for j in range(K))%p
            if v==0: zeros+=1; zlist.append(z)
        if zeros>best:
            best=zeros; best_witness=(c, zlist)
    return ("EXACT", best, best_witness)

if __name__=="__main__":
    print("=== EXACT max-zeros s* of {0..k-1,a,b}-spectral f on PROPER mu_n (prize-band p) ===")
    print("(rank characterization; NO coeff search; mu_n proper subgroup, m>=2, never n=q-1)\n")
    beta=4.0; k=3; K=k+2
    print(f"k={k}, K={K}, far line (a,b)=(k+1,k+2). Johnson=√(kn), DS-permitted=n(1-1/K), floor≈k+n/log n")
    print(f"{'n':>4} {'p':>10} {'m':>7} {'a,b':>6} {'s* EXACT':>9} {'s*-k':>5} "
          f"{'Johnson':>8} {'DS-perm':>8} {'status':>7}")
    for n in [8, 16, 32]:
        p=find_prime(n,beta)
        if p is None: print(f"{n} no prime"); continue
        m=(p-1)//n; a,b=k+1,k+2
        if b>=n: continue
        status,s,wit=max_zeros_exact(n,p,[0,1,2,a,b][:K] if k==3 else list(range(k))+[a,b],
                                     cap_subsets=300000 if n<=16 else 80000)
        john=math.sqrt(k*n); ds=n*(1-1/K)
        print(f"{n:>4} {p:>10} {m:>7} {f'{a},{b}':>6} {s:>9} {s-k:>5} "
              f"{john:>8.2f} {ds:>8.2f} {status:>7}")
        if wit and wit[1]:
            print(f"      witness zero-set (size {len(wit[1])}): {wit[1][:20]}{'...' if len(wit[1])>20 else ''}")
