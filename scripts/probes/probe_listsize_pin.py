#!/usr/bin/env python3
"""
List-decoding side of the prize, tied to FRI soundness. delta* is a list-decoding threshold; the
FRI above-Johnson bad-count is governed by the list size. We compute EXACTLY, for the dyadic RS
domain mu_N, the maximum list size at relative radius delta:
   L(N, e) = max over words f of #{RS codewords c : d(f,c) <= e}.
Coset-invariance: d(f,c)=d(f+c0, c+c0), so the multiset of distances {d(f,c)} depends only on the
coset f+RS, i.e. on syndrome s=H f. And #{c: d(f,c)<=e} = #{weight<=e vectors v with H v = s}.
So L(N,e) = max over syndromes s of #{weight<=e vectors with syndrome s} -- exact, from enumeration.

We print L(N,e) for e around the Johnson radius (1-sqrt(rho))*N and the unique-decoding radius, and
compare to the measured FRI above-Johnson bad-count. Johnson list bound: L=O(1) for e<=Johnson.
"""
import itertools,math,functools
print=functools.partial(print,flush=True)
def run(q,N,k):
    inv=[0]*q
    for a in range(1,q): inv[a]=pow(a,q-2,q)
    omega=next((g for g in range(2,q) if pow(g,N,q)==1 and pow(g,N//2,q)!=1),None)
    if omega is None or pow(omega,N//2,q)!=q-1: print(f"skip q={q} N={N}");return
    D=[pow(omega,i,q) for i in range(N)]
    def pc(dom,kk):
        n=len(dom);G=[[pow(x,j,q)for x in dom]for j in range(kk)];M=[r[:]for r in G]
        rows=kk;cols=n;piv=[];r=0
        for c in range(cols):
            pr=next((i for i in range(r,rows) if M[i][c]%q),None)
            if pr is None:continue
            M[r],M[pr]=M[pr],M[r];ip=inv[M[r][c]%q];M[r]=[(v*ip)%q for v in M[r]]
            for i in range(rows):
                if i!=r and M[i][c]%q:
                    f=M[i][c]%q;M[i]=[(M[i][j]-f*M[r][j])%q for j in range(cols)]
            piv.append(c);r+=1
            if r==rows:break
        free=[c for c in range(cols)if c not in piv];H=[]
        for fc in free:
            h=[0]*cols;h[fc]=1
            for ri,p in enumerate(piv):h[p]=(-M[ri][fc])%q
            H.append(h)
        return H
    HN=pc(D,k);rN=len(HN)
    def syn(f):return tuple(sum(HN[i][j]*f[j] for j in range(N))%q for i in range(rN))
    # count, per syndrome, the number of weight=w vectors (then cumulative for <=e)
    from collections import defaultdict
    cnt=defaultdict(lambda:defaultdict(int))   # syndrome -> {weight: count}
    cov=N-k
    for w in range(0,cov+1):
        for supp in itertools.combinations(range(N),w):
            for vals in itertools.product(range(1,q),repeat=w):
                f=[0]*N
                for idx,v in zip(supp,vals):f[idx]=v
                cnt[syn(f)][w]+=1
    rho=k/N;johnson=(1-math.sqrt(rho));jpos=johnson*N;ud=(N-k)//2  # unique-dec radius (rel (d-1)/2 ~ (N-k)/2)
    print(f"\n===== q={q} N={N} k={k} rho={rho:.3f} | Johnson={johnson:.3f}({jpos:.2f}pos) unique-dec~{ud}pos cov={cov} =====")
    # max list size at radius e = max over syndromes of sum_{w<=e} cnt[s][w]
    for e in range(0,cov+1):
        mx=0;arg=None
        for s,wc in cnt.items():
            L=sum(c for w,c in wc.items() if w<=e)
            if L>mx:mx=L;arg=s
        tag=""
        if e<jpos: tag=" (<=Johnson: L=O(1) by Johnson bound)"
        elif e<=jpos+1: tag=" <-- JUST ABOVE Johnson"
        print(f"   radius e={e} ({e/N:.3f}): max list size L={mx}{tag}")
    print(f"   (compare: measured FRI above-Johnson worst bad-count at N=8,rho=1/2 was 4)")
for (q,N,k) in [(17,8,4),(41,8,4),(97,8,4),(17,8,6),(17,8,2)]:
    run(q,N,k)
