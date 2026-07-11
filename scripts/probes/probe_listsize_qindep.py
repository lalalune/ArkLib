#!/usr/bin/env python3
"""q-independence of the just-above-Johnson max list size for dyadic RS[8,4] (rho=1/2).
L(e) = max over syndromes of #{weight<=e vectors with that syndrome}. Enumerate weight<=3 only
(enough for the e<=3 transition: Johnson=2.34, so e=3 is the just-above-Johnson radius)."""
import itertools,math,functools
from collections import defaultdict
print=functools.partial(print,flush=True)
def run(q,N=8,k=4):
    inv=[0]*q
    for a in range(1,q): inv[a]=pow(a,q-2,q)
    omega=next((g for g in range(2,q) if pow(g,N,q)==1 and pow(g,N//2,q)!=1),None)
    if omega is None or pow(omega,N//2,q)!=q-1: return None
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
    cnt=defaultdict(lambda:[0,0,0,0])  # syndrome -> count by weight 0..3
    for w in range(0,4):
        for supp in itertools.combinations(range(N),w):
            for vals in itertools.product(range(1,q),repeat=w):
                f=[0]*N
                for idx,v in zip(supp,vals):f[idx]=v
                cnt[syn(f)][w]+=1
    L={e:max(sum(c[:e+1]) for c in cnt.values()) for e in range(4)}
    return L
print("max list size L(e) for dyadic RS[8,4], rho=1/2 (Johnson=2.34 pos), weight<=3 enum:")
for q in [17,41,73,97,193,257,401]:
    L=run(q)
    if L: print(f"   q={q:4d}: L(0)={L[0]} L(1)={L[1]} L(2)={L[2]} [<=Johnson] | L(3)={L[3]} [ABOVE Johnson]")
