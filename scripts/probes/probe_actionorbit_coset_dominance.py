#!/usr/bin/env python3
"""
RIGOROUS exhaustive test of Conjecture 7.1 (sparse/3-position dominance), ePrint 2026/861
Action-Orbit FRI -- PDF-independent reconstruction that FIXES the weight-vs-distance confound.

Key fact: FRI fold and RS are F-linear, and the honest fold of a codeword is a codeword. So the
soundness eps(f) := #{lambda : Fold[f,lambda] is close to RS'} depends ONLY on the coset f+RS_N,
i.e. only on the syndrome s = H_N f. We therefore enumerate the ENTIRE adversary space exactly
(all q^{N-k} syndromes), and for each coset compute:
  - w(s) = coset-leader weight = exact distance d(f, RS_N)   (confound-free)
  - eps0(s)  = #{lambda : Fold within 0 positions of RS'}  (folded word is a codeword)
  - eps1(s)  = #{lambda : Fold within 1 position of RS'}
Then bucket max eps by leader weight w. Conj 7.1 predicts worst-case eps is achieved at the
minimal ABOVE-JOHNSON leader weight (the '3-position' class) and does NOT grow for deeper cosets.

Johnson radius for RS[N,k] = 1 - sqrt(k/N); above-Johnson leader weights w > (1-sqrt(rho))*N.
"""
import itertools, math, functools
print = functools.partial(print, flush=True)

def gf(q):
    inv=[0]*q
    for a in range(1,q): inv[a]=pow(a,q-2,q)
    return inv

def vander_paritycheck(dom, kk, q, inv):
    # H = basis of null space of G (kk x n Vandermonde on dom); codewords = rowspace(G)
    n=len(dom); G=[[pow(x,j,q) for x in dom] for j in range(kk)]
    M=[r[:] for r in G]; rows=kk; cols=n; piv=[]; r=0
    for c in range(cols):
        pr=next((i for i in range(r,rows) if M[i][c]%q),None)
        if pr is None: continue
        M[r],M[pr]=M[pr],M[r]; ip=inv[M[r][c]%q]; M[r]=[(v*ip)%q for v in M[r]]
        for i in range(rows):
            if i!=r and M[i][c]%q:
                f=M[i][c]%q; M[i]=[(M[i][j]-f*M[r][j])%q for j in range(cols)]
        piv.append(c); r+=1
        if r==rows: break
    free=[c for c in range(cols) if c not in piv]; H=[]
    for fc in free:
        h=[0]*cols; h[fc]=1
        for ri,pc in enumerate(piv): h[pc]=(-M[ri][fc])%q
        H.append(h)
    return H  # (n-kk) x n

def run(q,N,k):
    inv=gf(q)
    omega=next((g for g in range(2,q) if pow(g,N,q)==1 and pow(g,N//2,q)!=1),None)
    if omega is None or pow(omega,N//2,q)!=q-1: print(f"no root q={q} N={N}"); return
    D=[pow(omega,i,q) for i in range(N)]
    Dp=sorted(set(pow(x,2,q) for x in D)); Np=len(Dp); kp=k//2
    HN=vander_paritycheck(D,k,q,inv); rN=len(HN)            # (N-k) x N
    Hp=vander_paritycheck(Dp,kp,q,inv); rp=len(Hp)          # (Np-kp) x Np
    posDp={v:i for i,v in enumerate(Dp)}
    seen=set(); foldinfo=[]
    for x in D:
        y=pow(x,2,q); nx=(q-x)%q
        if y not in seen: seen.add(y); foldinfo.append((posDp[y],x,nx))
    inv2=inv[2]
    HpcolsT=[tuple(Hp[i][j] for i in range(rp)) for j in range(Np)]
    targets=[tuple([0]*rp)]+[HpcolsT[j] for j in range(Np)]
    def synN(f): return tuple(sum(HN[i][j]*f[j] for j in range(N))%q for i in range(rN))
    def eps(f):  # (eps0,eps1) coset-invariant
        fd={D[i]:f[i] for i in range(N)}; g0=[0]*Np; g1=[0]*Np
        for (yi,x,nx) in foldinfo:
            g0[yi]=((fd[x]+fd[nx])*inv2)%q; g1[yi]=((fd[x]-fd[nx])*inv[(2*x)%q])%q
        A=tuple(sum(Hp[i][j]*g0[j] for j in range(Np))%q for i in range(rp))
        B=tuple(sum(Hp[i][j]*g1[j] for j in range(Np))%q for i in range(rp))
        def sol(t):
            lam=None
            for i in range(rp):
                bi=B[i]%q; rhs=(t[i]-A[i])%q
                if bi==0:
                    if rhs: return set()
                else:
                    li=(rhs*inv[bi])%q
                    if lam is None: lam=li
                    elif lam!=li: return set()
            return None if lam is None else {lam}
        s0=sol(targets[0]); e0=q if s0 is None else len(s0)
        ls=set()
        for t in targets:
            st=sol(t)
            if st is None: ls=set(range(q)); break
            ls|=st
        return e0,len(ls)
    # enumerate all weight<=cov vectors -> syndrome -> (minweight, leader rep)
    cov=N-k  # covering radius of MDS [N,k]
    leader={}  # syndrome -> (weight, repvector)
    for w in range(0,cov+1):
        for supp in itertools.combinations(range(N),w):
            for vals in itertools.product(range(1,q),repeat=w):
                f=[0]*N
                for idx,v in zip(supp,vals): f[idx]=v
                s=synN(f)
                if s not in leader or leader[s][0]>w:
                    leader[s]=(w,f)
        if len(leader)==q**rN: break
    rho=k/N; johnson=1-math.sqrt(rho); jpos=johnson*N
    print(f"\n===== q={q} N={N} k={k} rho={rho:.3f} | Np={Np} kp={kp} | Johnson={johnson:.3f} ({jpos:.2f} pos) | #cosets={q**rN} enumerated={len(leader)} =====")
    by0={}; by1={}; supp_at_max={}
    for s,(w,f) in leader.items():
        e0,e1=eps(f)
        by0[w]=max(by0.get(w,-1),e0); by1[w]=max(by1.get(w,-1),e1)
        # track support orbit structure of the worst e1
        if e1>=by1[w]:
            supp=tuple(i for i in range(N) if f[i]); supp_at_max[w]=(e1,supp)
    print(f"   above-Johnson leader weights: w > {jpos:.2f}  => w in {[w for w in sorted(by0) if w>jpos]}")
    for w in sorted(by0):
        tag=" (ABOVE-Johnson)" if w>jpos else ""
        print(f"   w={w}: max eps0={by0[w]:3d}/{q}  max eps1={by1[w]:3d}/{q}{tag}  worst-e1 supp={supp_at_max.get(w)}")
    # the prize-relevant statement: among ABOVE-Johnson cosets, does worst eps stay O(1) (=small const)?
    aj=[w for w in sorted(by0) if w>jpos]
    if aj:
        m0=max(by0[w] for w in aj); m1=max(by1[w] for w in aj)
        first0=min((w for w in aj if by0[w]==m0),default=None)
        print(f"   ABOVE-JOHNSON worst: eps0={m0}/{q} (first at w={first0}), eps1={m1}/{q}")
        print(f"   3-position dominance (worst above-Johnson eps at the MINIMAL above-J weight {min(aj)}?): "
              f"{'YES' if first0==min(aj) else f'NO (needs w={first0})'}")

for (q,N,k) in [(17,8,6),(17,8,5),(41,8,6),(41,8,5),(97,8,6),(97,8,5),(17,16,14),(17,16,12)]:
    run(q,N,k)
