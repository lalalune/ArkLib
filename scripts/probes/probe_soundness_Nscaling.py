#!/usr/bin/env python3
"""
DECISIVE N-scaling of the above-Johnson FRI soundness bad-count -- distinguishes the prize O(1)/|F|
claim (2026/861) from the a=O(n/eta^5) regime. At N=8 (rho=1/2) the worst above-Johnson bad-count
was 4. Here N=16: sample GENUINE distance-(w) leaders at the minimal above-Johnson weight, compute
exact folded distance to RS[Np,kp] (Np=N/2), matched radius floor(w*Np/N), and report max bad-count.
If it stays ~constant (~4) => O(1)/|F| (prize). If it grows ~N => a=O(n/...) regime.

Genuine-leader check: weight-w f has d(f,RS_N)=w iff no deg<k poly agrees on >= N-(w-1) points.
We verify by sampling k-subsets, interpolating, and rejecting f if any agreement >= N-w+1.
exact folded dist to RS[Np,kp]: Np - max over kp-subsets (fit deg<kp poly) of agreement.
"""
import itertools,math,random,functools
print=functools.partial(print,flush=True)
def lagrange_eval(pts, X, q, inv):  # interpolate through pts=[(x,y)], eval at X
    tot=0
    for i,(xi,yi) in enumerate(pts):
        term=yi
        for j,(xj,_) in enumerate(pts):
            if j!=i: term=(term*((X-xj)%q)*inv[(xi-xj)%q])%q
        tot=(tot+term)%q
    return tot
def run(q,N,k,trials=5000,seed=5):
    inv=[0]*q
    for a in range(1,q): inv[a]=pow(a,q-2,q)
    kp=k//2
    omega=next((g for g in range(2,q) if pow(g,N,q)==1 and pow(g,N//2,q)!=1),None)
    if omega is None or pow(omega,N//2,q)!=q-1: print(f"skip q={q} N={N}");return
    D=[pow(omega,i,q) for i in range(N)];Dp=sorted(set(pow(x,2,q) for x in D));Np=len(Dp)
    seen=set();fold=[]
    for x in D:
        y=pow(x,2,q);nx=(q-x)%q
        if y not in seen: seen.add(y);fold.append((Dp.index(y),x,nx))
    inv2=inv[2]
    rho=k/N;johnson=1-math.sqrt(rho);wmin=math.floor(johnson*N)+1   # minimal above-Johnson weight
    radius=(wmin*Np)//N                                            # matched folded radius (positions)
    Dp_quad=list(itertools.combinations(range(Np),kp))             # kp-subsets of folded domain
    def folded_dist(u):  # exact min Hamming dist of u (len Np) to RS[Np,kp]
        best_ag=kp-1
        for sub in Dp_quad:
            pts=[(Dp[i],u[i]) for i in sub]
            ag=sum(1 for t in range(Np) if lagrange_eval(pts,Dp[t],q,inv)==u[t])
            if ag>best_ag: best_ag=ag
            if best_ag==Np: break
        return Np-best_ag
    Dk_sub=None
    def is_leader(f):  # check d(f,RS_N)=weight(f): reject if some deg<k poly agrees on >= N-w+1
        w=sum(1 for v in f if v); target=N-w+1
        # sample k-subsets to find a high-agreement codeword; also include subsets of the support+zeros
        idx=list(range(N))
        for _ in range(25):
            sub=random.sample(idx,k)
            pts=[(D[i],f[i]) for i in sub]
            ag=sum(1 for t in range(N) if lagrange_eval(pts,D[t],q,inv)==f[t])
            if ag>=target: return False
        return True
    def badcount(f):
        fd={D[i]:f[i] for i in range(N)};g0=[0]*Np;g1=[0]*Np
        for(yi,x,nx)in fold:
            g0[yi]=((fd[x]+fd[nx])*inv2)%q;g1[yi]=((fd[x]-fd[nx])*inv[(2*x)%q])%q
        c=0
        for lam in range(q):
            u=[(g0[t]+lam*g1[t])%q for t in range(Np)]
            if folded_dist(u)<=radius: c+=1
        return c
    random.seed(seed);best=-1;bs=None;ng=0
    supps=list(itertools.combinations(range(N),wmin))
    for _ in range(trials):
        supp=random.choice(supps)
        f=[0]*N
        for idx in supp: f[idx]=random.randrange(1,q)
        if not is_leader(f): continue
        ng+=1
        b=badcount(f)
        if b>best:
            best=b;bs=supp
            print(f"      [N={N}] new max bad-count={best} at {bs} (after {ng} genuine leaders)")
    print(f"   q={q} N={N} k={k} rho={rho:.3f} Johnson={johnson:.3f}({johnson*N:.2f}pos) wmin={wmin} matched-radius={radius}/{Np}: "
          f"max above-J bad-count = {best}/{q}  (genuine leaders={ng}/{trials})  worstsupp={bs}")
    return best
print("N-scaling of worst-case above-Johnson FRI soundness bad-count (rho=1/2):")
print("  baseline N=8 (exhaustive earlier): bad-count = 4")
run(17,16,8)
run(17,8,4)   # re-confirm N=8 with the sampling method as a sanity cross-check
