#!/usr/bin/env python3
"""THE MID-WINDOW FORK RECORD (#371, Fable rounds 5-7): tuned alignment above UDR.

Consolidated record of the tuned-(R0,R1) alignment experiments in (UDR, capacity)
and their q-scaling verdict.  Method: for targets {(T_i, gamma_i)}, the alignment
conditions "rep((l1*R0 + gamma*l0*R1)*Z_S^{-1} mod l0*l1) has degree <= j" are
cost := n-k-w linear conditions per target on (R0,R1); the kernel of the stacked
system always contains the 2k-dimensional DEGENERATE space (R0 in l0*P, R1 in l1*P),
so the genuine tuning budget is exactly 2w dimensions (kernel dims measured 2k at
six instances).  Within budget (targets*cost <= 2w-1), genuine tuned stacks exist.

RESULTS (exact mcaEvent verification, no-joint included):
  (37,12,6) w=4 (e=2, rate 1/2):  q=37: bad=14 > n;  q=61/73: similar smallfield;
                                  q=1153 >> C(12,3): bad = 3 = TARGETS EXACTLY.
  (97,16,8) w=6 (e=4, rate 1/2, delta=.375 in (Johnson,capacity)): bad=67~0.69q --
                                  small-field saturation (q << C(16,5)=4368).
  (97,16,4) w=9 (rate 1/4):       expl=97, bad=5: the no-joint clause kills 94%
                                  (rate-sensitivity; small-field caveat applies).
  cost-1 band w=n-k-1:            ALL q scalars bad -- the GENERIC saturation band
                                  (= in-tree SmoothWindowSaturation), not tuning.

VERDICT: the mid-window explosions are small-field arithmetic surplus (the census
two-layer law in a new domain); at q >> poly(n) the per-stack tuned count is
O(w/(n-k-w)).  No production-scale mass production from this mechanism; the
above-UDR four-face core is unchanged.  The corank lane's C(n,2)-saturation at the
e=1 slice (cb6623fbf) is corank-structural and does not continue at e=2.

Reproduce: the run2() driver in this file; decisive cell run2(1153,12,6,4,3).
"""
import random
from itertools import combinations
exec(open(__file__.replace('probe_midwindow_fork_record','probe_aboveudr_cost_law')).read().split('def run(')[0])
random.seed(99)

def nullspace(A, q, nvar):
    M=[r[:] for r in A]; m=len(M); r=0; piv=[]
    for c in range(nvar):
        p=next((i for i in range(r,m) if M[i][c]%q),None)
        if p is None: continue
        M[r],M[p]=M[p],M[r]
        inv=pow(M[r][c],q-2,q); M[r]=[(v*inv)%q for v in M[r]]
        for i in range(m):
            if i!=r and M[i][c]%q:
                f=M[i][c]; M[i]=[(a-f*b)%q for a,b in zip(M[i],M[r])]
        piv.append(c); r+=1
    free=[c for c in range(nvar) if c not in piv]
    basis=[]
    for fc in free:
        v=[0]*nvar; v[fc]=1
        for ri,pc in enumerate(piv): v[pc]=(-M[ri][fc])%q
        basis.append(v)
    return basis

def pdivmod(num,den,q):
    num=num[:]; out=[0]*max(1,len(num)-len(den)+1)
    while den and den[-1]%q==0: den=den[:-1]
    inv=pow(den[-1],q-2,q)
    while True:
        while num and num[-1]%q==0: num.pop()
        if len(num)<len(den): break
        f=num[-1]*inv%q; off=len(num)-len(den); out[off]=f
        for i2 in range(len(den)): num[off+i2]=(num[off+i2]-f*den[i2])%q
        num.pop()
    return out,(num or [0])

def run2(q,n,k,w,n_targets,trials=3,combos=200):
    g=find_gen(q,n)
    if g is None: print(f"({q},{n},{k}) no domain"); return
    dom=[pow(g,i,q) for i in range(n)]
    j=3*w+k-1-n; cost=n-k-w; tmin=n-w
    def rand_denom():
        while True:
            l=[random.randrange(q) for _ in range(w)]+[1]
            if all(evalp(l,x,q) for x in dom): return l
    best=(0,0)
    for tr in range(trials):
        l0=rand_denom(); l1=rand_denom(); m01=pmul(l0,l1,q)
        Xn1=[(-1)%q]+[0]*(n-1)+[1]
        Ts=list(dict.fromkeys(tuple(sorted(random.sample(range(n),w))) for _ in range(n_targets)))
        gammas=random.sample(range(1,q),len(Ts))
        A_rows=[]
        for T,gam in zip(Ts,gammas):
            ZT=[1]
            for i in T: ZT=pmul(ZT,[(-dom[i])%q,1],q)
            ZSinv=pinv(pmod(pmul(Xn1,pinv(ZT,m01,q),q),m01,q),m01,q)
            for cidx in range(j+1,2*w):
                row=[]
                for which,lpoly,scale in ((0,l1,1),(1,l0,gam)):
                    for d in range(w+k):
                        base=pmod(pmul(pmul([0]*d+[1],lpoly,q),ZSinv,q),m01,q)
                        row.append(base[cidx]*scale%q)
                A_rows.append(row)
        basis=nullspace(A_rows,q,2*(w+k))
        found=None
        for _ in range(combos):
            co=[random.randrange(q) for _ in basis]
            v=[0]*(2*(w+k))
            for ci,b in zip(co,basis):
                if ci:
                    for i2 in range(len(v)): v[i2]=(v[i2]+ci*b[i2])%q
            R0,R1=v[:w+k],v[w+k:]
            if not any(R0) or not any(R1): continue
            _,r0m=pdivmod(R0,l0,q); _,r1m=pdivmod(R1,l1,q)
            if not any(c%q for c in r0m) or not any(c%q for c in r1m): continue
            found=(R0,R1); break
        if found is None:
            print(f"  trial {tr}: kernel dim {len(basis)} -- NO genuine vector"); continue
        R0,R1=found
        u0=tuple(evalp(R0,x,q)*pow(evalp(l0,x,q),q-2,q)%q for x in dom)
        u1=tuple(evalp(R1,x,q)*pow(evalp(l1,x,q),q-2,q)%q for x in dom)
        solvek,explset=make_solver(q,n,k,dom)
        subs=list(combinations(range(n),tmin))
        expl=0; bad=0
        for gam in range(q):
            line=[(u0[i]+gam*u1[i])%q for i in range(n)]
            asets=set()
            for S in subs:
                A=explset(list(S),line)
                if A is not None and len(A)>=tmin: asets.add(A)
            if not asets: continue
            expl+=1
            for A in asets:
                if solvek(list(A),list(u0)) is None or solvek(list(A),list(u1)) is None:
                    bad+=1; break
        best=max(best,(bad,expl))
        print(f"  trial {tr}: kernel dim {len(basis)} genuine ok -> (bad,expl)=({bad},{expl})")
    pred=(2*w)//max(cost,1)
    print(f"({q},{n},{k}) w={w} cost={cost} -> BEST (bad,expl)={best}  corrected-pred ~{pred}+base")


if __name__ == "__main__":
    run2(37,12,6,4,3)
    run2(1153,12,6,4,3,trials=1)
