import numpy as np, math, sys
from itertools import combinations, islice
from numba import njit
TAU=2*math.pi
@njit(cache=True)
def scan_chunk(X,k,a,b,w,comb,outr,outi,outf):
    Xs=np.empty(w,dtype=np.complex128)
    kk=k+2
    for t in range(comb.shape[0]):
        for j in range(w): Xs[j]=X[comb[t,j]]
        M=np.zeros((w,kk),dtype=np.complex128)
        for i in range(w):
            x=Xs[i]; p=1.0+0j
            for c in range(k): M[i,c]=p; p=p*x
            M[i,k]=x**a; M[i,k+1]=x**b
        G=np.zeros((kk,kk),dtype=np.complex128)
        for r in range(kk):
            for c in range(kk):
                s=0j
                for i in range(w): s+=np.conj(M[i,r])*M[i,c]
                G[r,c]=s
        if abs(np.linalg.det(G))>1e-9: outf[t]=2; continue
        V=M[:,:k]
        GV=np.zeros((k,k),dtype=np.complex128)
        for r in range(k):
            for c in range(k):
                s=0j
                for i in range(w): s+=np.conj(V[i,r])*V[i,c]
                GV[r,c]=s
        GVi=np.linalg.pinv(GV)
        ra=M[:,k].copy(); rb=M[:,k+1].copy()
        for which in range(2):
            col=M[:,k+which]
            vc=np.zeros(k,dtype=np.complex128)
            for r in range(k):
                s=0j
                for i in range(w): s+=np.conj(V[i,r])*col[i]
                vc[r]=s
            coef=GVi@vc
            for i in range(w):
                acc=0j
                for c in range(k): acc+=V[i,c]*coef[c]
                if which==0: ra[i]=col[i]-acc
                else: rb[i]=col[i]-acc
        na=0.0;nb=0.0
        for i in range(w): na+=ra[i].real**2+ra[i].imag**2; nb+=rb[i].real**2+rb[i].imag**2
        if nb<1e-12: outf[t]=2; continue
        if na<1e-12: outf[t]=1; continue
        num=0j
        for i in range(w): num+=np.conj(rb[i])*ra[i]
        lam=num/nb; err=0.0
        for i in range(w):
            e=ra[i]-lam*rb[i]; err+=e.real**2+e.imag**2
        if err>1e-12*na: outf[t]=2; continue
        g=-lam; outf[t]=0; outr[t]=g.real; outi[t]=g.imag

def incidence(n,k,a,b,w,chunk=1_500_000):
    X=np.exp(1j*TAU*np.arange(n)/n)
    it=combinations(range(n),w); gammas=set(); total=0
    while True:
        block=list(islice(it,chunk))
        if not block: break
        comb=np.array(block,dtype=np.int64); total+=len(block)
        outr=np.zeros(len(block));outi=np.zeros(len(block));outf=np.zeros(len(block),dtype=np.int64)
        scan_chunk(X,k,a,b,w,comb,outr,outi,outf)
        for t in range(len(block)):
            if outf[t]==1: gammas.add((0.0,0.0))
            elif outf[t]==0: gammas.add((round(outr[t],3),round(outi[t],3)))
        if len(gammas)>n:  # already exceeds budget -> can stop early for the >budget verdict
            return len(gammas), total, True
    return len(gammas), total, False
print("validate n=16 dir(8,14) w=7:",incidence(16,4,8,14,7),"(expect ~9)",flush=True)
n=32
for w in [11,12]:
    for (a,b) in [(16,22),(16,20)]:
        I,tot,early=incidence(n,8,a,b,w)
        print(f"n=32 k=8 dir({a},{b}) w={w} delta={1-w/n:.4f}: I={I}{'+(>budget,early-stop)' if early else ''} [{'>32' if I>32 else '<=32'}]",flush=True)

# STATUS (2026-06-15): numba-JIT, memory-safe (chunked + early-stop at I>budget). CORRECT + reusable.
# n=16 worst-dir validated. n=32 worst-direction is the DECISIVE adjudication (bounded m*=3 vs growing
# ~log n) but is minutes-per-band single-threaded (C(32,11)=1.3e8, C(32,12)=2.25e8 subsets; full scan
# needed when I<=budget since early-stop only fires when I EXCEEDS budget). Needs a longer/parallel run
# or numba parallel=True + prange to settle. Data so far (brute-force n=8,16 + A2 sumset model n<=64)
# LEANS BOUNDED m*~3 (delta*=1-rho-3/n), which would REFUTE the conjectured window-edge 1-rho-Theta(1/log n)
# -- but n=8,16 cannot separate 3 from log2 n, so n>=32 worst-direction is REQUIRED to confirm/refute.
