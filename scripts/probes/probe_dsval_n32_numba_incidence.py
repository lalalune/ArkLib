import numpy as np, math
from numba import njit
TAU=2*math.pi

@njit(cache=True)
def gamma_if_consistent(X, k, a, b, w):
    # M = [x^0..x^{k-1}, x^a, x^b] (w x (k+2)). Consistent iff rank<=k+1.
    kk=k+2
    M=np.zeros((w,kk),dtype=np.complex128)
    for i in range(w):
        x=X[i]
        p=1.0+0j
        for c in range(k):
            M[i,c]=p; p=p*x
        M[i,k]=x**a; M[i,k+1]=x**b
    # Gram G = M^H M (kk x kk); rank-deficient iff det(G)~0
    G=np.zeros((kk,kk),dtype=np.complex128)
    for r in range(kk):
        for c in range(kk):
            s=0j
            for i in range(w):
                s+=np.conj(M[i,r])*M[i,c]
            G[r,c]=s
    d=np.linalg.det(G)
    if abs(d)>1e-9:   # full rank kk -> not consistent
        return 2,0.0,0.0
    # rank-deficient: find gamma s.t. col_a + gamma col_b in span(first k cols).
    # Solve least squares of (col_a) and (col_b) on first k cols; residuals ra, rb; gamma=-<rb,ra>/<rb,rb>
    V=M[:,:k]
    GV=np.zeros((k,k),dtype=np.complex128)
    for r in range(k):
        for c in range(k):
            s=0j
            for i in range(w): s+=np.conj(V[i,r])*V[i,c]
            GV[r,c]=s
    GVi=np.linalg.pinv(GV)
    def resid(col):
        # V^H col
        vc=np.zeros(k,dtype=np.complex128)
        for r in range(k):
            s=0j
            for i in range(w): s+=np.conj(V[i,r])*col[i]
            vc[r]=s
        coef=GVi@vc
        rr=col.copy()
        for i in range(w):
            acc=0j
            for c in range(k): acc+=V[i,c]*coef[c]
            rr[i]=col[i]-acc
        return rr
    ra=resid(M[:,k]); rb=resid(M[:,k+1])
    nb=0.0
    for i in range(w): nb+=(rb[i].real**2+rb[i].imag**2)
    na=0.0
    for i in range(w): na+=(ra[i].real**2+ra[i].imag**2)
    if nb<1e-12: return 2,0.0,0.0
    if na<1e-12: return 1,0.0,0.0   # gamma=0
    num=0j
    for i in range(w): num+=np.conj(rb[i])*ra[i]
    lam=num/nb
    # check parallel
    err=0.0
    for i in range(w):
        e=ra[i]-lam*rb[i]; err+=(e.real**2+e.imag**2)
    if err>1e-12*na: return 2,0.0,0.0
    g=-lam
    return 0, g.real, g.imag

@njit(cache=True)
def scan(X,k,a,b,w,comb):  # comb: (Ncomb,w) int array of subsets
    gr=np.empty(comb.shape[0]); gi=np.empty(comb.shape[0]); fl=np.empty(comb.shape[0],dtype=np.int64)
    Xs=np.empty(w,dtype=np.complex128)
    for t in range(comb.shape[0]):
        for j in range(w): Xs[j]=X[comb[t,j]]
        f,re,im=gamma_if_consistent(Xs,k,a,b,w)
        fl[t]=f; gr[t]=re; gi[t]=im
    return fl,gr,gi

def incidence(n,k,a,b,w):
    X=np.exp(1j*TAU*np.arange(n)/n)
    from itertools import combinations
    comb=np.array(list(combinations(range(n),w)),dtype=np.int64)
    fl,gr,gi=scan(X,k,a,b,w,comb)
    gammas=set()
    for t in range(len(fl)):
        if fl[t]==1: gammas.add((0.0,0.0))
        elif fl[t]==0: gammas.add((round(gr[t],3),round(gi[t],3)))
    return len(gammas), comb.shape[0]

if __name__=="__main__":
    # warm + validate at n=16 (known: rho1/4 worst dir(8,14) w=7 I=9 -> delta*=0.5625)
    print("validate n=16:", incidence(16,4,8,14,7), "(expect ~9)")
    n=32; budget=32
    print("n=32 rho=1/4 k=8: worst-candidate incidence per band (m*=w*-k):")
    for w in [10,11,12,13]:
        mx=0;md=None
        for (a,b) in [(16,18),(16,20),(16,22),(16,24),(8,14),(12,20)]:
            if not(8<=a<b<n): continue
            I,nc=incidence(n,8,a,b,w)
            if I>mx: mx=I;md=(a,b)
        print(f"  w={w} delta={1-w/n:.4f} maxI={mx} dir={md} [{'>budget' if mx>budget else '<=budget'}]", flush=True)
