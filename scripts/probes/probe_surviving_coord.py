# Verify SurvivingTPrimeCoord across the deep stratum: for deep pairs T,T' (|T∩T'|=j, k<j<k+m+1),
# does there EXIST a coordinate d such that the m+1 functionals {T-band coeffs k+1..k+m of I_T} ∪
# {coeff_{k+1+d} of I_{T'}} are jointly SURJECTIVE (rank m+1) over the generator coeff space?
# I_T = degree<(k+m+1) interpolant of genPoly on T's points. Functionals are linear in genPoly coeffs.
import itertools, numpy as np
np.set_printoptions(linewidth=200)
def vander_interp_band(points_idx, dom, k, m, M, p):
    # For a degree<M generator with coeff vector c (len M), I_T = interpolant of genPoly|_T (deg<k+m+1).
    # coeff_{k+1+j}(I_T) is linear in c. Build that linear functional row (len M) over F_p.
    # genPoly(x)=sum c_t x^t. values on T: V_T c where V_T[i,t]=dom[i]^t. Interpolant coeffs on T:
    # A_T = (Vandermonde of T's k+m+1 nodes)^{-1} @ values = (W_T^{-1} @ V_T) c, where W_T[i,s]=node_i^s, s<k+m+1.
    nodes=[dom[i] for i in points_idx]  # k+m+1 nodes
    deg=k+m+1
    W=np.array([[pow(nd,s,p) for s in range(deg)] for nd in nodes],dtype=object)%p
    V=np.array([[pow(nd,t,p) for t in range(M)] for nd in nodes],dtype=object)%p
    Winv=matinv_modp(W,p)
    A=(Winv@V)%p   # deg x M : interpolant coeffs as linear in c
    return A  # row s = coeff_s(I_T) as functional over c
def matinv_modp(Mx,p):
    Mx=np.array(Mx,dtype=object)%p; nn=Mx.shape[0]
    Aug=np.concatenate([Mx,np.eye(nn,dtype=object)],axis=1)%p
    for col in range(nn):
        piv=None
        for r in range(col,nn):
            if Aug[r,col]%p!=0: piv=r;break
        Aug[[col,piv]]=Aug[[piv,col]]
        inv=pow(int(Aug[col,col]),p-2,p)
        Aug[col]=(Aug[col]*inv)%p
        for r in range(nn):
            if r!=col and Aug[r,col]%p!=0:
                Aug[r]=(Aug[r]-Aug[r,col]*Aug[col])%p
    return Aug[:,nn:]%p
def rank_modp(rows,p):
    Mx=np.array(rows,dtype=object)%p; R=Mx.copy(); nr,nc=R.shape; rank=0; rr=0
    for c in range(nc):
        piv=None
        for r in range(rr,nr):
            if R[r,c]%p!=0: piv=r;break
        if piv is None: continue
        R[[rr,piv]]=R[[piv,rr]]
        inv=pow(int(R[rr,c]),p-2,p); R[rr]=(R[rr]*inv)%p
        for r in range(nr):
            if r!=rr and R[r,c]%p!=0: R[r]=(R[r]-R[r,c]*R[rr])%p
        rr+=1; rank+=1
        if rr==nr: break
    return rank
p=101
print("k m j(overlap)  exists_d_surjective(rank=m+1)?  best_rank  trivial_m")
for k in [1,2]:
  for m in [1,2]:
    n=k+m+5; dom=list(range(1,n+1)); M=n  # generator deg<M=n
    full=list(range(k+m+1))  # T = first k+m+1 indices
    for j in range(k+1, k+m+1):  # deep overlap
        # T' shares j points with T, has (k+m+1-j) new points
        Tset=full
        overlap=full[:j]; newpts=list(range(k+m+1, k+m+1+(k+m+1-j)))
        Tp=overlap+newpts
        if max(Tp)>=n: continue
        A_T=vander_interp_band(Tset,dom,k,m,M,p)   # deg x M
        A_Tp=vander_interp_band(Tp,dom,k,m,M,p)
        Tband=[A_T[k+1+jj] for jj in range(m)]     # m functionals
        best=0; found=False
        for d in range(m):
            rows=Tband+[A_Tp[k+1+d]]
            r=rank_modp(rows,p); best=max(best,r)
            if r==m+1: found=True
        print(f" {k} {m}   j={j}        exists_d={found}              {best}        m={m}")

print("\n=== FULL exact pair-coherence rank 2m+1-(j-k) verification ===")
print("k m j  full_rank{T-band(m), T'-band(m), value(1)}  predicted 2m+1-(j-k)  match")
for k in [1,2,3]:
  for m in [1,2,3]:
    n=k+m+6; dom=list(range(1,n+1)); M=n
    full=list(range(k+m+1))
    for j in range(k+1, k+m+1):
        overlap=full[:j]; newpts=list(range(k+m+1, k+m+1+(k+m+1-j)))
        Tp=overlap+newpts
        if max(Tp)>=n: continue
        A_T=vander_interp_band(full,dom,k,m,M,p); A_Tp=vander_interp_band(Tp,dom,k,m,M,p)
        rows=[A_T[k+1+jj] for jj in range(m)]+[A_Tp[k+1+jj] for jj in range(m)]+[ (A_T[k]-A_Tp[k])%p ]
        r=rank_modp(rows,p); pred=2*m+1-(j-k)
        print(f"{k} {m} j={j}    {r}                          {pred}            {r==pred}")
