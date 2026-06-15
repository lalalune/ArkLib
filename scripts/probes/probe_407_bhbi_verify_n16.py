#!/usr/bin/env python3
"""Adversarial confirm: at n=16, p=65537, prove EXACTLY that
   BHBI(omega,8,3) is TRUE  (no nonzero relation, all |coeff|<=3)  and
   BHBI(omega,8,4) is FALSE (a height-4 witness exists).
Full vectorized brute over the box (numpy chunked), no MITM, independent engine."""
import numpy as np
p=65537; m=4; n=16; N=8
def prim(p,m):
    e=(p-1)//(1<<m)
    for b in range(2,p):
        w=pow(b,e,p)
        if pow(w,(1<<m)//2,p)==p-1: return w
prim_w=prim(p,m)
powers=np.array([pow(prim_w,j,p) for j in range(N)],dtype=np.int64)
print(f"p={p} omega={prim_w} powers={powers.tolist()}")
print(f"check omega^16={pow(prim_w,16,p)} (=1), omega^8={pow(prim_w,8,p)} (={p-1})")

def has_relation(Cmax):
    """Full brute over [-Cmax,Cmax]^8 in numpy chunks; return min-height witness or None."""
    vals=np.arange(-Cmax,Cmax+1,dtype=np.int64)
    M=len(vals)
    # iterate first 2 coords in python (M^2), vectorize last 6 (M^6) -- M=7 -> 117k rows/chunk
    tail=np.array(np.meshgrid(*([vals]*6),indexing='ij')).reshape(6,-1).T  # (M^6,6)
    tailres=(tail@powers[2:])%p
    tailh=np.max(np.abs(tail),axis=1)
    best=None
    for a in vals:
        for b in vals:
            head=(a*powers[0]+b*powers[1])%p
            hh=max(abs(a),abs(b))
            mask=((head+tailres)%p==0)
            if mask.any():
                idx=np.where(mask)[0]
                for i in idx:
                    full=(int(a),int(b))+tuple(int(x) for x in tail[i])
                    if any(full):
                        h=max(hh,int(tailh[i]))
                        if best is None or h<best[0]:
                            best=(h,full)
    return best

for Cmax in [3,4]:
    r=has_relation(Cmax)
    if r is None:
        print(f"box {Cmax}: NO nonzero relation => BHBI(omega,8,{Cmax}) is TRUE")
    else:
        # verify witness exactly
        s=sum(c*int(x) for c,x in zip(r[1],powers))%p
        print(f"box {Cmax}: min height={r[0]} witness={r[1]} verify sum={s}(=0) => BHBI(omega,8,{r[0]}) FALSE; BHBI for C<{r[0]} TRUE")
