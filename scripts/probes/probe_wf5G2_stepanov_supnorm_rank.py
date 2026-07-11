#!/usr/bin/env python3
"""probe(#444 wf-G2): rank of the order-M vanishing system on the phase-bad set (mod p, fast)."""
import numpy as np, sympy

def subgroup(p,n):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); S,c=[],1
    for _ in range(n): S.append(c); c=c*h%p
    return sorted(S)
def find_prime(n,beta):
    m=max(2,n**beta//n)
    while True:
        p=m*n+1
        if sympy.isprime(p) and p>n**3: return p
        m+=1
def modrank(rows,Ccol,p):
    A=[r[:] for r in rows]; R=len(A); rk=0
    for col in range(Ccol):
        piv=None
        for i in range(rk,R):
            if A[i][col]%p!=0: piv=i;break
        if piv is None: continue
        A[rk],A[piv]=A[piv],A[rk]
        inv=pow(A[rk][col],p-2,p)
        A[rk]=[(v*inv)%p for v in A[rk]]
        for i in range(R):
            if i!=rk and A[i][col]%p!=0:
                f=A[i][col]; A[i]=[(A[i][k]-f*A[rk][k])%p for k in range(Ccol)]
        rk+=1
        if rk==Ccol: break
    return rk
def order_M_rank(B,M,p):
    D=M*len(B)-1; rows=[]
    for x in B:
        for j in range(M):
            row=[]
            for i in range(D+1):
                if i<j: row.append(0)
                else:
                    c=1
                    for t in range(j): c=c*(i-t)%p
                    row.append(c*pow(x,i-j,p)%p)
            rows.append(row)
    return D, modrank(rows,D+1,p)

print("rank of order-M vanishing system on phase-bad set B (n/2 worst-b interval slice)")
print(f"{'mu':>3}{'n':>5}{'M':>3}{'|B|':>5}{'M|B|':>6}{'rank':>6}{'#coef':>7} {'genuine-saving?'}")
for mu in (4,5,6):
    n=2**mu; p=find_prime(n,4); S=subgroup(p,n)
    bb,bm=1,0
    for b in range(1,min(p,3000)):
        z=np.exp(2j*np.pi*(np.array(S,float)*b%p)/p).sum()
        if abs(z)>bm: bm,bb=abs(z),b
    res=np.array([(bb*x)%p for x in S]); signed=np.where(res>p//2,res-p,res)
    order=np.argsort(np.abs(signed)); k=n//2; B=[S[i] for i in order[:k]]
    for M in (2,3):
        D,rk=order_M_rank(B,M,p)
        print(f"{mu:>3}{n:>5}{M:>3}{k:>5}{M*k:>6}{rk:>6}{D+1:>7}  {rk<M*k}")
print()
print("rank == M|B| => FULL rank => smallest auxiliary degree = M|B|-1 => Stepanov |B|<=(M|B|-1)/M")
print("  = trivial; NO algebraic degeneracy in the phase-bad set; M(n) stays ~n. Past-Johnson FAILS.")
