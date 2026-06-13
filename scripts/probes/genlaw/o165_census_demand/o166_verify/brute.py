# Fully from-scratch Python brute force. Shares NO code with either C kernel.
# Method: build bordered Vandermonde matrix, compute det via numpy-free pure-python
# fraction-free Bareiss over GF(p) using sympy-free integer arithmetic. Different
# determinant algorithm AGAIN (Bareiss, not Gauss-with-inverse, not Laplace).
import itertools, sys
def find_root(p,n):
    e=(p-1)//n
    for c in range(2,1000):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1:
            return [pow(h,i,p) for i in range(n)]
    raise SystemExit("no root")
def det_bareiss(M,p):
    # fraction-free Bareiss determinant mod p (DIFFERENT algo from Gauss/Laplace)
    M=[row[:] for row in M]; n=len(M); prev=1; sign=1
    for k in range(n-1):
        if M[k][k]==0:
            sw=-1
            for i in range(k+1,n):
                if M[i][k]!=0: sw=i;break
            if sw<0: return 0
            M[k],M[sw]=M[sw],M[k]; sign=-sign
        for i in range(k+1,n):
            for j in range(k+1,n):
                M[i][j]=( (M[i][j]*M[k][k]-M[i][k]*M[k][j]) * pow(prev,p-2,p) )%p
        prev=M[k][k]
    return (sign*M[n-1][n-1])%p
def residual(dom,k,t,y,p):
    # rows = t (len k+1); cols 0..k-1 powers, col k = y
    M=[[pow(dom[ti],b,p) for b in range(k)]+[y[ti]] for ti in t]
    return det_bareiss(M,p)
def count(dom,k,a,U0,U1,p,n):
    al=0; bad=set()
    for S in itertools.combinations(range(n),a):
        gam=None; nondeg=False; any1=False; ok=True; pin=None
        for t in itertools.combinations(S,k+1):
            r0=residual(dom,k,t,U0,p); r1=residual(dom,k,t,U1,p)
            if r0 or r1: nondeg=True
            if r1==0:
                if r0!=0: ok=False; break
            else:
                any1=True
                g=((-r0)*pow(r1,p-2,p))%p
                if gam is None: gam=g
                elif gam!=g: ok=False; break
        if ok and nondeg:
            al+=1
            if any1: bad.add(gam)
    return al,len(bad)
p=2013265921; n=16
dom=find_root(p,n)
# KKH26 r=3 deep band a0=4
r=3;k=r-1;a0=r+1
U0=[pow(x,r,p) for x in dom]; U1=[pow(x,r-1,p) for x in dom]
al,bad=count(dom,k,a0,U0,U1,p,n); print(f"BRUTE KKH26 r=3 deep a0=4: #align={al} #bad={bad}  (expect 0,0)")
# worst monomial r=3 maximizer (x^8,x^7)
U0=[pow(x,8,p) for x in dom]; U1=[pow(x,7,p) for x in dom]
al,bad=count(dom,k,a0,U0,U1,p,n); print(f"BRUTE worst r=3 (x^8,x^7): #align={al} #bad={bad}  (expect #bad=97)")
# codeword literal-form r=3 (x^0,x^2)
U0=[pow(x,0,p) for x in dom]; U1=[pow(x,2,p) for x in dom]
al,bad=count(dom,k,a0,U0,U1,p,n); print(f"BRUTE codeword r=3 (x^0,x^2): #align={al} #bad={bad}  (expect 1820,1)")
