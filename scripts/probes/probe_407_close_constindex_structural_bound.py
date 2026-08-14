#!/usr/bin/env python3
"""
#407 STRUCTURAL BOUND verification: at CONSTANT index m, is A_k <= C^k k! n^k with C=C(m) ABSOLUTE?

PROVEN INPUTS (in-tree, axiom-clean, ConstantIndexGaussSumBound.lean):
  (P1) M := max_{b!=0}|eta_b| <= ((m-1)sqrt(p)+1)/m =: B,  with p=mn+1.  =>  M <= sqrt(m)*sqrt(n)*(1+o(1)).
  (P2, Parseval) sum_{b!=0}|eta_b|^2 = p*E_1 - n^2 = p*n - n^2 = n(p-n) = n^2(m-1)+... <= n*p.
       [E_1 = #{x=y in mu_n} = n, so sum_b|eta_b|^2 = p*n, minus b=0 term n^2.]

STRUCTURAL DERIVATION of A_k:
  A_k = (1/p) sum_{b!=0} |eta_b|^{2k}
      = (1/p) sum_{b!=0} |eta_b|^2 * |eta_b|^{2(k-1)}
      <= (1/p) * M^{2(k-1)} * sum_{b!=0}|eta_b|^2          [holder/trivial: pull sup of the (k-1) extra factors]
      <= (1/p) * M^{2(k-1)} * (p*n)
      = n * M^{2(k-1)}
      <= n * (m n)^{k-1}                                    [by P1: M^2 <= m n]
      = m^{k-1} * n^k.
  => A_k <= m^{k-1} n^k <= m^k n^k.  This is a CLEAN PROVEN-INPUT bound A_k <= C^k n^k, C=m.
  (No k! -- it's actually BETTER: A_k <= m^{k-1} n^k <= (1/m)(m^k n^k), and the conjectured
   C^k k! n^k is WEAKER, so the structural bound IMPLIES the conjecture with C=m.)

VERIFY: ratio R_k := A_k / (m^{k-1} n^k) should be <= 1 (structural bound) for ALL feasible (n,m,k).
ALSO report A_k / (n * M^{2(k-1)}) <= 1 (the sharper Holder step) and A_k/(k! n^k) (=C_k^k).
"""
import numpy as np, math

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    if x % 3 == 0: return x == 3
    d = 5
    while d*d <= x:
        if x % d == 0 or x % (d+2) == 0: return False
        d += 6
    return True

def primroot(p):
    if p == 2: return 1
    phi = p-1; fs=[]; m=phi; d=2
    while d*d<=m:
        if m%d==0:
            fs.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fs.append(m)
    for a in range(2,p):
        if all(pow(a,phi//q,p)!=1 for q in fs): return a

def subgroup(p,n):
    g=pow(primroot(p),(p-1)//n,p); dom=[]; x=1
    for _ in range(n): dom.append(x); x=x*g%p
    return dom

def abs_eta(p,dom):
    ind=np.zeros(p);
    for x in dom: ind[x]=1.0
    return np.abs(np.fft.fft(ind))

print("Structural bound check: A_k <= m^{k-1} n^k (PROVEN-INPUT via M<=sqrt(mn) + Parseval).")
print("R_struct = A_k/(m^{k-1} n^k) MUST be <= 1.   R_holder = A_k/(n M^{2(k-1)}) MUST be <=1 (tighter).")
print("Also report Mq = M^2/(mn) (proven <=~1) and C_k=(A_k/(k! n^k))^{1/k}.")
print(f"{'n':>8} {'m':>4} {'p':>10} {'M2/(mn)':>8} | " + " ".join(f"k={k}:Rstr/Rhol".rjust(16) for k in (2,3,4,5,6)))
worst_struct=0.0; worst_holder=0.0
for mu in range(3,21):
    n=2**mu
    # smallest index t with t*n+1 prime, t in 2..200
    p=None; t=2
    while t<=400:
        c=t*n+1
        if c>30_000_000: break
        if isprime(c): p=c; break
        t+=1
    if p is None: continue
    m=(p-1)//n
    dom=subgroup(p,n); A=abs_eta(p,dom)
    M=float(np.max(A[1:])); A2=A[1:]**2
    cells=[]
    for k in (2,3,4,5,6):
        Ak=float(np.sum(A2**k))/p
        Rstruct=Ak/((m**(k-1))*(n**k))
        Rholder=Ak/(n*(M**(2*(k-1)))) if M>0 else 0
        worst_struct=max(worst_struct,Rstruct); worst_holder=max(worst_holder,Rholder)
        cells.append(f"{Rstruct:.4f}/{Rholder:.4f}".rjust(16))
    print(f"{n:>8} {m:>4} {p:>10} {M*M/(m*n):>8.4f} | "+" ".join(cells), flush=True)
print()
print(f"WORST R_struct over all = {worst_struct:.4f}  (must be <=1 for the proven structural bound to hold)")
print(f"WORST R_holder over all = {worst_holder:.4f}  (the Holder step A_k <= n M^{{2(k-1)}})")
print()
print("CONCLUSION: if R_struct <= 1 everywhere, then A_k <= m^{k-1} n^k is a THEOREM at constant index")
print("(inputs P1,P2 both PROVEN axiom-clean in ConstantIndexGaussSumBound.lean) => C(m)=m BOUNDED, NO BGK.")
