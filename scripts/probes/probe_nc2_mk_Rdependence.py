#!/usr/bin/env python3
"""
probe_nc2_mk_Rdependence.py (DO NOT COMMIT)

The decisive structural test. The Markov-Krein 'max given moments m_1..m_{2R}'
answer is the largest Gauss node L_R. Two facts to nail:

 (A) L_R is a NON-DECREASING function of R that converges to the true sup only as
     R -> infinity. With ONLY a fixed finite R of proven char-0 moments, L_R does NOT
     reach the true M(n) -- so 'use the first R proven moments' gives NO valid upper
     bound on M(n) (it gives a LOWER fence). To upper-bound the sup you need the FULL
     moment sequence + sub-Gaussian tail = the open transfer.

 (B) The sub-Gaussian extreme value sqrt(2 n log q): for this to come out of moments,
     you need R ~ log q moments AND each char-p moment <= char-0 Wick moment. We test
     whether the char-p (true) moments stay <= char-0 Wick moments at every r up to
     r ~ log q. If they EXCEED char-0 at some r <= log q, the family's 'char-0 moments
     suffice' claim is refuted (per-r char-p transfer is unavoidable, = the open part).
"""
import numpy as np
from math import log, sqrt
import sympy

def find_prime(target_n, beta):
    mu = int(round(log(target_n, 2))); n = 2**mu
    qtarget = int(target_n**beta); k = max(2, qtarget // n)
    for _ in range(500000):
        q = k*n + 1
        if sympy.isprime(q): return q, n, mu
        k += 1
    return None, n, mu

def subgroup(q, n):
    g = sympy.primitive_root(q); h = pow(g, (q-1)//n, q)
    S = []; x = 1
    for _ in range(n): S.append(x); x = (x*h) % q
    return S

def abseta_nz(q, S):
    S = np.array(S); bs = np.arange(1, q)
    ang = 2*np.pi/q * (np.outer(bs, S) % q)
    eta = np.cos(ang).sum(1) + 1j*np.sin(ang).sum(1)
    return np.abs(eta)

def dfact(r):
    p = 1
    for k in range(1, 2*r, 2): p *= k
    return p

def largest_gauss_node(moments):
    R = (len(moments)-1)//2
    H0 = np.array([[moments[i+j] for j in range(R)] for i in range(R)])
    H1 = np.array([[moments[i+j+1] for j in range(R)] for i in range(R)])
    try:
        ev = np.linalg.eigvals(np.linalg.solve(H0, H1)).real
        return float(ev.max())
    except Exception:
        return None

print("="*72)
print("(A) L_R vs R: does the Markov-Krein max-node reach the true M(n) at finite R?")
print("(B) char-p moment vs char-0 Wick ceiling at each r up to r~log q")
print("="*72)
for tn, beta in [(16, 4.0), (32, 3.5), (64, 3.0)]:
    q, n, mu = find_prime(tn, beta)
    if q is None: continue
    S = subgroup(q, n); ae = abseta_nz(q, S); e2 = ae**2
    Mtrue = ae.max(); Mtrue2 = Mtrue**2
    logq = log(q)
    print(f"\nn={n} q={q} beta={logq/log(n):.2f}  M(n)={Mtrue:.3f}  M^2={Mtrue2:.2f}"
          f"  sqrt(2 n log q)={sqrt(2*n*logq):.3f}  (log q={logq:.2f})")
    # (A) sweep R
    print("   R :  L_R (max Gauss node)   sqrt(L_R)   reaches M^2?")
    for R in range(1, min(8, n//2)+1):
        mom = [1.0] + [float(np.mean(e2**r)) for r in range(1, 2*R+1)]
        L = largest_gauss_node(mom)
        if L is None:
            print(f"   {R} :  (singular)"); continue
        print(f"   {R} :  {L:10.3f}            {sqrt(max(L,0)):7.3f}    {'YES' if L>=Mtrue2-1e-6 else 'no (under by %.1f%%)'%(100*(Mtrue2-L)/Mtrue2)}")
    # (B) per-r char-p vs char-0 Wick ceiling, up to r ~ log q
    print("   per-r: m_r(char-p true)  vs  E_r=(2r-1)!! n^r (char-0 Wick ceiling)")
    Rmax = max(2, int(round(logq)))
    bad = []
    for r in range(1, Rmax+1):
        # true b-summed 2r-th moment = sum_{b!=0} eta_b^{2r}; char-0 prediction = q*E_r - n^{2r}
        true_sum = float(np.sum(e2**r))           # sum over b!=0 of eta_b^{2r}
        char0_Er = dfact(r)*n**r
        char0_sum = q*char0_Er - n**(2*r)         # since sum_{all b} eta_b^{2r} = q*E_r, minus b=0 term n^{2r}
        ratio = true_sum/char0_sum if char0_sum>0 else float('nan')
        flag = "" if ratio <= 1.0+1e-9 else "  <-- EXCEEDS char-0!"
        if ratio > 1.0+1e-9: bad.append(r)
        if r <= 12 or ratio>1:
            print(f"      r={r:2d}: true/char0_Wick = {ratio:.4f}{flag}")
    if bad:
        print(f"   >>> char-p EXCEEDS char-0 Wick ceiling at r={bad}  => char-0 moments do NOT dominate; per-r transfer needed.")
    else:
        print(f"   >>> char-p <= char-0 Wick at all r<=log q here (consistent, but this IS the open transfer claim).")
