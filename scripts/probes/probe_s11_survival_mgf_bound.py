#!/usr/bin/env python3
"""
probe_s11_survival_mgf_bound.py  (#444, S11)

Now find the cleanest FORMALIZABLE inequality (sign-definite, no continuous integral) that takes a
survival ceiling N(v_j) <= B * exp(-cc * v_j) (B = A*P, cc > c) to a MGF bound Sum_b exp(c t_b) <= K*P.

CANDIDATE (the one that telescopes cleanly with sign-definite increments):
  Abel:  Sum_b exp(c t_b) = N_0*g_0 + Sum_{j>=1} N_j*(g_j - g_{j-1}),  g_j = exp(c v_j), N_0=P, v_0>=0.
  Since g_j - g_{j-1} > 0 (g increasing) and N_j <= B exp(-cc v_j):
    Sum <= P*g_0 + B * Sum_{j>=1} exp(-cc v_j)*(exp(c v_j) - exp(c v_{j-1})).
  Each increment exp(c v_j)-exp(c v_{j-1}) <= c*(v_j - v_{j-1})*exp(c v_j)  (convexity? NO, MVT gives
    = c*exp(c*xi)*(v_j-v_{j-1}) for xi in (v_{j-1},v_j) <= c exp(c v_j) (v_j-v_{j-1})).
  This is getting messy. SIMPLER provable bound (the one I'll formalize):

  *** THE CLEAN ONE: termwise survival-count domination. ***
  For NONNEG t with values <= T, and threshold count N(s)=#{t_b>=s}:
     exp(c t_b) <= 1 + (exp(c T)-1)/T * t_b ??? NO (exp not linear).

  Try the GEOMETRIC/dyadic level bound which IS clean:
  Sum_b exp(c t_b) <= sum over INTEGER levels... only if t integer.

  BEST CLEAN ROUTE that is exact + sign-definite: the "tail-sum = sum of survival over the value grid
  weighted by g-increments" but bound g-increments by the MEAN-VALUE upper estimate g'(v_j):
    exp(c v_j) - exp(c v_{j-1}) <= c (v_j - v_{j-1}) exp(c v_j).
  Then Sum_b exp(c t_b) <= P + c * Sum_{j>=1} N_j (v_j - v_{j-1}) exp(c v_j)   [using N_0 g_0 <= P + ...]
  hmm still grid-dependent.

  REFRAME: The honestly-formalizable brick is NOT a clean closed form K; it is the EXACT Abel identity
  PLUS the monotone bound  N_j <= N(threshold) used termwise. The cleanest SHARP scalar consequence,
  provable in Lean, is:
     IF for every b, exp(c t_b) <= A_b  with  Sum_b A_b <= A*P  (a per-point survival-derived ceiling),
     THEN MGFBound holds.  That's trivial. Not the content.

  THE REAL CONTENT worth formalizing (decision): the EXACT Abel/summation-by-parts identity
     Sum_b g(t_b) = N_0 g(v_0) + Sum_{j>=1} N_j (g(v_j) - g(v_{j-1}))
  for a finite spectrum, g increasing -- because THAT is the discrete layer-cake, and it lets the
  MGF be CONTROLLED BY the survival counts N_j directly (each N_j multiplies a POSITIVE increment).
  Then the monotone consequence: if N_j <= Nbound_j (any pointwise survival ceiling) then
     Sum_b g(t_b) <= N_0 g(v_0) + Sum_{j>=1} Nbound_j (g(v_j)-g(v_{j-1})).
  This is the formalizable, sign-definite, no-integral brick. Verify the monotone consequence too.
"""
import numpy as np
from sympy import primerange

def gauss_period_spectrum(p, n):
    cof = (p-1)//n
    def is_primroot(g):
        x=1; seen=set()
        for _ in range(p-1):
            x=(x*g)%p; seen.add(x)
        return len(seen)==p-1
    g=2
    while not is_primroot(g): g+=1
    h=pow(g,cof,p); H=[]; x=1
    for _ in range(n): H.append(x); x=(x*h)%p
    H=np.array(H); bs=np.arange(1,p); ang=2*np.pi/p
    eta=np.exp(1j*ang*np.outer(bs,H)).sum(axis=1)
    return (np.abs(eta)**2)/n

def abel_and_monotone(t, c):
    vals=np.sort(np.unique(np.round(t,9)))
    g=np.exp(c*vals)
    N=np.array([np.sum(t>=v-1e-9) for v in vals],dtype=float)
    P=len(t)
    direct=np.sum(np.exp(c*t))
    # exact Abel
    abel=N[0]*g[0]+np.sum(N[1:]*(g[1:]-g[:-1]))
    # monotone consequence: replace N_j by ANY ceiling >= N_j -> upper bounds direct
    # use Nbound_j = ceil to a survival-tail B exp(-cc v): pick cc=0.4,B chosen so >= N everywhere
    cc=0.4
    B=np.max(N*np.exp(cc*vals))   # smallest B making B exp(-cc v) >= N(v) for all v
    Nb=B*np.exp(-cc*vals)
    assert np.all(Nb>=N-1e-6), "ceiling must dominate"
    abel_ub=Nb[0]*g[0]+np.sum(Nb[1:]*(g[1:]-g[:-1]))
    return direct, abel, abel_ub, P, B, cc

if __name__=="__main__":
    cases=[]
    for n in [4,8,16]:
        cnt=0
        for p in primerange(max(50,n**3), n**3+5000):
            if (p-1)%n==0 and (p-1)//n>=2:
                cases.append((p,n)); cnt+=1
                if cnt>=2: break
    print("=== EXACT Abel + MONOTONE survival-ceiling upper bound ===")
    for (p,n) in cases:
        t=gauss_period_spectrum(p,n)
        for c in [0.4,0.6]:
            direct,abel,ub,P,B,cc=abel_and_monotone(t,c)
            id_ok=abs(direct-abel)/direct<1e-8
            ub_ok=ub>=direct-1e-6
            print(f"p={p:5d} n={n:3d} c={c:.2f}: direct={direct:.3f} abel={abel:.3f} ub={ub:.3f} "
                  f"B/P={B/P:.3f} cc={cc} ABEL={'OK' if id_ok else 'FAIL'} UB>=direct={'OK' if ub_ok else 'FAIL'}")
