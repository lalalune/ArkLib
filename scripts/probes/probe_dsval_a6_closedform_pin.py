#!/usr/bin/env python3
"""
A6 CLOSED-FORM PIN -- the binding-band fibre count.

ESTABLISHED (probe_dsval_a6_fibre_index_pin.py):
  At the worst-direction binding band, w = b (agreement = top exponent), and
  the bad scalar gamma is in BIJECTION with the symmetric function of degree
  step = b-a:  step=1 -> e_1=p_1;  step=2 -> e_2=p_2 (with p_1 collapsed).
  Binding-band incidence I_bind = 40 for (8,4,4,5),(16,4,4,6),(16,8,8,10);
  consistent count = 56 = C(8,3) in all three; n=8,k=2 dir(4,7) gives I=9, cons=10=C(5,2).

GOAL: pin the closed forms of
  (C) #consistent subsets at binding band, and
  (I) #distinct gamma (= the fibre count = incidence).
as functions of (n,k,a,b). Then deduce delta* = 1 - b/n (since w=b at the band)
or the next-crossing form.

METHOD: characterize the consistent w-subsets structurally (which S?), count them,
and count distinct p_{step}(S). Test closed-form hypotheses:
  H_cons: #consistent = C(n/d, (w-?)/?) for d=gcd(b-a,n) etc.
  H_I:    I = #distinct p_step(S) over consistent S.
We compute EXACTLY over Z[zeta_n] and report the structural description.
"""
import itertools, cmath, math
import numpy as np
from collections import defaultdict, Counter
from math import comb, gcd
TAU = 2*math.pi

def zroot(j, n):
    half = n//2; e = j % n; v = [0]*half
    if e < half: v[e] = 1
    else: v[e-half] = -1
    return tuple(v)
def psum_exact(S, n, jdeg):
    half = n//2; acc = [0]*half
    for s in S:
        r = zroot((s*jdeg) % n, n)
        for i in range(half): acc[i] += r[i]
    return tuple(acc)

def consistent_gamma(n, k, a, b, S):
    xs = [cmath.exp(1j*TAU*s/n) for s in S]
    V = np.array([[x**c for c in range(k)] for x in xs], dtype=complex)
    va = np.array([x**a for x in xs], dtype=complex)
    vb = np.array([x**b for x in xs], dtype=complex)
    Vp = np.linalg.pinv(V)
    ra = va - V@(Vp@va); rb = vb - V@(Vp@vb)
    na = np.linalg.norm(ra); nb = np.linalg.norm(rb)
    if nb < 1e-9: return None
    if na < 1e-9: return 0j
    lam = np.vdot(rb, ra)/np.vdot(rb, rb)
    if np.linalg.norm(ra - lam*rb) < 1e-6*na: return -lam
    return None

def analyze_band(n, k, a, b, w):
    step = b-a
    rec = []
    for S in itertools.combinations(range(n), w):
        g = consistent_gamma(n, k, a, b, S)
        if g is not None:
            rec.append((round(g.real,4)+1j*round(g.imag,4), S))
    cons = len(rec)
    I = len(set(r[0] for r in rec))
    # structural: how do consistent S look? complement structure, coset content
    subsets = [r[1] for r in rec]
    # distinct p_step
    pstep = defaultdict(list)
    for gr,S in rec: pstep[psum_exact(S,n,step)].append((gr,S))
    n_pstep = len(pstep)
    # gamma orbit under dilation gamma -> gamma * zeta^step (the action-orbit)
    # (incidence is action-orbit count times orbit size, per #400/#407)
    return cons, I, n_pstep, subsets

def structural_desc(subsets, n, k, a, b, w):
    """Describe consistent subsets: are they 'k free points + a step-coset'?
    Check: each S = (a (k)-subset) plus a structured remainder. Report complement
    distribution and whether S always contains a full mu_d coset (d=n/gcd(step,n))."""
    step=b-a; d=n//gcd(step,n)
    # does each S contain a coset of the order-(n/gcd) subgroup? coset = {r+s*gcd...}
    g=gcd(step,n); sub=[(i*g)%n for i in range(n//g)]  # subgroup gen by step
    contains_coset=0
    for S in subsets:
        Sset=set(S); found=False
        for r in range(g):
            coset=set((r+x)%n for x in sub)
            if coset<=Sset: found=True; break
        if found: contains_coset+=1
    return d, g, contains_coset, len(subsets)

def main():
    print("="*84)
    print("A6 CLOSED-FORM PIN: binding-band consistent count + fibre (incidence)")
    print("="*84)
    cases = [(8,2,4,7,4),(8,4,4,5,5),(16,4,4,6,6),(16,8,8,10,10),
             (8,4,4,6,6),(8,4,5,6,6),(16,4,4,5,5),(16,4,4,8,8),
             (16,8,8,9,9),(16,8,8,12,12),(16,4,6,8,8)]
    rows=[]
    for (n,k,a,b,w) in cases:
        if w>=n or w<=k: continue
        cons,I,npstep,subs = analyze_band(n,k,a,b,w)
        if cons==0:
            print(f"n={n} k={k} ({a},{b}) w={w}: empty"); continue
        d,g,cc,tot = structural_desc(subs,n,k,a,b,w)
        step=b-a
        # closed-form candidates
        cf_cons = {
            "C(n/2, w-k)": comb(n//2, w-k) if w-k<=n//2 else -1,
            "C(n/2, k)": comb(n//2, k),
            "C(n-?, ?)": -1,
        }
        print(f"\nn={n} k={k} dir=({a},{b}) step={step} w={w}={'=b' if w==b else ''} "
              f"delta=1-w/n={1-w/n:.3f}")
        print(f"   #consistent={cons}  #incidence(I)={I}  #distinct p_step={npstep}  "
              f"(I==p_step? {I==npstep})")
        print(f"   contains step-subgroup-coset: {cc}/{tot}; gcd(step,n)={g} order={d}")
        for name,v in cf_cons.items():
            if v==cons: print(f"   >> #consistent == {name} = {v}")
        rows.append((n,k,a,b,step,w,cons,I))
    print("\n" + "="*84)
    print("TABLE: (n,k,a,b,step,w,cons,I)  -- hunt closed form")
    print("="*84)
    print(f"  {'n':>3}{'k':>3}{'a':>3}{'b':>3}{'st':>3}{'w':>3}{'cons':>6}{'I':>5}"
          f"{'  cons-form':>22}{'  I-form':>16}")
    for (n,k,a,b,step,w,cons,I) in rows:
        # guesses
        cform=""
        for name,v in [("C(n/2,k)",comb(n//2,k)),("C(n/2,w-k)",comb(n//2,w-k) if 0<=w-k<=n//2 else -1),
                       ("C(b,k)",comb(b,k) if k<=b else -1),("C(n-a-1,?)",-1)]:
            if v==cons: cform=name; break
        iform=""
        # I vs cons ratio
        r=I/cons if cons else 0
        iform=f"I/cons={r:.3f}"
        print(f"  {n:>3}{k:>3}{a:>3}{b:>3}{step:>3}{w:>3}{cons:>6}{I:>5}{cform:>22}{iform:>16}")
    print("\nDONE")

if __name__=="__main__":
    main()
