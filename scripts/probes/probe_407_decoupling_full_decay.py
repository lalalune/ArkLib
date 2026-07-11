#!/usr/bin/env python3
"""
DECOUPLING decay law: FULL max-over-directions I(s) profile (the complete decay curve).

Reuses the (k+1)-subset candidate-gen engine (probe_407_regimeB_sstar_np: fast, no C(n,s) blowup)
but prints the ENTIRE I(thr) profile thr=k+1..n (not just the band near n/2). This is the raw
decay curve I need to derive the general decay law I(c), c=s-k, and locate the budget crossing.

rho=1/4 axis (k=n/4) = the prize axis. Multi-prime (p-independence). PROPER mu_n, p>>n^3, NEVER n=q-1.
"""
import sys, itertools
from math import gcd, sqrt
import numpy as np
sys.path.insert(0, '/tmp/ArkLib/scripts/probes')
from probe_407_regimeB_sstar_np import (prime_ge, find_gen, alpha_for_subset,
                                        precompute_lagrange, max_agree_vec)

def full_profile(n, k, mult):
    budget = n
    p = prime_ge(mult * n**3, n)
    w = find_gen(p, n)
    X = [pow(w, j, p) for j in range(n)]
    m_index = (p-1)//n
    assert m_index > 1
    lagr = precompute_lagrange(n, k, p, X)
    per_thr = {}
    b = k
    seen_gcd = {}
    for a in range(k, n):
        if a == b: continue
        d = gcd((b-a) % n, n)
        if d not in seen_gcd: seen_gcd[d] = a
    Xl = [int(x) for x in X]
    for d, a in sorted(seen_gcd.items()):
        cand = set()
        for Tidx in itertools.combinations(range(n), k+1):
            al = alpha_for_subset([Xl[j] for j in Tidx], a, b, p, k)
            if al is not None: cand.add(al)
        if not cand: continue
        Xa = np.array([pow(int(x), a, p) for x in X], dtype=np.int64)
        Xb = np.array([pow(int(x), b, p) for x in X], dtype=np.int64)
        calp = np.array(list(cand), dtype=np.int64).reshape(-1,1)
        y_mat = (Xa.reshape(1,-1) + (calp * Xb.reshape(1,-1)) % p) % p
        agrs = max_agree_vec(y_mat, lagr, p)
        for thr in range(k+1, n+1):
            I = int((agrs >= thr).sum())
            cur = per_thr.get(thr)
            if cur is None or I > cur[0]: per_thr[thr] = (I, (a,b,d))
    return p, m_index, per_thr

if __name__=='__main__':
    print("=== FULL max-over-dir I(s) decay profile, rho=1/4 axis ===", flush=True)
    allprof={}
    for n in [8,12,16,20,24]:
        if n%4: continue
        k=n//4; budget=n
        profs={}
        for mult in [8]:
            p,mi,pt = full_profile(n,k,mult)
            profs[mult]=(p,pt)
        # p-independence over over-det band
        (p0,pt0),(p1,pt1)=profs[8],profs[8]
        m=n//4; peak=2*m**3-2*m**2+1
        print(f"\nn={n} k={k} m={m} budget={budget} Johnson_thr~{sqrt(0.25)*n:.1f} (p={p0},{p1}):",flush=True)
        allprof[n]=(k,pt0)
        sstar=None
        for thr in range(k+1, n+1):
            I0=pt0.get(thr,(0,None))[0]; I1=pt1.get(thr,(0,None))[0]
            c=thr-k
            pind = "OK" if I0==I1 else f"P-DEP({I1})"
            flag=""
            if I0<=budget and sstar is None: sstar=thr; flag=f" <== s*=k+{c}"
            note=""
            if c==2: note=f"  [cubic-peak 2m^3-2m^2+1={peak} {'HIT' if I0==peak else 'miss'}]"
            if I0>0 or c<=k:  # show whole over-det band + a bit
                print(f"   c={c} (s={thr}, r={n-thr}): I={I0} [{pind}]{flag}{note}",flush=True)
            if I0==0 and c>2: break
        if sstar:
            print(f"  => s*={sstar} c*={sstar-k} delta*=(n-s*)/n={(n-sstar)/n:.4f}",flush=True)
    print("\n=== DECAY-LAW table: I(c) for c=1,2,3,4 (max over dirs) ===",flush=True)
    for n,(k,pt) in sorted(allprof.items()):
        row=[pt.get(k+c,(0,None))[0] for c in [1,2,3,4,5]]
        print(f"n={n:>3} k={k}: I(c=1..5)={row}",flush=True)
    print("DONE",flush=True)
