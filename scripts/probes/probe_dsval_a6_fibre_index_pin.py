#!/usr/bin/env python3
"""
A6 FIBRE-INDEX PIN -- which symmetric function (if any) indexes the bad-gamma fibre
at the BINDING BAND, and is the binding-band incidence (=40 in all measured cases)
a closed form?

FINDINGS FROM probe_dsval_a6_symfunc_fibre.py:
  - The binding-band incidence I_bind = 40 across n=8 (4,5) w=5, n=16 (4,6) w=6,
    n=16 (8,10) w=10.  (Just above budget=n; deeper bands give I=0.)
  - At the binding band, #distinct e_1 = 1  (all consistent subsets share e_1!).
    So A6's gamma=-e_1 (Vieta) does NOT index the fibre at the binding band.
  - gamma=-e_1 IS an exact bijection only for the ADJACENT direction b=a+1 (then
    #e1 = I exactly), but that direction is not worst.

THIS PROBE pins:
 (1) WHY #e1=1 at the binding band: the consistent subsets are all translates/cosets
     with identical e_1 -- characterize them.
 (2) WHICH symmetric function e_j (or power sum p_j) actually has 40 distinct values
     = the incidence at the binding band (the true fibre index).
 (3) the closed form of I_bind=40 and how it scales: recompute the binding-band
     incidence + the indexing symmetric function for n=8,16,32 and several rho, to
     test whether I_bind is CONSTANT (=40?) or grows.  If constant -> delta* is just
     "first w with I<=n", a hard threshold; if 40 is universal that is the closed form.
"""
import itertools, cmath, math
import numpy as np
from collections import defaultdict
TAU = 2*math.pi

# exact Z[zeta_n], n=2^a
def zroot(j, n):
    half = n//2; e = j % n; v = [0]*half
    if e < half: v[e] = 1
    else: v[e-half] = -1
    return tuple(v)
def e_sym_exact(S, n, jdeg):
    """elementary symmetric e_jdeg of {zeta^s : s in S}, exact in Z[zeta_n]."""
    half = n//2
    # accumulate via polynomial product prod (1 + t*zeta^s); coeff of t^jdeg
    # represent each coeff as Z[zeta] vector
    def zadd(u, v): return tuple(a+b for a, b in zip(u, v))
    def zmul(u, v):
        res = [0]*(2*half)
        for i in range(half):
            if u[i] == 0: continue
            for j in range(half):
                res[i+j] += u[i]*v[j]
        out = [0]*half
        for d in range(2*half):
            c = res[d]
            if c == 0: continue
            dd = d % n
            if dd < half: out[dd] += c
            else: out[dd-half] -= c
        return tuple(out)
    one = tuple([1]+[0]*(half-1)); zero = tuple([0]*half)
    coeffs = [one] + [zero]*len(S)  # coeffs[j] = e_j so far
    cnt = 0
    for s in S:
        zs = zroot(s, n)
        newc = list(coeffs)
        for j in range(cnt, -1, -1):
            newc[j+1] = zadd(newc[j+1], zmul(coeffs[j], zs))
        coeffs = newc; cnt += 1
    return coeffs[jdeg] if jdeg <= len(S) else zero
def psum_exact(S, n, jdeg):
    """power sum p_jdeg = sum zeta^{s*jdeg}."""
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

def band_records(n, k, a, b, w):
    rec = []
    for S in itertools.combinations(range(n), w):
        g = consistent_gamma(n, k, a, b, S)
        if g is not None:
            rec.append((round(g.real, 4)+1j*round(g.imag, 4), S))
    return rec

def binding_band(n, k, a, b, budget):
    """Scan from LARGEST w (smallest delta) downward; the binding band is the first
    (largest-w) band with nonzero incidence. Return (w, I, records). This avoids the
    huge deep (small-w) bands entirely."""
    for w in range(n-1, k, -1):
        rec = band_records(n, k, a, b, w)
        I = len(set(r[0] for r in rec))
        if I > 0:
            return (w, I, rec)
    return None

def index_test(rec, n):
    """For each symmetric function e_1..e_5 and power sum p_1..p_5, count #distinct
    values over consistent subsets, and whether it is in bijection with gamma."""
    out = {}
    gammas = [r[0] for r in rec]
    for kind, fn in [("e", e_sym_exact), ("p", psum_exact)]:
        for j in range(1, 6):
            vmap = defaultdict(set)
            for gr, S in rec:
                v = fn(S, n, j)
                vmap[v].add(gr)
            nd = len(vmap)
            bij = all(len(s) == 1 for s in vmap.values()) and nd == len(set(gammas))
            out[f"{kind}{j}"] = (nd, bij)
    return out

def main():
    print("="*84)
    print("A6 FIBRE-INDEX PIN: binding-band incidence + true indexing symmetric function")
    print("="*84)
    cases = [(8,2,4,7),(8,4,4,5),(16,4,4,6),(16,8,8,10)]
    for (n,k,a,b) in cases:
        bb = binding_band(n,k,a,b,budget=n)
        if bb is None:
            print(f"n={n} k={k} dir({a},{b}): no nonzero binding band"); continue
        w,I,rec = bb
        idx = index_test(rec, n)
        ng = len(set(r[0] for r in rec))
        print(f"\nn={n} k={k} rho={k/n} dir=({a},{b}) BINDING w={w} delta={1-w/n:.3f} "
              f"I={I} (#gamma={ng}, consistent={len(rec)})")
        print("   symfunc #distinct (bij-with-gamma):")
        for key in ["e1","e2","e3","e4","e5","p1","p2","p3","p4","p5"]:
            nd,bij = idx[key]
            star = " <== BIJECTION (indexes fibre)" if bij else ""
            print(f"      {key}: {nd}{star}")
        # closed-form candidates for I:
        print(f"   I={I} candidates: n/4-1={n//4-1}, n/2={n//2}, n={n}, "
              f"5n={5*n}, 5*n/2={5*n//2}, binom(b-k+1,?)")
    # universality of I_bind: sweep more (n=32 rho=1/4, worst-ish dirs)
    print("\n" + "="*84)
    print("I_bind SCALING (is binding-band incidence constant or growing?)")
    print("="*84)
    # n=32 brute is infeasible; report binding-band incidence at the KNOWN worst dirs.
    known = [(8,2,4,7),(8,4,4,5),(16,4,4,6),(16,8,8,10)]
    for (n,k,a,b) in known:
        bb=binding_band(n,k,a,b,n)
        if bb is None: continue
        w,I,rec=bb
        print(f"  n={n} k={k} rho={k/n}: worst dir=({a},{b}) binding w={w} "
              f"delta*={1-w/n:.4f} I_bind={I}  [I==40? {I==40}]")
    print("\nDONE")

if __name__=="__main__":
    main()
