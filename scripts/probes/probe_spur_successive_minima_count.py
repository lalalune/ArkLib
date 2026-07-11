#!/usr/bin/env python3
"""
probe_spur_successive_minima_count.py  (#444, lane wf-W6 frontier-movement)

PROBE-FIRST for the candidate brick: replace the INSUFFICIENT first-minimum gap
`(G-W6)  φ(n)·2r < λ₁²  ⟹  Spur=0`
with the SUCCESSIVE-MINIMA POINT-COUNT frame
`Spur_r ≤ #{v∈L_p\\{0} : ‖v‖²≤φ(n)·2r} ≤ ∏_i (1 + 2R/λ_i(L_p)) - 1,  R=√(φ(n)·2r).`

The lattice L_p = ker(ev_h: ℤ[ζ_n] ↠ F_p) in the cyclotomic TRACE form, an index-p
sublattice of the trace lattice of ℤ[ζ_n], n=2^m, d=φ(n)=n/2, det = p (p splits completely).

QUESTIONS (probe-first, NEVER n=q-1, proper μ_n, prize primes p≍n^4, p≡1 mod n):
 Q1. Are the successive minima λ_1..λ_d(L_p) clustered near p^{1/d} (so the point-count frame is
     NON-VACUOUS), or are there tiny minima making it blow up?
 Q2. Does the successive-minima product bound  ∏(1+2R/λ_i)-1  actually UPPER-BOUND the true
     spurious count #{v≠0:‖v‖≤R} at the relevant radii?  (sanity: it MUST, classically — verify.)
 Q3. At the PRIZE depth r* ≈ ln(q)/2 where the first-minimum gap FAILS, is the product-count bound
     still finite/useful, or does it already exceed the Wick ceiling (i.e. is even the count frame
     insufficient — an honest wall)?

We compute L_p via the power-basis embedding and the trace (Minkowski) inner product, get the
Gram matrix, and read successive minima by exact short-vector enumeration at small d, plus the
LLL-reduced Gram-Schmidt norms as a successive-minima proxy at larger d.
"""
import numpy as np
import itertools, math
from sympy import isprime, totient

def primitive_root_mod_p(n, p):
    # find h of multiplicative order exactly n in F_p (n | p-1)
    g = None
    for cand in range(2, p):
        # order of cand
        o = 1; x = cand % p
        while x != 1:
            x = (x*cand) % p; o += 1
            if o > p: break
        if o == p-1:
            g = cand; break
    if g is None:
        return None
    h = pow(g, (p-1)//n, p)
    return h

def trace_lattice_basis(n):
    """Power basis 1,ζ,...,ζ^{d-1}, d=φ(n)=n/2 for n=2^m. Trace form Gram:
    Tr(ζ^a · conj(ζ^b)) over Q(ζ_n)/Q. For 2-power cyclotomic the trace lattice
    of ℤ[ζ_n] in the power basis has Gram = φ(n)·I in the *embedding* (NT2 identity:
    ‖Σ ε_i ζ^{a_i}‖² = φ(n)·(#terms) when a_i distinct). We use the canonical complex
    embedding and take the real 2d-dim vector, but exploit NT2: in the power basis
    reduced by ζ^d=-1, the Gram is φ(n)*Identity on Z^d. So L (full lattice) = √φ(n)·Z^d
    geometrically; weight-w signed configs are vectors of squared length φ(n)·w."""
    d = n//2
    return d  # Gram = d * I_d   (d = φ(n) for n=2^m)

def Lp_kernel_basis(n, p, h):
    """L_p = {c ∈ Z^d : Σ c_k h^k ≡ 0 mod p}, index-p sublattice of Z^d (power basis,
    reduced via ζ^d=-1 so coefficient k from exponent j is at index j mod d with sign
    (-1)^{j div d}). We return an integer basis (d x d) of L_p as rows. Geometric Gram
    of L_p in trace form = d * (B Bᵀ) where B is the Z^d-basis (since trace Gram on Z^d is d·I)."""
    d = n//2
    # residues r_k = h^k mod p for k=0..d-1  (these are the images of basis e_k under ev_h)
    res = [pow(h, k, p) for k in range(d)]
    # L_p = ker of the map Z^d -> Z_p, e_k |-> res[k]. HNF basis:
    # vectors p*e_0, and e_k - (res[k]*inv(res[0]))*e_0 for k>=1, assuming res[0]=1 (h^0=1). 
    inv0 = 1  # res[0] = h^0 = 1
    basis = []
    # p * e_0
    v = [0]*d; v[0] = p; basis.append(v)
    for k in range(1, d):
        v = [0]*d
        v[k] = 1
        v[0] = (-res[k]) % p   # so res[k]*1 + (-res[k])*1 = 0 mod p
        # keep small: center
        if v[0] > p//2: v[0] -= p
        basis.append(v)
    return np.array(basis, dtype=float), d

def gram_schmidt_norms(B, d):
    """LLL-ish: just GS norms of B (rows) under trace Gram = d*I, i.e. ordinary
    Euclidean times d. Returns sorted GS squared-norms * d as successive-minima proxy."""
    # reduce B by LLL first for a real successive-minima proxy
    from numpy.linalg import qr
    Bred = lll_reduce(B.copy())
    # GS
    Q, R = np.linalg.qr(Bred.T)
    gs2 = np.array([R[i,i]**2 for i in range(R.shape[0])])
    gs2 = np.sort(np.abs(gs2)) * d   # trace form scales by d
    return gs2, Bred

def lll_reduce(B, delta=0.75):
    B = B.astype(float).copy()
    n = B.shape[0]
    def gs(B):
        Bs = B.copy(); mu = np.zeros((n,n))
        for i in range(n):
            for j in range(i):
                mu[i,j] = np.dot(B[i], Bs[j])/np.dot(Bs[j],Bs[j])
                Bs[i] = Bs[i] - mu[i,j]*Bs[j]
        return Bs, mu
    Bs, mu = gs(B)
    k = 1
    it = 0
    while k < n and it < 10000:
        it += 1
        for j in range(k-1, -1, -1):
            if abs(mu[k,j]) > 0.5:
                B[k] = B[k] - round(mu[k,j])*B[j]
                Bs, mu = gs(B)
        if np.dot(Bs[k],Bs[k]) >= (delta - mu[k,k-1]**2)*np.dot(Bs[k-1],Bs[k-1]):
            k += 1
        else:
            B[[k,k-1]] = B[[k-1,k]]
            Bs, mu = gs(B)
            k = max(k-1,1)
    return B

def enumerate_short_count(B, d, R2_over_d):
    """Exact count of nonzero L_p vectors with trace-sq-norm <= d*R2_over_d, i.e.
    Euclidean-sq <= R2_over_d, by bounded enumeration. R2_over_d is in Z^d Euclidean units.
    Only feasible for small d (<=8). Returns count or None."""
    if d > 8: return None
    Bred = lll_reduce(B.copy())
    # enumerate integer combos with bounded coords; use box from R2
    R = math.sqrt(R2_over_d)
    # crude bound on combo range via reduced basis shortest GS
    Q,Rm = np.linalg.qr(Bred.T)
    gs2 = np.array([Rm[i,i]**2 for i in range(d)])
    lim = [int(R/math.sqrt(max(gs2[i],1e-9)))+1 for i in range(d)]
    cap = 1
    for l in lim: cap *= (2*l+1)
    if cap > 6_000_000: return None
    cnt = 0
    ranges = [range(-l, l+1) for l in lim]
    for combo in itertools.product(*ranges):
        if all(c==0 for c in combo): continue
        v = np.zeros(d)
        for i,c in enumerate(combo):
            if c: v += c*Bred[i]
        if np.dot(v,v) <= R2_over_d + 1e-6:
            cnt += 1
    return cnt

print("="*78)
print("PROBE: successive-minima point-count frame for the spurious count Spur_r(p)")
print("L_p = index-p sublattice of trace lattice of Z[ζ_n], n=2^m, d=φ(n)=n/2, det=p")
print("Frame:  Spur_r ≤ #{v≠0:‖v‖²≤d·2r} ≤ ∏_i(1+2R/λ_i)-1,  R=√(d·2r) (trace units)")
print("="*78)

# prize-shaped primes p ≍ n^4, p ≡ 1 mod n
def find_prime(n, beta=4):
    target = n**beta
    p = target - (target % n) + 1
    for _ in range(200000):
        if p > target//2 and isprime(p) and (p-1)%n==0:
            return p
        p += n
    return None

for m in [3,4,5]:           # n = 8,16,32
    n = 2**m; d = n//2
    p = find_prime(n,4)
    h = primitive_root_mod_p(n,p)
    if h is None or pow(h,n,p)!=1:
        print(f"n={n}: no valid h"); continue
    B, dd = Lp_kernel_basis(n,p,h)
    gs2, Bred = gram_schmidt_norms(B,d)
    lam1_proxy = gs2[0]; lamd_proxy = gs2[-1]
    pinv_d = p**(1.0/d)
    print(f"\n--- n={n}, d={d}, p={p} (β≈{math.log(p,n):.2f}), h={h} ---")
    print(f"  p^(1/d) = {pinv_d:.3f}   (expected λ_i scale in EUCLIDEAN Z^d units)")
    print(f"  LLL GS successive-minima² (trace units, =d·euclid²):")
    print(f"    λ_1²≈{gs2[0]:.2f}  λ_2²≈{gs2[1]:.2f} ... λ_d²≈{gs2[-1]:.2f}")
    print(f"    ratio λ_d/λ_1 ≈ {math.sqrt(lamd_proxy/lam1_proxy):.3f}  (clustered if ~O(1)..O(√d))")
    print(f"    geo-mean λ_i (euclid) ≈ {math.exp(np.mean(np.log(np.sqrt(gs2/d)))):.3f}  vs p^(1/d)={pinv_d:.3f}")
    # Q2/Q3: at depths r, compare true short-count vs product bound vs Wick
    for r in [2,3,4,5,6]:
        R2_trace = d*2*r           # ‖v‖²≤φ(n)·2r
        R = math.sqrt(R2_trace)
        # product successive-minima bound (Euclidean: λ_i in same trace units)
        prod = 1.0
        for li2 in gs2:
            prod *= (1 + 2*R/math.sqrt(li2))
        prodbound = prod - 1
        wick = math.factorial(2*r)/(2**r*math.factorial(r)) * n**r  # (2r-1)!! n^r
        true_cnt = enumerate_short_count(B,d, 2*r)  # euclid-sq <= 2r
        tc = f"{true_cnt}" if true_cnt is not None else "n/a(d>8 or cap)"
        tag = ""
        if true_cnt is not None:
            tag = "OK(bound≥true)" if prodbound>=true_cnt-1e-6 else "!!BOUND<TRUE!!"
        print(f"    r={r}: R²={R2_trace}  true#={tc}  ∏-bound≈{prodbound:.3g}  Wick≈{wick:.3g}  "
              f"∏/Wick≈{prodbound/wick:.3g}  {tag}")
print("\nVERDICT printed above: read clustering (Q1), bound-validity (Q2), prize-depth usefulness (Q3).")
