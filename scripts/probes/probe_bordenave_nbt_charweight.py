#!/usr/bin/env python3
"""
probe_bordenave_nbt_charweight.py  (I037 — Bordenave non-backtracking trace on the
                                     CHARACTER-WEIGHTED period multigraph)

THE IDEA (I037).  M(mu_n) = max_{b!=0}|eta_b|, eta_b = sum_{u in mu_n} e_p(b u), is the
non-principal spectral radius of the n-regular Cayley graph Cay(F_p, mu_n) (adjacency
A_{xy}=1 iff x-y in mu_n). For a d-REGULAR graph the Hashimoto non-backtracking operator B
obeys Ihara-Bass: every B-eigenvalue mu solves mu^2 - lambda*mu + (d-1) = 0 for an adjacency
eigenvalue lambda. So rho(B) ~ sqrt(d-1)=sqrt(n-1) <=> |lambda_2|<=2 sqrt(n-1) <=> M<=2 sqrt n.
=> for the BARE regular graph, NBT radius is EQUIVALENT to the target, gives nothing new.

I037's twist: attach a NON-CONSTANT edge weight w(x,y)=chi(x/y) (chi a multiplicative char of
F_p^*) to make the graph IRREGULAR, hoping rho(B) decouples from any single eta_b and Bordenave's
tangle-free Catalan trace forces rho(B)<=2 sqrt(n), recovering M<=2 sqrt(n)+tail via
rho(A) <= rho(B)+1/rho(B).

THIS PROBE TESTS THE THREE LOAD-BEARING CLAIMS, EXACTLY, on proper mu_n (p prime, n|p-1,
p >> n^3, n=2^mu, m=(p-1)/n>1, NEVER n=p-1):

  CLAIM-A (Ihara-Bass / regular baseline): for the UNWEIGHTED graph, does rho(B) relate to M as
     the pairing predicts? (sanity: confirm the equivalence is exact, so no free lunch there.)

  CLAIM-B (the actual lever): build the CHARACTER-WEIGHTED Hashimoto B_chi on the directed edges,
     B_chi[(x->y),(y->z)] = w(y,z) * [x != z]  (non-backtracking), w(y,z)=chi((z-y)) i.e. the
     character of the STEP z-y in mu_n... but the step is always in mu_n. The faithful weight that
     ties to M is the ADDITIVE character twist: we instead study the WEIGHTED ADJACENCY
        A_chi[x,y] = chi(x-y)  for x-y in mu_n   (chi a multiplicative character of F_p^*)
     whose eigenvalues are the TWISTED Gauss periods eta_b^chi = sum_{u in mu_n} chi(u) e_p(b u).
     Measure rho(A_chi) and M_chi := max_b |eta_b^chi|. Does the multiplicative twist chi help
     (push the spectral radius toward sqrt(n))? If max over chi of M_chi still ~ M, weighting the
     SAME group fails. KEY HONEST GATE: rho of the weighted operator must still be COMPUTED, not
     assumed = sqrt(n).

  CLAIM-C (Bordenave Catalan vs Wick — the heart): the moment-ladder cap at Johnson comes from
     E[tr A^{2k}] being counted by Wick (2k-1)!! pairings (the L2-energy moment route). Bordenave's
     NBT trace replaces (2k-1)!! by Catalan C_k. We DIRECTLY measure, for the weighted NBT operator,
        T_k := tr(B_chi^{2k}) / (q * n^k)
     and compare to Catalan C_k and to Wick (2k-1)!!. If T_k <= C_k (Catalan) robustly while the
     adjacency moments track Wick, the Catalan suppression is REAL and rho(B_chi) <= 2 sqrt(n) would
     follow. If T_k tracks Wick (or worse, blows up), the Catalan claim is false for this graph.

DECISIVE: does rho(B_chi) (hence the recovered M-bound 2 sqrt(n)+tail) come out BELOW M(mu_n)
itself? If rho(B_chi)+1/rho(B_chi) >= M for the worst chi (no chi beats the unweighted bound),
the lever gives no gain. If the NBT radius is genuinely ~2 sqrt(n) << M while still upper-bounding
M, that's a real handle.

HONESTY: exact eigenvalues via numpy on the FULL p x p (or 2|E| x 2|E|) operator for feasible p.
Feasible only for small p, so we use the SMALLEST proper regime p >> n^3 we can diagonalize
(p up to ~few thousand => n up to 8, m=(p-1)/n>1). Cross-check M against the direct period sum.
"""
import math, cmath, itertools
import numpy as np

def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    if x % 3 == 0: return x == 3
    d = 5
    while d*d <= x:
        if x % d == 0 or x % (d+2) == 0: return False
        d += 6
    return True

def find_p(n, beta_min=3.0):
    """smallest prime p with n | p-1, p > n^beta_min, m=(p-1)/n>1 (proper, never n=p-1)."""
    target = int(n ** beta_min) + 1
    p = ((target // n) + 1) * n + 1
    while True:
        if is_prime(p) and (p - 1) % n == 0 and (p - 1) // n > 1:
            return p
        p += n

def primitive_root(p):
    fac = []
    m = p - 1
    d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fac):
            return g
    raise RuntimeError("no primitive root")

def subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    H = [pow(h, i, p) for i in range(n)]
    return g, set(H), H

def gauss_period(p, n, Hlist, b, mchar=None, g=None):
    """eta_b^chi = sum_{u in mu_n} chi(u) e_p(b u).  mchar: index of multiplicative char (None=trivial)."""
    w = 2 * math.pi / p
    s = 0+0j
    if mchar is None:
        for u in Hlist:
            s += cmath.exp(1j * w * ((b * u) % p))
    else:
        # chi(g^k) = exp(2 pi i mchar k / (p-1)); express u as power of g via discrete log on the subgroup
        # u = h^j = g^{(p-1)/n * j}; chi(u) = exp(2 pi i mchar (p-1)/n j /(p-1)) = exp(2 pi i mchar j / n)
        for j, u in enumerate(Hlist):
            chi = cmath.exp(2j * math.pi * mchar * j / n)
            s += chi * cmath.exp(1j * w * ((b * u) % p))
    return s

def M_of_periods(p, n, Hlist, mchar=None, g=None):
    """max_{b!=0} |eta_b^chi|, computed over ONE rep per mu_n-coset (|S_b| is mu_n-coset invariant
    for the unweighted; for twisted it is also coset-invariant up to a phase, so |.| is invariant)."""
    best = 0.0
    seen = bytearray(p)
    Hset = set(Hlist)
    for b in range(1, p):
        if seen[b]: continue
        for u in Hlist:
            seen[(b * u) % p] = 1
        val = abs(gauss_period(p, n, Hlist, b, mchar, g))
        if val > best: best = val
    return best

def build_nbt(p, Hset, weightfn):
    """Hashimoto non-backtracking operator on Cay(F_p, Hset).
    Directed edges e=(x,y) with x-y in Hset. B[e=(x,y), f=(u,v)] = weightfn(u,v) if y==u and v!=x.
    Returns dense complex matrix (2|E| x 2|E|) and the edge list."""
    edges = []
    for x in range(p):
        for s in Hset:
            y = (x - s) % p   # x - y = s in Hset
            edges.append((x, y))
    idx = {e: i for i, e in enumerate(edges)}
    E = len(edges)
    B = np.zeros((E, E), dtype=complex)
    # group edges by head 'y' for speed
    from collections import defaultdict
    by_tail = defaultdict(list)  # edges leaving a vertex u
    for j, (u, v) in enumerate(edges):
        by_tail[u].append(j)
    for i, (x, y) in enumerate(edges):
        for j in by_tail[y]:
            u, v = edges[j]   # u==y
            if v != x:        # non-backtracking
                B[i, j] = weightfn(u, v)
    return B, edges

def spectral_radius(M):
    ev = np.linalg.eigvals(M)
    return max(abs(ev)), ev

def catalan(k):
    return math.comb(2*k, k) // (k + 1)

def wick(k):  # (2k-1)!!
    r = 1
    for i in range(1, 2*k, 2):
        r *= i
    return r

def run(n, beta_min, max_k=4, do_nbt=True):
    p = find_p(n, beta_min)
    g, Hset, Hlist = subgroup(p, n)
    m = (p - 1) // n
    print(f"\n=== n={n}  p={p}  m=(p-1)/n={m}  beta=log_n(p)={math.log(p)/math.log(n):.2f}  E=p*n={p*n} ===")
    assert m > 1 and p > n, "must be proper subgroup"
    # --- M (unweighted) and twisted M over all multiplicative chars on mu_n ---
    M0 = M_of_periods(p, n, Hlist, mchar=None)
    sqrtn = math.sqrt(n)
    print(f"  M(mu_n) unweighted   = {M0:.4f}   (sqrt n={sqrtn:.4f}, 2sqrt(n-1)={2*math.sqrt(n-1):.4f}, n={n})")
    Mtw = []
    for c in range(n):   # multiplicative characters of mu_n are indexed 0..n-1
        Mtw.append(M_of_periods(p, n, Hlist, mchar=c))
    worst_tw = max(Mtw)
    best_tw = min(m for m in Mtw)
    print(f"  M_chi twisted: min over chi = {best_tw:.4f}, max over chi = {worst_tw:.4f}")
    print(f"     -> does ANY multiplicative twist push M below the unweighted M? best_tw < M0 ? {best_tw < M0 - 1e-9}")

    if not do_nbt:
        return dict(n=n, p=p, m=m, M0=M0, sqrtn=sqrtn, best_tw=best_tw, worst_tw=worst_tw)

    # --- NBT operator, unweighted (CLAIM-A baseline) and char-weighted (CLAIM-B/C) ---
    # weight w(u,v) = chi(u - v)?  step u-v in mu_n. Use the multiplicative char of the STEP.
    # chi_step(s) = exp(2 pi i * c0 * dlog_h(s) / n).  Pick c0=1 (first nontrivial step-char).
    # precompute dlog on the subgroup
    dlog = {s: j for j, s in enumerate(Hlist)}
    def w_unweighted(u, v): return 1.0
    def make_w_charstep(c0):
        def w(u, v):
            s = (u - v) % p
            return cmath.exp(2j * math.pi * c0 * dlog[s] / n)
        return w

    B0, edges = build_nbt(p, Hset, w_unweighted)
    rhoB0, _ = spectral_radius(B0)
    print(f"  rho(B) unweighted    = {rhoB0:.4f}   (sqrt(n-1)={math.sqrt(n-1):.4f}, predicted recovery rho+1/rho={rhoB0+1/rhoB0:.4f} vs M0={M0:.4f})")

    # char-weighted NBT: sweep nontrivial step-characters, report the one that MINIMIZES rho(B_chi)
    best_rho = None; best_c = None
    for c0 in range(1, n):
        Bc = build_nbt(p, Hset, make_w_charstep(c0))[0]
        r, _ = spectral_radius(Bc)
        if best_rho is None or r < best_rho:
            best_rho, best_c = r, c0
    print(f"  rho(B_chi) char-weighted: best over step-char c0 = {best_rho:.4f} (c0={best_c}); recovered M-bound rho+1/rho = {best_rho + 1/best_rho:.4f}")
    print(f"     -> char-weighted NBT recovers M <= {best_rho + 1/best_rho:.4f}; ACTUAL M0={M0:.4f}. Beats it? {best_rho + 1/best_rho < M0 - 1e-9}")

    # --- CLAIM-C: trace moments, Catalan vs Wick ---
    # adjacency moments (Wick expectation) vs NBT moments (Catalan claim)
    A = np.zeros((p, p), dtype=complex)
    for x in range(p):
        for s in Hset:
            A[x, (x - s) % p] = 1.0
    print(f"  trace moment ladder   T_k^A = tr(A^{{2k}})/(p n^k),  T_k^B = tr(B_chi^{{2k}})/(p n^k):")
    Bc_best = build_nbt(p, Hset, make_w_charstep(best_c))[0]
    Apow = np.eye(p, dtype=complex)
    Bpow = np.eye(Bc_best.shape[0], dtype=complex)
    A2 = A @ A
    B2 = Bc_best @ Bc_best
    for k in range(1, max_k + 1):
        Apow = Apow @ A2
        Bpow = Bpow @ B2
        TkA = abs(np.trace(Apow).real) / (p * n**k)
        TkB = abs(np.trace(Bpow).real) / (p * n**k)
        print(f"     k={k}: T_k^A={TkA:8.4f}  T_k^B={TkB:8.4f}   Catalan C_k={catalan(k):6d}  Wick(2k-1)!!={wick(k):8d}")

    return dict(n=n, p=p, m=m, M0=M0, sqrtn=sqrtn, best_tw=best_tw, worst_tw=worst_tw,
                rhoB0=rhoB0, best_rho=best_rho, recovered=best_rho + 1/best_rho)

if __name__ == "__main__":
    print("I037 Bordenave non-backtracking / character-weighted period-multigraph probe")
    print("Proper mu_n (n=2^mu, n|p-1, p prime, m>1, p>>n^3). Exact dense eigenvalues.")
    results = []
    # n=4: p>64 proper; n=8: p>512 proper. NBT operator is (p*n) x (p*n): keep p*n <= ~3500 for dense eig.
    for n in [4, 8]:
        beta = 3.0
        # cap NBT to feasible sizes
        p = find_p(n, beta)
        do_nbt = (p * n <= 4000)
        results.append(run(n, beta, max_k=4, do_nbt=do_nbt))
    # also a slightly larger p for n=4 to see beta-dependence on M (period sums only, cheap)
    print("\n--- M-only beta sweep (no NBT), checking M vs sqrt(n) growth in regime ---")
    for n in [4, 8, 16]:
        for beta in [3.0, 4.0]:
            p = find_p(n, beta)
            g, Hset, Hlist = subgroup(p, n)
            M0 = M_of_periods(p, n, Hlist)
            print(f"  n={n:3d} p={p:9d} beta={math.log(p)/math.log(n):.2f}  M={M0:8.4f}  sqrt(n*log(p/n))={math.sqrt(n*math.log(p/n)):.4f}  M/sqrt(n)={M0/math.sqrt(n):.3f}")
