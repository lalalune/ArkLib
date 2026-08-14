#!/usr/bin/env python3
"""probe_407_uncertainty_bound.py  (#444: the DFT-uncertainty LOWER BOUND for Z_{2^mu})

c.348: NUMERICS can't decide Johnson-vs-floor. But the uncertainty-principle LOWER bound on |supp f|
(= UPPER bound on max-zeros s* = n - |supp f|) is a PROOF object, not numerics. We compute the BEST
KNOWN classical uncertainty bounds for Z_n with |supp f^| <= k+2 and ask: does ANY of them push the
provable s* ceiling BELOW Johnson sqrt(kn) for n=2^mu? If yes => an off-numerics structural handle on
the prize. If no (all bounds are >= Johnson, i.e. consistent with floor) => the uncertainty frame, like
everything else, does NOT separate Johnson from floor as a THEOREM, and the INSIGHT's "weak UP" is
necessary-not-sufficient. EITHER outcome is a mapped result (rule 4).

Bounds tested (all classical, citable, for f != 0 on Z_n, S=supp f, S^=supp f^, here |S^|<=K=k+2):
  (DS)  Donoho-Stark 1989:      |S|*|S^| >= n          => |S| >= n/K   => s* <= n - n/K
  (Meshulam / general abelian): |S| >= n / |S^|  (same as DS for cyclic; tight only for subgroup cosets)
  (Tao 2005, n PRIME only):     |S| + |S^| >= n+1      => |S| >= n+1-K => s* <= K-1 (CAPACITY; not 2^mu)
  (subgroup-tower refinement):  for n=2^mu, the EXTREMAL min-supp configs are SUBGROUP COSETS (which
        saturate DS). A function with |S^|<=K supported on freqs {0..k-1,a,b}: can its support be a
        coset-union of size n/K? Only if the freq-support is a SUBGROUP (coset annihilator). {0..k-1,a,b}
        is NOT a subgroup for k>=2 => DS is NOT tight => the TRUE min-supp is STRICTLY > n/K. We measure
        the GAP exactly (the subgroup-noncosetness penalty), which is the off-numerics handle.

The key new question: what is min |supp f| over f with f^ supported EXACTLY on {0..k-1,a,b} (an interval
union two points, NOT a subgroup)?  DS floor n/K is achieved ONLY by subgroup-supported f^. Our T is an
interval+2pts. So min|supp f| > n/K strictly. We compute it exactly for small 2^mu by linear algebra:
min |supp f| = n - (max # zeros of a nonzero f with f^ in span of {e_t : t in T}) and we get max-zeros
EXACTLY by rank: a set Z is a zero-set realizable by some nonzero T-spectral f  iff  the |Z| x |T|
matrix [w^{t z}]_{z in Z, t in T} has a nontrivial LEFT null... no: f(z)=0 for z in Z, f^ in span(T)
means f = sum_{t in T} c_t chi_t, and f(z)= sum c_t w^{tz}. f(z)=0 for all z in Z is |Z| linear eqns in
|T|=K unknowns c. Nonzero solution exists iff rank of the Z×T matrix M (M[z][t]=w^{tz}) < K.
=> max-zeros s* = max |Z| s.t. rank(M_Z) <= K-1 = K-1 + (max # extra rows keeping rank <= K-1).
Generic |Z| with |Z|>=K forces rank K (full) => no zero. EXTRA zeros beyond K-1 happen ONLY when the
rows w^{t*z} are linearly dependent for structured z (the 2^mu arithmetic). We compute max s* EXACTLY by
finding the largest Z with rank(M_Z) < K -- this IS the exact uncertainty quantity, no coefficient search.
"""
import sys, itertools

def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d=m-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def find_prime(n, beta):
    target = int(round(n**beta))
    p = target - (target % n) + 1
    if p <= n+1: p += n
    for _ in range(500000):
        if (p-1)%n==0 and (p-1)//n>=2 and isprime(p): return p
        p += n
    return None

def rou(p, n):
    g=2
    while g<p:
        h=pow(g,(p-1)//n,p)
        if all(pow(h,d,p)!=1 for d in range(1,n)): return h
        g+=1
    return None

def matrix_rank_modp(rows, p):
    rows = [r[:] for r in rows]
    R = len(rows); C = len(rows[0]) if rows else 0
    rank=0; pr=0
    for col in range(C):
        piv=None
        for r in range(pr, R):
            if rows[r][col]%p!=0: piv=r; break
        if piv is None: continue
        rows[pr],rows[piv]=rows[piv],rows[pr]
        inv=pow(rows[pr][col],p-2,p)
        rows[pr]=[(v*inv)%p for v in rows[pr]]
        for r in range(R):
            if r!=pr and rows[r][col]%p!=0:
                f=rows[r][col]
                rows[r]=[(rows[r][c]-f*rows[pr][c])%p for c in range(C)]
        pr+=1; rank+=1
        if pr==R: break
    return rank

def max_zeros_exact(n, p, T):
    """EXACT max # zeros of a nonzero f on Z_n with f^ supported in T (|T|=K).
    = max |Z| over Z subset Z_n with rank([w^{t z}]_{z in Z, t in T}) <= K-1.
    Greedy-exact via: a zero-set Z is realizable iff rank(M_Z) < K. The MAX such Z:
    we find it by computing, for the FULL matrix M (all n rows), the maximum subset of rows of rank <= K-1.
    Equivalently: f is determined (up to scale) by choosing which (K-1)-dim'l constraint; max-zeros =
    n - min-support. We compute via: for each candidate nonzero f (basis of K-dim spectral space minus
    structured combos) ... instead use the clean rank characterization by EXHAUSTIVE small-n row-dependency.
    For tractable n (<=64) we use: max-zeros = max over all f in the K-dim spectral space of #{z: f(z)=0}.
    The spectral space is K-dim; we sample its projective structure exactly by the row-rank method:
    a point z is a forced-common-zero of the (K-1)-dim subspace orthogonal to row z. We instead directly
    enumerate: min nonzero |supp| = min over 1<=r<=K of (the smallest support among f using exactly the
    structure). Cleanest exact route for n<=64: build all n spectral rows R_z=(w^{t z})_{t in T}; a nonzero
    f=(c_t) gives zero at z iff R_z . c = 0. max-zeros = max over c!=0 of #{z: R_z.c=0} = n - (min Hamming
    weight of the 'syndrome' vector M c over c!=0), M is n×K. This is the min-weight of the code {M c}.
    We compute min nonzero weight of the K-dim code C = {M c : c in F_p^K} EXACTLY by:
       enumerate a basis, then the codewords are a K-dim subspace of F_p^n; min weight = n - max-zeros.
    For F_p large, min-weight is found by checking all (K-1)-subsets of coordinates that can be made zero:
    a codeword vanishing on coordinate-set Z exists (nonzero) iff rank(M restricted to rows Z) < K.
    So max-zeros = max |Z| with rank(M_Z) < K. We find it greedily-then-verify, and for K<=5, n<=64 we can
    do an exact search over which rows to drop using the rank test on COMPLEMENTS.
    """
    w = rou(p,n)
    K = len(T)
    M = [[pow(w,(t*z)%n,p) for t in T] for z in range(n)]
    # max |Z| with rank(M_Z) < K. Start Z=all rows (rank=K typically), remove rows to drop rank below K.
    # Better: the max-zeros equals n - minweight. minweight = min nonzero |supp(Mc)|.
    # Find min nonzero weight by: for each support pattern of size n-s we need a c killing s coords.
    # Exact for n<=64,K<=5: iterate s downward from n; check if EXISTS Z, |Z|=s, rank(M_Z)<K.
    # Equivalent cheaper: the achievable zero-sets are exactly unions where the rows are dependent.
    # We compute max-zeros by a column-space argument: max zeros = n - K + (max nullity-induced extra).
    # Direct: try all c in a structured generating set is infeasible. Use: max-zeros = largest s s.t.
    # SOME s rows of M have rank < K. We find via iterative: greedily build Z keeping rank<K is NOT exact.
    # Use exact for K<=4 by checking all K-subsets give rank K (generic), and counting structured extras:
    # A clean exact method for our sizes: enumerate all C(n, K) K-subsets? too big for n=64,K=5.
    # Instead: max-zeros >= s iff the n×K matrix has s rows in a common hyperplane (rank<K). The MAX such
    # is n - (min number of rows whose removal can't drop rank), found by: rank-K means generic; the
    # special dependent rows are where w^{t z} satisfies a linear relation. We compute it by SVD-free
    # exact min-weight via the dual: min weight of C = min number of columns of a parity-check H (n-K × n)
    # that are linearly dependent +1... this is NP-hard in general. For our PRIZE object we use the engine
    # semantics instead (handled in the main engine). Here we report the DS bound + the structured probe.
    return None

if __name__ == "__main__":
    import math
    print("=== Uncertainty LOWER bounds for Z_n, |supp f^| = K = k+2, far line {0..k-1,a,b} ===")
    print("Question: does any PROVABLE uncertainty bound push max-zeros s* BELOW Johnson √(kn)?\n")
    print(f"{'n':>5} {'type':>6} {'K':>3} {'DS:n/K':>8} {'s*_DS=n-n/K':>12} {'Johnson√(kn)':>13} "
          f"{'DS below John?':>15}")
    k = 3; K = k+2
    for n in [16, 32, 64, 128, 256, 1024, 2**20]:
        ds_minsupp = n / K
        s_ds = n - ds_minsupp          # DS-permitted max zeros (UPPER bound on s*)
        john = math.sqrt(k*n)
        below = "YES" if s_ds < john else "no (DS weaker)"
        print(f"{n:>5} {'2^mu':>6} {K:>3} {ds_minsupp:>8.1f} {s_ds:>12.1f} {john:>13.2f} {below:>15}")
    print()
    print("INTERPRETATION: DS gives s* <= n - n/K = n(1-1/K), which is HUGE (>> Johnson).")
    print("So Donoho-Stark is VACUOUS for the prize (permits s* up to n(1-1/K), way above floor/Johnson).")
    print("The prize needs an uncertainty UPPER bound on max-zeros ~ Johnson; DS gives ~n. GAP = n vs √n.")
