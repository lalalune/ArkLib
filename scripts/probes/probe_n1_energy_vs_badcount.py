#!/usr/bin/env python3
"""N1 DECISIVE TEST: does the Mobius pencil energy E2(H) predict the bad-scalar count?

N1 conjectures delta*(H) = F(E2(H)/n^2) -- i.e. the bad-scalar count past Johnson is
GOVERNED by the pencil energy E2 = sum_b t2(b)^2.  We test the CORE claim: across domains
of the same size n with DIFFERENT E2, does the bad count track E2?

- E2(H): t2(b) = #2-orbits of x -> b*x^-1 on H (= (n - #sqrt_H(b))/2), summed-squared over b in H.
- bad count: for RS[F_p, D, k], the EXACT mcaEvent bad-scalar count over the worst (u0,u1)
  line, at a radius delta.  Syndrome-reduced (per probe_exact_epsmca_ladder).

If smooth (subgroup) and random domains of equal n have very different E2 (n^3 vs n^2) but
SIMILAR bad counts past Johnson, N1's simple form is REFUTED (a real constraint: the
separating invariant does not directly set delta*).  Pre-registered.
"""
import itertools, random

def is_prime(n):
    if n < 2: return False
    for d in range(2, int(n**0.5)+1):
        if n % d == 0: return False
    return True

def mult_subgroup(p, n):
    """A multiplicative subgroup of F_p^* of order n (n | p-1)."""
    assert (p-1) % n == 0
    g = None
    for cand in range(2, p):
        # find an element of order n: take a generator^((p-1)/n)
        # first find a primitive root
        order = 1; x = cand % p; seen=set()
        # cheap order computation
        o=1; y=cand%p
        while y!=1:
            y=(y*cand)%p; o+=1
            if o>p: break
        if o==p-1:
            g=cand; break
    h = pow(g, (p-1)//n, p)
    H = sorted({pow(h, i, p) for i in range(n)})
    return H

def pencil_energy(p, D):
    """E2(D) = sum_{b in D-as-set} t2(b)^2 with sigma_b(x)=b*x^{-1} on D.
    For a subgroup this is the Mobius energy; for a general set we use the same formula
    over b in D (closure not assumed -> b*x^-1 may leave D; we count 2-orbits WITHIN D)."""
    Dset = set(D); n=len(D)
    inv = {x: pow(x, p-2, p) for x in D}
    E2 = 0
    for b in D:
        # orbits of x -> b * x^{-1} restricted to points whose image stays in D
        fixed = sum(1 for x in D if (x*x) % p == b % p)
        # 2-orbits: pairs {x, b x^-1} both in D, x != b x^-1
        paired = 0
        for x in D:
            y = (b * inv[x]) % p
            if y in Dset and y != x:
                paired += 1
        t2 = paired // 2
        E2 += t2*t2
    return E2

def rref(mat, p):
    m=[r[:] for r in mat]; rows=len(m); cols=len(m[0]) if m else 0; piv=[]; r=0
    for c in range(cols):
        pr=None
        for i in range(r,rows):
            if m[i][c]%p!=0: pr=i; break
        if pr is None: continue
        m[r],m[pr]=m[pr],m[r]
        invp=pow(m[r][c],p-2,p)
        m[r]=[(v*invp)%p for v in m[r]]
        for i in range(rows):
            if i!=r and m[i][c]%p!=0:
                f=m[i][c]; m[i]=[(a-f*b)%p for a,b in zip(m[i],m[r])]
        piv.append(c); r+=1
        if r==rows: break
    return m[:r],piv

def parity_check(p, D, k):
    """H: (n-k) x n parity check for RS[F_p, D, k] (eval of deg<k polys)."""
    n=len(D)
    # generator G: rows = [D[j]^i] for i<k
    G=[[pow(D[j], i, p) for j in range(n)] for i in range(k)]
    # null space of G = parity check H. Build via rref of G, free cols.
    R,piv=rref(G,p); pivset=set(piv); free=[c for c in range(n) if c not in pivset]
    Hrows=[]
    for fc in free:
        row=[0]*n; row[fc]=1
        for ri,pc in enumerate(piv):
            row[pc]=(-R[ri][fc])%p
        Hrows.append(row)
    return Hrows

def syndrome(H,w,p): return tuple(sum(H[i][j]*w[j] for j in range(len(w)))%p for i in range(len(H)))

def ext_from_S(p,D,k,s_syndrome,H,S):
    """Does some codeword agree with a word of syndrome s on all of S? (coset-invariant)
    Equivalent: exists codeword c with (w-c)|_S = 0 for any w of that syndrome.
    We test: the linear system 'codeword matches a fixed coset rep on S' is solvable."""
    n=len(D)
    # pick a coset representative w0 with syndrome s (solve H w0 = s)
    # then need codeword c (deg<k) with c(x)=w0(x) for x in S  -> interpolation feasibility
    # build w0 by least-structure: solve H x = s
    # Augment H with s and rref
    aug=[H[i][:]+[s_syndrome[i]] for i in range(len(H))]
    R,piv=rref(aug,p)
    for ri in range(len(R)):
        if all(R[ri][c]%p==0 for c in range(n)) and R[ri][n]%p!=0:
            return False  # no rep (shouldn't happen for valid syndrome)
    w0=[0]*n
    for ri,pc in enumerate(piv):
        if pc<n: w0[pc]=R[ri][n]%p
    # interpolation: deg<k poly through (D[j], w0[j]) for j in S  -> solvable iff
    # the |S| points with values are consistent with a deg<k poly. Build Vandermonde on S.
    Sl=sorted(S)
    V=[[pow(D[j],i,p) for i in range(k)]+[w0[j]] for j in Sl]
    R2,piv2=rref(V,p)
    for ri in range(len(R2)):
        if all(R2[ri][c]%p==0 for c in range(k)) and R2[ri][k]%p!=0:
            return False
    return True

def bad_count_at_delta(p, D, k, delta):
    """EXACT worst-case bad-scalar count at radius delta (syndrome-reduced).
    Returns max over syndrome-pairs (s0,s1) of #{gamma in F_p : line pt bad}.
    SMALL instances only."""
    n=len(D); H=parity_check(p,D,k); m=len(H)
    Sthresh = -(-int((1-delta)*n)//1)  # ceil((1-delta)n)
    Smin = int((1-delta)*n + 0.999999)  # |S| >= (1-delta) n
    # enumerate syndrome pairs
    best=0
    allS=[set(c) for r in range(Smin, n+1) for c in itertools.combinations(range(n), r)]
    syn_space=list(itertools.product(range(p), repeat=m))
    # limit blowup
    if len(syn_space)**2 * p > 6_000_000:
        return None  # infeasible by this method
    for s0 in syn_space:
        for s1 in syn_space:
            cnt=0
            for gamma in range(p):
                sg=tuple((s0[i]+gamma*s1[i])%p for i in range(m))
                # bad: line pt gamma is delta-close (ext from some S) but the WHOLE line
                # isn't jointly close on that S. We approximate the mcaEvent: exists S with
                # ext(sg,S) but not (ext(s0,S) and ext(s1,S)).  (faithful to pairJoint split)
                bad=False
                for S in allS:
                    if ext_from_S(p,D,k,sg,H,S) and not (ext_from_S(p,D,k,s0,H,S) and ext_from_S(p,D,k,s1,H,S)):
                        bad=True; break
                if bad: cnt+=1
            best=max(best,cnt)
    return best

# ---- run: compare smooth vs random domains of equal n, E2 vs bad count ----
print("N1 TEST: E2(H) vs bad-scalar count, smooth subgroup vs random subset (equal n,k)")
print(f"{'p':>4} {'n':>3} {'k':>2} {'domain':>8} {'E2':>8} {'E2/n^2':>7} {'delta':>6} {'badcount':>9}")
random.seed(1)
for (p,n,k) in [(13,4,2),(13,6,2),(13,4,3),(13,6,3)]:
    if (p-1)%n!=0: continue
    H=mult_subgroup(p,n)
    allpts=[x for x in range(1,p)]
    R=sorted(random.sample(allpts, n))
    for label,D in [("smooth",H),("random",R)]:
        E2=pencil_energy(p,D)
        # Johnson radius 1-sqrt(rho), rho=k/n; test just below & above
        import math
        rho=k/n; john=1-math.sqrt(rho)
        for delta in [round(john-0.05,3), round(john+0.05,3)]:
            if delta<=0 or delta>=1: continue
            bc=bad_count_at_delta(p,D,k,delta)
            print(f"{p:>4} {n:>3} {k:>2} {label:>8} {E2:>8} {E2/(n*n):>7.2f} {delta:>6} {str(bc):>9}")
