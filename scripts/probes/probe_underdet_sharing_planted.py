#!/usr/bin/env python3
"""
UNDER-DET / SHARING lane (#444), PART 2: adversarially MAXIMIZE the sharing.

Part-1 (worst structured line) found mult==1 everywhere: zero sharing on the binder line.
Now we PLANT joint agreement to make sharing as large as possible and measure its CAP vs band.

Construction: pick a deg-<k codeword pair (v0,v1) (here deg<=k-1 polynomials evaluated on mu_n).
Set u0 = v0, u1 = v1 EXACTLY on a planted set P, and GENERIC elsewhere. Then on every subset of
P, the pair is jointly deg-<k => aligned for EVERY gamma (mult = "all" = p). This is the MAXIMAL
sharing. The question the brief poses: how large can such a SHARED (multi-gamma / jointly-deg<k)
set be while still being a genuine alignment in the census? And does that size reach the deep
binding band a0 ~ n/2, or is it Johnson-capped?

KEY STRUCTURAL POINT (the thing to verify, then formalize):
A jointly-deg<k set P (u0,u1 both deg<k on P) has NO size cap from joint-agreement ALONE -- you can
plant P as large as you want by construction. BUT in the census, the binding object is the BAD-SET
count = sets aligned for some gamma WITH A NON-DEGENERATE TUPLE (residual not jointly zero). The
non-degeneracy clause in CensusDomination EXCLUDES exactly the jointly-deg<k (mult="all") sets:
those have residual u0 = residual u1 = 0 on every tuple => they FAIL the
  "exists t injective in S: NOT (residual u0 = 0 AND residual u1 = 0)"
clause. So the SHARED (multi-gamma) sets are PRECISELY the ones the census throws away as
degenerate. The census counts only mult==1 (single-gamma, non-degenerate) sets.

So we test BOTH counts as a function of planted-P size:
  - n_aligned_nondeg(a): a-sets aligned for some gamma WITH a non-degenerate tuple (the census object)
  - n_shared(a): a-sets that are jointly-deg<k (mult = all, the sharing)
and confirm the census object EXCLUDES the sharing, i.e. growing the planted joint agreement does
NOT grow the census bad-count at the deep band (the sharing is invisible to the binding constraint).
If confirmed: SHARING COLLAPSES (contributes 0 to the binding census) => beyond-Johnson cannot come
from the sharing face; it must be the per-gamma char-sum (BGK) wall. A clean structural result.

Exact mod p, PROPER mu_n, p>>n^3, multi-prime, NEVER n=q-1.
"""
import itertools
from math import comb

def prime_factors(n):
    fs=set(); d=2
    while d*d<=n:
        while n%d==0: fs.add(d); n//=d
        d+=1
    if n>1: fs.add(n)
    return fs

def find_prime(n, lo):
    p = lo; p += (1 - p) % n
    if p < 3: p = n+1
    while True:
        if p>2 and p%n==1 and all(p%d for d in range(2,int(p**0.5)+1)):
            return p
        p += n

def find_g(p, n):
    for h in range(2, 20000):
        x = pow(h, (p-1)//n, p)
        if pow(x,n,p)==1 and all(pow(x,n//q,p)!=1 for q in prime_factors(n)):
            return x
    raise ValueError

def divided_diff(vals, T, xs, p):
    acc = 0
    for i in T:
        den = 1
        for j in T:
            if i!=j: den = den*((xs[i]-xs[j])%p)%p
        acc = (acc + vals[i]*pow(den,-1,p))%p
    return acc

def run(n, k, planted_sizes, beta_lo):
    p = find_prime(n, max(beta_lo, n**3))
    g = find_g(p, n)
    xs = [pow(g,i,p) for i in range(n)]
    # deg<k codewords v0,v1: random-ish deg = k-1 polynomials
    import random
    random.seed(12345)
    def poly_eval(coeffs):
        return [sum(c*pow(x,j,p) for j,c in enumerate(coeffs))%p for x in xs]
    v0 = poly_eval([random.randrange(p) for _ in range(k)])  # deg <= k-1 => deg < k
    v1 = poly_eval([random.randrange(p) for _ in range(k)])
    # generic words g0,g1 (off the planted set)
    gen0 = [random.randrange(p) for _ in range(n)]
    gen1 = [random.randrange(p) for _ in range(n)]
    results = []
    for psize in planted_sizes:
        P = set(range(psize))   # plant joint agreement on first `psize` coords
        u0 = [v0[i] if i in P else gen0[i] for i in range(n)]
        u1 = [v1[i] if i in P else gen1[i] for i in range(n)]
        # precompute residuals
        Tlist = list(itertools.combinations(range(n), k+1))
        e0 = {T: divided_diff(u0,T,xs,p) for T in Tlist}
        e1 = {T: divided_diff(u1,T,xs,p) for T in Tlist}
        def classify(S):
            forced=None; all_dz=True
            for T in itertools.combinations(sorted(S), k+1):
                a_,b_=e0[T],e1[T]
                if b_==0:
                    if a_!=0: return "none"
                else:
                    all_dz=False
                    gv=(-a_*pow(b_,-1,p))%p
                    if forced is None: forced=gv
                    elif forced!=gv: return "none"
            if all_dz: return "shared"   # jointly deg<k (mult=all), degenerate
            return "single" if forced is not None else "shared"
        # measure at the deep binding band a0 = n//2 (and a couple around it)
        bands = [b for b in (n//2 - 1, n//2, n//2 + 1) if k+1 <= b <= n]
        row = dict(psize=psize, p=p)
        for a in bands:
            n_single=0; n_shared=0
            for S in itertools.combinations(range(n), a):
                c=classify(set(S))
                if c=="single": n_single+=1
                elif c=="shared": n_shared+=1
            row[f"a{a}_single"]=n_single
            row[f"a{a}_shared"]=n_shared
        results.append((row,bands))
    return p, results

if __name__=="__main__":
    for n in [12, 16]:
        k=2
        psizes = [0, k, k+2, n//2, n//2+2, n-2]  # grow the planted joint agreement
        psizes = sorted(set(x for x in psizes if 0<=x<=n))
        print(f"\n=== n={n} k={k}: grow planted JOINT agreement, watch census(single,nondeg) vs sharing ===")
        p, results = run(n,k,psizes, n**3)
        bands = results[0][1]
        hdr = "  planted " + " ".join(f"a{a}:SGL/SHR" for a in bands)
        print(f"  p={p}")
        print(hdr)
        for row,bands in results:
            cells=" ".join(f"{row[f'a{a}_single']:>4}/{row[f'a{a}_shared']:<4}" for a in bands)
            print(f"  {row['psize']:>7}  {cells}")
