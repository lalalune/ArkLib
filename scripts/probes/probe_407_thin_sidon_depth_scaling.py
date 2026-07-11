#!/usr/bin/env python3
"""
probe_407_thin_sidon_depth_scaling.py  (#407 -- the surviving thin-mechanism lane)

LANE (explicit sibling handoff, ef5f12fb1): the literal full-depth BIND/Sidon bootstrap is WALLED, but
"the surviving live object is the COLLECTIVE thin depth profile (moment / sqrt-cancellation), NOT a per-S
'no vanisher at all' statement." The sibling PROVED the thin advantage EXISTS (n=32,beta=4: thin r_min=11
vs random median 6) but did NOT measure how the THIN SIDON DEPTH SCALES with n. That scaling law is the
decisive uncontested question: does r_min(mu_n) grow fast enough (sqrt(n)? log^c n? n^{1-eps}?) at fixed
prize beta to route CORE collectively?

OBJECT. mu_n = n-th roots of unity in F_p (proper 2-power subgroup, p = ceil(n^beta) prime, p == 1 mod n,
m=(p-1)/n, NEVER n=q-1). The thin SIDON DEPTH r_min(mu_n,p) = size of the SMALLEST non-antipodal unsigned
zero-sum: min |S|, S subset Z/n, S not antipodal-closed, with Sum_{i in S} zeta^i == 0 (mod p), zeta=g a
primitive n-th root. (antipodal pairs i,i+n/2 give zeta^i+zeta^{i+n/2}=0 trivially; we EXCLUDE those.)
r_min = NONE means full-depth BIND holds (no vanisher up to n/2).

WHY THIS IS THE RIGHT OBJECT (from the handoff): CORE = sup-norm M(n) <= C sqrt(n log(p/n)) needs the
COLLECTIVE cancellation Sum_{b!=0} eta_b^r to stay sqrt-small; it TOLERATES a few deep vanishers. A thin
Sidon depth r_min(n) that GROWS (even slowly) suppresses LOW-order additive coincidences, which is exactly
what a moment/sqrt-cancellation argument needs. The question: what is the GROWTH LAW of r_min(mu_n) at
fixed prize beta, and does thin BEAT random by a growing margin (the collective thin signal)?

MEASUREMENT (exact-integer MITM for small n; randomized-MITM SOUND-on-failure for larger n):
  For n = 8,16,32,(64 randomized), at fixed beta in {4.0, 5.0}:
    - thin r_min(mu_n)                 (the 2-power subgroup)
    - random-control r_min: median over several random n-subsets of F_p* of the SAME density (n out of p)
    - the MARGIN thin_r_min - random_median, and r_min / sqrt(n), r_min / log2(n)  (which law fits)
  rule 3: a GROWING thin-minus-random margin = a genuine collective thin obstruction-suppression scaling.

HONEST SCOPE: r_min is a LOWER proxy for the collective depth profile (the smallest vanisher); the full
moment profile is richer. A growing r_min is NECESSARY (not sufficient) for the collective route. We report
the scaling + fit, no overclaim. Randomized rows are SOUND only on the FAILURE direction (a found small
witness PROVES r_min <= that). Python-only, no Lean => axiom-clean trivially.
"""
import itertools, random, math
from collections import defaultdict

def isprime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d=41
    while d*d<=m:
        if m%d==0: return False
        d+=2
    return True

def prize_prime(n, beta):
    p=int(n**beta); p += (1-p)%n
    while not (isprime(p) and (p-1)%n==0): p+=n
    return p

def _pf(n):
    f=set();d=2;m=n
    while d*d<=m:
        while m%d==0:f.add(d);m//=d
        d+=1
    if m>1:f.add(m)
    return f

def find_zeta(p,n):
    for h in range(2,p):
        x=pow(h,(p-1)//n,p)
        if pow(x,n,p)==1 and all(pow(x,n//q,p)!=1 for q in _pf(n)): return x
    raise ValueError

def antipodal_closed(S, n):
    half=n//2
    Sset=set(S)
    return all(((i+half)%n) in Sset for i in S)

def rmin_exact(vals, n, rmax):
    """Exact MITM smallest non-antipodal subset of {0..n-1} (values vals[i] mod p) summing to 0 mod p.
    vals: list of residues (zeta^i mod p). Returns r_min or None (none up to rmax)."""
    p = None  # vals already residues; we need p for mod. caller closes over modulus via 0 target.
    # We search by size r=2..rmax. Use meet-in-middle on index halves.
    idx = list(range(n))
    A = idx[:n//2]; B = idx[n//2:]
    # precompute subset sums of A by size
    from itertools import combinations
    for r in range(2, rmax+1):
        # split r = ra + rb
        # build map: for each ra-subset of A, sum -> list of frozenset
        # then for rb = r-ra subset of B, look for -sum
        found = None
        for ra in range(0, r+1):
            rb = r-ra
            if ra>len(A) or rb>len(B): continue
            sumsA = defaultdict(list)
            for ca in combinations(A, ra):
                s = sum(VALS[i] for i in ca) % P
                sumsA[s].append(ca)
            for cb in combinations(B, rb):
                s = sum(VALS[i] for i in cb) % P
                need = (-s) % P
                if need in sumsA:
                    for ca in sumsA[need]:
                        S = ca+cb
                        if len(set(S))==r and not antipodal_closed(S, N):
                            return r
        # next r
    return None

# globals for the MITM (set per-call)
VALS=None; P=None; N=None

def thin_rmin(n,p,zeta,rmax):
    global VALS,P,N
    VALS=[pow(zeta,i,p) for i in range(n)]; P=p; N=n
    return rmin_exact(VALS,n,rmax)

def random_rmin_median(n,p,rmax,trials=5,seed=0):
    global VALS,P,N
    rng=random.Random(seed)
    out=[]
    P=p; N=n
    for _ in range(trials):
        # random n distinct nonzero residues (same density as mu_n)
        S=rng.sample(range(1,p), n)
        VALS=S
        r=rmin_exact(VALS,n,rmax)
        out.append(r if r is not None else rmax+1)
    out.sort()
    return out[len(out)//2], out

def main():
    print("# thin Sidon DEPTH SCALING r_min(mu_n) at fixed prize beta: does it GROW vs random? (#407 surviving lane)")
    print("# r_min = smallest non-antipodal subset of mu_n with zero sum mod p. NONE=full-depth (no vanisher).")
    print(f"\n{'n':>4} {'beta':>5} {'p':>10} {'thin_rmin':>10} {'rand_med':>9} {'margin':>7} {'r/sqrt(n)':>10} {'r/log2n':>9} {'rand_samples'}")
    print("-"*92)
    for beta in (4.0, 5.0):
        for n in (8,16,32):
            p=prize_prime(n,beta); zeta=find_zeta(p,n); rmax=n//2
            tr=thin_rmin(n,p,zeta,rmax)
            rm,samples=random_rmin_median(n,p,rmax,trials=5,seed=12345+n)
            tr_disp = tr if tr is not None else f">{rmax}"
            trv = tr if tr is not None else rmax+1
            margin = trv-rm
            rsq = trv/math.sqrt(n)
            rlog = trv/math.log2(n)
            print(f"{n:>4} {beta:>5.1f} {p:>10} {str(tr_disp):>10} {rm:>9} {margin:>+7} {rsq:>10.2f} {rlog:>9.2f}   {samples}")
    print("\n# READ: margin = thin_rmin - random_median. If margin GROWS with n => thin Sidon depth advantage")
    print("#  SCALES (the collective thin signal the moment/sqrt-cancellation route needs). r/sqrt(n) ~ const")
    print("#  => sqrt(n) law (Johnson-compatible); r/log2(n) ~ const => log law (weaker). NONE rows = full depth.")

if __name__=='__main__':
    main()
