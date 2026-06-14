#!/usr/bin/env python3
"""
#407 — The subset-sum FIBRE / lattice-relation reframing of the prize floor.

THE REDUCTION (in-tree, proven):
  Bad scalars of the deep-band pencil X^{k+1}+gamma X^k are pinned by Vieta:
  gamma = -sum_{zeta in S} zeta, S subset of mu_n.  The worst-case LIST size
  (= q*eps_mca) equals the maximal FIBRE of the subset-sum map
        Phi : {r-subsets of mu_n} -> F_p,   S |-> sum_{zeta in S} zeta.
  The closed-form candidate is  delta* = 1 - rho - H(rho)/log2(q*eps*),
  which is the entropy crossover where the CHAR-0 max fibre N_fib(n,r) = C(n/2, r/2)
  (Lam-Leung antipodal structure) crosses the budget B = q*eps* ~ n.

THE OPEN CORE (the floor): worst-case F_p list <= N_fib, i.e. the char-p fibre does
  NOT inflate beyond the char-0 fibre below the crossover.

THE NEW HANDLE (this probe):  Writing a subset sum in the Z-basis {1,z,...,z^{n/2-1}}
  via z^{n/2} = -1, a sum is a vector c in {-1,0,1}^{n/2}.  Char-0 collisions force
  c = c' (basis independence).  Over F_p the sum is sum_i c_i g^i, so
        p-DEFECTS  <=>  nonzero short vectors of L = ker(Z^{n/2} -> F_p, e_i |-> g^i).
  The fibre inflation is governed by the MINIMAL HAMMING WEIGHT w_min of a nonzero
  c in {-1,0,1}^{n/2} with sum_i c_i g^i = 0 mod p.  This SEPARATES OUT the W2
  diagonal floor (c=0 main term) and is an O(1)-weight, q-independent computable object.

This probe measures, for genuine prize-like instances (n=2^mu, p ~ n^beta, beta~4):
  (A) ground-truth: char-0 max fibre vs char-p max fibre (exhaustive, small n);
  (B) the lattice min-weight relation w_min and low-weight relation counts (scalable);
  (C) correlation: does fibre inflation track w_min, and is the floor (no inflation
      below crossover) consistent?
"""
import itertools, math, sys
from collections import defaultdict

def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,n)
        if x==1 or x==n-1: continue
        for _ in range(r-1):
            x = x*x%n
            if x==n-1: break
        else: return False
    return True

def find_primes_for_n(n, beta_lo=3.5, beta_hi=4.8, count=6, avoid_fermat=True):
    """Primes p == 1 mod n with log_n(p) in [beta_lo, beta_hi]."""
    lo = int(n**beta_lo); hi = int(n**beta_hi)
    lo += (1 - lo) % n  # first == 1 mod n at/above lo
    out=[]
    p = lo
    while p <= hi and len(out) < count:
        if is_prime(p):
            # avoid p = 2^k+1 Fermat-type traps (m a pure 2-power -> #400 artifact)
            if not (avoid_fermat and (p-1 & (p-2))==0):
                out.append(p)
        p += n
    return out

def order_n_generator(p, n):
    """An element g of F_p* of exact order n (n | p-1)."""
    # primitive root h, then g = h^{(p-1)/n}
    fac = factorize(p-1)
    for h in range(2, p):
        if all(pow(h,(p-1)//q,p)!=1 for q in fac):
            return pow(h,(p-1)//n,p)
    raise RuntimeError("no primitive root?!")

def factorize(m):
    fs=set(); d=2
    while d*d<=m:
        while m%d==0: fs.add(d); m//=d
        d+=1
    if m>1: fs.add(m)
    return fs

def Hbin(x):
    if x<=0 or x>=1: return 0.0
    return -x*math.log2(x)-(1-x)*math.log2(1-x)

# ---------------------------------------------------------------------------
# (A) GROUND TRUTH: exhaustive char-0 vs char-p max fibre of S |-> sum_S zeta
# ---------------------------------------------------------------------------
def exhaustive_fibres(n, p, g, r):
    """Return (char0_maxfibre, charp_maxfibre, charp_image_size, N_fib_formula).
    Enumerate all r-subsets of mu_n = {g^0..g^{n-1}}; bin by char-0 c-vector and
    by F_p sum value."""
    half = n//2
    powg = [pow(g, j, p) for j in range(n)]
    char0 = defaultdict(int)   # c-vector (tuple in {-1,0,1}^half) -> count
    charp = defaultdict(int)   # F_p value -> count
    for S in itertools.combinations(range(n), r):
        Sset = set(S)
        cvec = tuple((1 if i in Sset else 0) - (1 if (i+half) in Sset else 0)
                     for i in range(half))
        char0[cvec]+=1
        v = sum(powg[j] for j in S) % p
        charp[v]+=1
    c0max = max(char0.values())
    cpmax = max(charp.values())
    # N_fib formula: C(half - r%2, r//2)
    nfib = math.comb(half - (r%2), r//2)
    return c0max, cpmax, len(charp), nfib

# ---------------------------------------------------------------------------
# (B) LATTICE MIN-WEIGHT: minimal Hamming weight nonzero c in {-1,0,1}^{half}
#     with sum_i c_i g^i = 0 mod p.  Meet-in-the-middle.
# ---------------------------------------------------------------------------
def _enum_side(coords, powg, p, side_cap):
    """dict: value mod p -> dict(weight -> count) for all {-1,0,1} assignments on
    `coords` with Hamming weight <= side_cap.  Explicit support+sign enumeration."""
    res = defaultdict(lambda: defaultdict(int))
    res[0][0] = 1
    for w in range(1, side_cap+1):
        for supp in itertools.combinations(coords, w):
            base = [powg[i] for i in supp]
            for signs in itertools.product((1,-1), repeat=w):
                v = 0
                for s,b in zip(signs, base): v = (v + s*b) % p
                res[v][w] += 1
    return res

def min_weight_relation(p, g, half, wmax=8):
    """w_min = min Hamming weight of nonzero c in {-1,0,1}^{half} with
    sum_i c_i g^i = 0 mod p.  Meet-in-the-middle with per-side weight cap = wmax//2."""
    powg = [pow(g, i, p) for i in range(half)]
    A = half//2
    side_cap = (wmax+1)//2
    L = _enum_side(list(range(A)), powg, p, side_cap)
    R = _enum_side(list(range(A, half)), powg, p, side_cap)
    weight_counts = defaultdict(int)
    for val, wdL in L.items():
        wdR = R.get((-val) % p)
        if wdR:
            for wl,cl in wdL.items():
                for wr,cr in wdR.items():
                    w = wl+wr
                    if 1 <= w <= wmax:
                        weight_counts[w] += cl*cr
    if not weight_counts:
        return None, 0, {}
    wmin = min(weight_counts)
    return wmin, weight_counts[wmin], dict(sorted(weight_counts.items()))

# ---------------------------------------------------------------------------
# MAIN
# ---------------------------------------------------------------------------
print("="*78)
print("(A) GROUND TRUTH: char-0 vs char-p max fibre of subset-sum over mu_n")
print("    (does the F_p fibre inflate beyond the char-0 Lam-Leung N_fib?)")
print("="*78)
print(f"{'n':>3} {'p':>10} {'beta':>5} {'r':>3} | {'N_fib':>8} {'char0max':>9} {'charpmax':>9} {'inflate':>8} {'img/Cnr':>8}")
for n in (8,16):
    half=n//2
    primes = find_primes_for_n(n, count=2)
    for p in primes:
        beta = math.log(p)/math.log(n)
        g = order_n_generator(p,n)
        for r in range(2, n+1, max(1,n//8)):
            if math.comb(n,r) > 3_000_000:  # keep exhaustive feasible
                continue
            c0,cp,img,nfib = exhaustive_fibres(n,p,g,r)
            infl = cp/c0 if c0 else float('nan')
            tot = math.comb(n,r)
            print(f"{n:>3} {p:>10} {beta:>5.2f} {r:>3} | {nfib:>8} {c0:>9} {cp:>9} {infl:>8.3f} {img/tot:>8.4f}")

print()
print("="*78)
print("(B) LATTICE MIN-WEIGHT RELATION w_min of mu_n in F_p")
print("    w_min = min Hamming weight nonzero c in {-1,0,1}^{n/2}, sum c_i g^i = 0 mod p")
print("    (the O(1)-weight object governing fibre inflation; worst over g,p)")
print("="*78)
print(f"{'n':>3} {'p':>12} {'beta':>5} | {'w_min':>5} {'#@wmin':>7}   weight->count (low weights)")
for n in (8,16,32,64,128):
    half=n//2
    primes = find_primes_for_n(n, count=5)
    worst_wmin = 99; rows=[]
    for p in primes:
        beta = math.log(p)/math.log(n)
        g = order_n_generator(p,n)
        wmax = 10 if half<=16 else 8
        wmin,cnt,wc = min_weight_relation(p,g,half,wmax=wmax)
        rows.append((n,p,beta,wmin,cnt,wc))
        if wmin is not None: worst_wmin=min(worst_wmin,wmin)
    for (n,p,beta,wmin,cnt,wc) in rows:
        wcs = " ".join(f"{w}:{c}" for w,c in list(wc.items())[:5]) if wc else "(none<=wmax)"
        print(f"{n:>3} {p:>12} {beta:>5.2f} | {str(wmin):>5} {cnt:>7}   {wcs}")
    print(f"    -> n={n}: WORST (min over primes) w_min = {worst_wmin}")
    print()
