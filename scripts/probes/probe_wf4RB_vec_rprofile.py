#!/usr/bin/env python3
"""
wf-RB (#444): DECISIVE numpy-VECTORIZED over-determined far-line r-profile I(n,r), n=32,34,38.

See probe_wf4RB_overdet_rprofile.py for the object/mission. This is the FAST engine: it computes
the per-subset far-coset gamma for ALL C(n,s) witness sets at once via batched modular linear
algebra, so the GOOD (small-count) rungs -- which the CPython engine enumerates one-subset-at-a-time
at ~4s/rung -- become seconds even at n=32.

VECTORIZED MECHANISM (far-coset law, FarCosetExplosion / probe_farline_incidence_exact).
For an agreement set R (|R|=s, rung r=n-s) with points X=mu|_R and far/offset values
u1=X^b, u0=X^a:
  u in RS[k]|_R  <=>  u in col(V_R), V_R the s x k Vandermonde [X^0..X^{k-1}].
  Equivalently  W_R @ u = 0  where W_R is a basis of the (s-k)-dim LEFT null space of V_R.
  We use the (s-k) consecutive order-k DIVIDED-DIFFERENCE functionals as W_R rows (each is a
  sparse k+1-support left null vector of V_R on a sorted window -- the standard RS parity check).
  Then:
    * R "heavy" (=> all gammas, incidence p) iff  W_R u0 = 0 AND W_R u1 = 0.
    * else the affine system  W_R u0 + gamma W_R u1 = 0  has a solution gamma iff the two
      (s-k)-vectors  W_R u0  and  W_R u1  are PARALLEL (proportional) AND  W_R u1 != 0; the
      common ratio gives  gamma = -(first nonzero comp of W_R u0)/(corresp comp of W_R u1),
      checked for consistency across all components. (For s-k=1 this is automatic.)
  I(a,b;s) = #distinct such gamma over all R (+ p if any heavy).

All of W_R u0, W_R u1 over ALL subsets R are computed as batched numpy int64 mod-p matmuls.
"""
import sys, itertools
from math import comb
import numpy as np

def isprime(x):
    if x < 2: return False
    d = x-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a % x == 0: continue
        y = pow(a, d, x)
        if y in (1, x-1): continue
        ok = False
        for _ in range(s-1):
            y = y*y % x
            if y == x-1: ok = True; break
        if not ok: return False
    return True
def fac(x):
    f = {}; dd = 2
    while dd*dd <= x:
        while x % dd == 0: f[dd] = f.get(dd,0)+1; x //= dd
        dd += 1
    if x > 1: f[x] = f.get(x,0)+1
    return f
def proot(p):
    fs = set(fac(p-1))
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fs): return g
def find_prime_cong1(n, lo):
    c = lo + ((1 - lo) % n)
    if c <= 2: c += n
    while not (c % n == 1 and isprime(c)): c += n
    return c
def setup(n, p):
    g = proot(p); h = pow(g, (p-1)//n, p)
    return np.array([pow(h, i, p) for i in range(n)], dtype=np.int64)

def mulmod(A, B, p):
    # int64 matmul guarded against overflow: do it in python-int via object? No -- use blockwise.
    # p < 2^21 so products < 2^42, sums over <= k+1<=64 terms < 2^48 < 2^63 OK in int64.
    return (A @ B) % p

def ddk_weights(Xwin, k, p):
    """Order-k divided-difference functional weights on a (k+1)-point sorted window Xwin.
       Returns a length-(k+1) vector w with  sum_t w[t]*f(Xwin[t]) = [Xwin]f = 0 iff deg f < k.
       w[t] = 1 / prod_{j!=t} (Xwin[t]-Xwin[j])  (Lagrange / divided-difference)."""
    w = np.empty(k+1, dtype=np.int64)
    for t in range(k+1):
        denom = 1
        for j in range(k+1):
            if j != t:
                denom = denom * int((Xwin[t]-Xwin[j]) % p) % p
        w[t] = pow(denom, p-2, p)
    return w

def incidence_vec(a, b, n, mu, k, p, s, budget, maxscan=None):
    """Vectorized exact I(a,b;s) with early stop at >budget distinct gammas (returns budget+1),
       or p if a heavy set exists. If maxscan is set and we scan that many subsets without
       exceeding budget, return ('CAP', count_so_far) meaning 'not the binder, <=budget so far'."""
    r = n - s
    c = s - k  # over-determination
    if c < 1:
        return None  # not over/critically determined; far-coset law for c>=1
    Xall = mu  # mu[i] = generator^i, already "sorted" by exponent; agreement sets are index subsets
    u0all = np.array([pow(int(x), a, p) for x in mu], dtype=np.int64)
    u1all = np.array([pow(int(x), b, p) for x in mu], dtype=np.int64)
    # Build all s-subsets as a (C,s) int array (indices ascending). Stream in chunks.
    gam = set()
    heavy = False
    CHUNK = 200000
    combs = itertools.combinations(range(n), s)
    invtab = {}  # memo for divided-diff denominators per window not feasible; recompute per subset row-block
    # We need, per subset R (sorted indices), the c divided-diff functionals on consecutive
    # windows R[i:i+k+1], i=0..c-1, applied to u0|_R and u1|_R.
    # Vectorize: for a chunk of subsets, build index array, gather X,u0,u1, compute the c
    # windowed dd-values. The dd-weights depend on the actual X-window (per subset) so we compute
    # them with a small per-row loop over the c windows but vectorized across the chunk via
    # gathering -- still C-level numpy for the gather and the final dot.
    buf = []
    def flush(rows):
        nonlocal heavy
        if not rows: return False
        idx = np.array(rows, dtype=np.int64)              # (B, s)
        Xs = Xall[idx]                                     # (B, s)
        U0 = u0all[idx]; U1 = u1all[idx]                   # (B, s)
        B = idx.shape[0]
        d0 = np.zeros((B, c), dtype=np.int64)
        d1 = np.zeros((B, c), dtype=np.int64)
        for i in range(c):
            win = Xs[:, i:i+k+1]                            # (B, k+1)
            # weights per row: w[t] = 1/prod_{j!=t}(win[t]-win[j])
            # compute pairwise diffs (B,k+1,k+1)
            diff = (win[:, :, None] - win[:, None, :]) % p  # (B,k+1,k+1)
            # product over j!=t of diff[:,t,j]; set diagonal to 1
            dd = diff.copy()
            ii = np.arange(k+1)
            dd[:, ii, ii] = 1
            prod = np.ones((B, k+1), dtype=np.int64)
            for j in range(k+1):
                prod = (prod * dd[:, :, j]) % p
            # modular inverse of prod via Fermat (vectorized pow)
            winv = pow_mod_vec(prod, p-2, p)               # (B,k+1)
            w = winv                                       # (B,k+1)
            d0[:, i] = (w * U0[:, i:i+k+1]).sum(axis=1) % p
            d1[:, i] = (w * U1[:, i:i+k+1]).sum(axis=1) % p
        # classify rows
        z0 = (d0 == 0).all(axis=1)
        z1 = (d1 == 0).all(axis=1)
        if (z0 & z1).any():
            heavy = True
            return True  # incidence = p, stop
        # rows with z1 (u1 in RS) but not heavy -> no gamma (far direction stays far), skip
        cand = ~z1
        if c == 1:
            # gamma = -d0/d1 for cand rows with d1!=0
            sel = cand & (d1[:, 0] != 0)
            num = (-d0[sel, 0]) % p
            den = d1[sel, 0]
            g = (num * pow_mod_vec(den, p-2, p)) % p
            for gv in g.tolist():
                gam.add(gv)
                if len(gam) > budget: return True
        else:
            # need d0 + gamma d1 == 0 in all c comps. VECTORIZED: pick first comp t0 with d1!=0
            # per candidate row, gamma = -d0[t0]/d1[t0], then verify d0 + gamma*d1 == 0 in ALL c.
            dr0 = d0[cand]; dr1 = d1[cand]          # (M, c)
            if dr0.shape[0] == 0:
                return False
            nzmask = (dr1 % p) != 0                  # (M,c)
            has = nzmask.any(axis=1)
            dr0 = dr0[has]; dr1 = dr1[has]; nzmask = nzmask[has]
            if dr0.shape[0] == 0:
                return False
            t0 = nzmask.argmax(axis=1)               # first nonzero col per row
            rows = np.arange(dr0.shape[0])
            den = dr1[rows, t0]
            num = (-dr0[rows, t0]) % p
            gv = (num * pow_mod_vec(den, p-2, p)) % p   # (M,)
            # verify all c comps: d0 + gv*d1 == 0
            check = (dr0 + gv[:, None] * dr1) % p     # (M,c)
            good = (check == 0).all(axis=1)
            for v in np.unique(gv[good]).tolist():
                gam.add(v)
                if len(gam) > budget:
                    return True
        return False
    scanned = 0
    for R in combs:
        buf.append(R)
        if len(buf) >= CHUNK:
            if flush(buf):
                return p if heavy else budget + 1
            scanned += len(buf); buf = []
            if maxscan is not None and scanned >= maxscan:
                return ('CAP', len(gam))   # not the binder so far (<=budget after maxscan subsets)
    if flush(buf):
        return p if heavy else budget + 1
    return len(gam)

def pow_mod_vec(base, e, p):
    """Vectorized modular exponentiation base**e mod p, base int64 array."""
    base = base % p
    result = np.ones_like(base)
    b = base.copy()
    ee = e
    while ee > 0:
        if ee & 1:
            result = (result * b) % p
        b = (b * b) % p
        ee >>= 1
    return result

def run(n, k, primes, s_range, dirs):
    budget = n
    rho = k/n
    print(f"\n===== n={n} k={k} rho={rho:.4f} budget={budget} =====", flush=True)
    print(f"  Johnson/Plotkin proxy s*=2k-1={2*k-1} delta*=1/2+1/n={0.5+1/n:.4f}; floor 1-rho={1-rho:.4f}", flush=True)
    print(f"  {len(dirs)} dirs incl antipodal {(n//2,n//2-1)}", flush=True)
    print(f"  {'s':>3} {'r':>3} {'delta':>7} {'C(n,s)':>13}  " + "  ".join(f'maxI@p{i}' for i in range(len(primes))) + "  pindep verdict  binder", flush=True)
    setups = [(p, setup(n, p)) for p in primes]
    res = {}
    for s in s_range:
        r = n - s
        if s < k+1: continue
        delta = r/n
        per_p = []; per_arg = []
        for (p, mu) in setups:
            best = 0; arg = None
            for (a, b) in dirs:
                # FAR-coset validity: the far exponent x^b counts as a *far* direction only when
                # b < s (= n-r). For b >= s, x^b agrees with a deg<k codeword on the s points and
                # is NOT far -> the far-coset count over-counts (spurious "heavy"). Skip those.
                if b >= s:
                    continue
                I = incidence_vec(a, b, n, mu, k, p, s, budget)
                if I is None: continue
                v = I if I <= budget else budget+1
                if v > best:
                    best = v; arg = (a,b)
                    if best > budget: break
            per_p.append(best); per_arg.append(arg)
        pindep = "YES" if len(set(per_p))==1 else "MIX"
        verdict = "GOOD" if max(per_p) <= budget else "BAD"
        res[s] = max(per_p)
        print(f"  {s:>3} {r:>3} {delta:>7.4f} {comb(n,s):>13}  " + "  ".join(str(v).rjust(6) for v in per_p) + f"   {pindep}  {verdict}  {per_arg[0]}", flush=True)
    # CORRECT readout: delta* = sup{ delta=r/n : I(rung r) <= budget }. The far-line is BAD at the
    # DEEP band (large r); GOOD once r is small enough. delta* is the LARGEST GOOD r (= smallest
    # BAD r minus 1). The binding witness size s* = n - r*. Johnson+1rung is r*=n/2+1, s*=n/2-1.
    good_r = sorted([n - s for s in res if res[s] <= budget])   # GOOD rungs r
    bad_r = sorted([n - s for s in res if res[s] > budget])     # BAD rungs r
    if good_r:
        # delta* = largest GOOD r that is below all BAD r (contiguous good region from the top)
        if bad_r:
            rstar = max([r for r in good_r if r < min(bad_r)], default=None)
        else:
            rstar = max(good_r)
        if rstar is not None:
            sstar = n - rstar
            johnson_r = n//2 + 1
            tag = ("== JOHNSON+1rung (LOCKED)" if rstar == johnson_r else
                   ("CLIMB past Johnson toward floor!" if rstar > johnson_r else "below Johnson"))
            print(f"  >>> r* (largest GOOD below BAD) = {rstar}  delta* = {rstar/n:.4f}  s* = {sstar}", flush=True)
            print(f"  >>> Johnson+1rung r*={johnson_r} (s*={n//2-1}, delta*={0.5+1/n:.4f}); floor r*={int((1-rho)*n)} (delta*={1-rho:.4f}).  VERDICT: {tag}", flush=True)
    return res

if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--ns", default="16")
    ap.add_argument("--maxC", type=float, default=1e9)
    ap.add_argument("--full", action="store_true", help="full b-range direction set")
    ap.add_argument("--rlo", type=int, default=None, help="min rung r to test")
    ap.add_argument("--rhi", type=int, default=None, help="max rung r to test")
    args = ap.parse_args()
    KMAP = {16:4, 20:5, 24:6, 28:7, 32:8, 34:8, 36:9, 38:9, 40:10}
    for n in [int(x) for x in args.ns.split(",")]:
        k = KMAP[n]
        primes = [find_prime_cong1(n,200000), find_prime_cong1(n,700000)]
        m2 = n//2
        if args.full:
            dirs = [(a,b) for b in range(k,n) for a in range(k,n) if a!=b]
        else:
            dirs = []
            for d in [(m2,m2-1),(m2-1,m2),(m2,m2+1),(m2,m2-2),(m2,k),(k,m2)]:
                if d[0]!=d[1] and k<=d[0]<n and k<=d[1]<n: dirs.append(d)
            for b in [k,k+1]:
                for a in range(k,n):
                    if a!=b: dirs.append((a,b))
            seen=set(); dd=[]
            for d in dirs:
                if d not in seen: seen.add(d); dd.append(d)
            dirs=dd
        rlo = args.rlo if args.rlo is not None else 1
        rhi = args.rhi if args.rhi is not None else n-1
        # s = n - r; restrict to rung window [rlo,rhi] and over-determined s>=k+1, C<=maxC
        s_all = [s for s in range(k+1, n)
                 if comb(n,s) <= args.maxC and rlo <= (n-s) <= rhi]
        run(n, k, primes, s_all, dirs)
    print("\nALL DONE", flush=True)
