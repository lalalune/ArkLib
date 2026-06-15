#!/usr/bin/env python3
"""
RED-TEAM the claim that the BINDING (max-|S|) genuine direction is ALWAYS an even-symmetric
mu_2-coset CORE (excess=0), so R-thin (which bounds only excess) is prize-irrelevant.

Strategy: the claim only tested n=8,12,16 where d in {1,2,4,8} and there is essentially no
room for a genuine d>=2 ragged direction to bind. Push to n=24,32 (larger divisor lattice)
and measure, for the ACTUAL binding genuine direction:
   |S|, coset-core, ragged-excess, and whether the binding dir is even-symmetric.

ALSO test the central counterclaim directly: is there ANY genuine far direction whose
ragged EXCESS exceeds the core, with |S| >= sqrt(nk) (i.e. R-thin would actually bite and
the binding quantity is NOT the additive-energy core)?

Exact F_p arithmetic. Subset interpolation is C(n,k) which blows up; we cap k small.
"""
import itertools, math, sys
from sympy import isprime, factorint

def find_prime(n, want_min):
    p = max(want_min, n+1); r = p % n
    if r != 1: p += (1-r) % n
    while True:
        if p % n == 1 and isprime(p): return p
        p += n

def generator(p):
    fac = list(factorint(p-1).keys())
    for c in range(2, p):
        if all(pow(c,(p-1)//q,p) != 1 for q in fac): return c

def mu_n(p, n):
    g0 = generator(p); w = pow(g0,(p-1)//n,p)
    return [pow(w,j,p) for j in range(n)], w

def max_agreement_set(fv, xs, k, p, cap=None):
    """max over deg<k single codewords of agreement set. Returns (size, set). Exact subset interp."""
    n = len(xs)
    if k >= n: return n, set(range(n))
    best = k; bestS = set(range(k))
    cnt = 0
    for T in itertools.combinations(range(n), k):
        cnt += 1
        if cap and cnt > cap: break
        Tl = list(T)
        # build interpolating poly value at each x via Lagrange
        ag = set()
        # precompute denominators
        for j in range(n):
            xj = xs[j]; val = 0
            for t in Tl:
                term = fv[t]; xt = xs[t]
                for s in Tl:
                    if s == t: continue
                    term = (term * ((xj - xs[s]) % p)) % p
                    term = (term * pow((xt - xs[s]) % p, p-2, p)) % p
                val = (val + term) % p
            if val == fv[j] % p: ag.add(j)
        if len(ag) > best:
            best = len(ag); bestS = ag
            if best == n: return n, bestS
    return best, bestS

def coset_core(Sidx, n):
    """largest union of full mu_{d'}-cosets contained in S, over divisors d'>1.
       mu_{d'} coset of index i = {(i + (n//d')*t) mod n : t in range(d')}, size d'."""
    Sset = set(Sidx); best = 0; bestd = 1
    divs = [d for d in range(2, n+1) if n % d == 0]
    for dp in divs:
        step = n // dp
        covered = 0
        for i in range(step):
            coset = set((i + step*t) % n for t in range(dp))
            if coset <= Sset: covered += len(coset)
        if covered > best: best = covered; bestd = dp
    return best, bestd

def is_correlated(a, b, n, k):
    nh = n // 2
    return (a % nh < k) and (b % nh < k)

def even_symmetric_dir(a, b, n):
    """direction whose agreement set is forced antipodal-closed: a,b both even => x->-x preserves x^a,x^b."""
    return (a % 2 == 0) and (b % 2 == 0)

def gamma_set(p, sample):
    G = list(range(1, p))
    if len(G) > sample:
        step = max(1,(p-1)//sample); G = list(range(1,p,step))
    return G

def analyze(n, k, gamma_sample=60, subset_cap=None):
    p = find_prime(n, n*40+1)
    xs, w = mu_n(p, n)
    m = (p-1)//n; rho = k/n
    print(f"\n### n={n} k={k} p={p} m={m} rho={rho:.3f} sqrt(nk)={math.sqrt(n*k):.2f} k+1={k+1} ###", flush=True)
    # iterate all directions; for each compute best over sampled gamma of (|S|, core, excess)
    recs = []
    for a in range(k, n):
        for b in range(0, a):
            d = math.gcd(a-b, n)
            corr = is_correlated(a, b, n, k)
            best_size = 0; best_core = 0; best_exc = 0; best_g = None; best_d2 = 1
            best_exc_size = 0; best_exc_exc = 0  # for excess-tracking
            for g in gamma_set(p, gamma_sample):
                fv = [(pow(xs[i],a,p) + g*pow(xs[i],b,p)) % p for i in range(n)]
                sz, S = max_agreement_set(fv, xs, k, p, cap=subset_cap)
                if sz == n: continue  # saturated = degenerate
                core, cd = coset_core(S, n)
                exc = sz - core
                if sz > best_size:
                    best_size = sz; best_core = core; best_exc = exc; best_g = g; best_d2 = cd
                if exc > best_exc_exc:
                    best_exc_exc = exc; best_exc_size = sz
            recs.append((a, b, d, corr, even_symmetric_dir(a,b,n),
                         best_size, best_core, best_exc, best_d2, best_exc_exc, best_exc_size))
    # genuine = not correlated, not saturated
    genuine = [r for r in recs if not r[3] and r[5] > 0]
    if not genuine:
        print("  no genuine directions"); return
    # The binding direction = max |S| among genuine
    genuine.sort(key=lambda r: -r[5])
    print("  TOP genuine directions by |S|  (a,b,d, evenSym, |S|, core, excess, coreGrp):")
    for r in genuine[:8]:
        a,b,d,corr,ev,sz,core,exc,cd,_,_ = r
        print(f"    a={a:>2} b={b:>2} d={d:>2} even={int(ev)} |S|={sz} core={core}(mu_{cd}) excess={exc}"
              f"  sqrt(nk)={math.sqrt(n*k):.1f}", flush=True)
    binding = genuine[0]
    print(f"  >>> BINDING genuine dir: a={binding[0]} b={binding[1]} d={binding[2]} even={int(binding[4])} "
          f"|S|={binding[5]} core={binding[6]} excess={binding[7]}")
    # The MAX-EXCESS genuine direction (where R-thin would bite):
    gx = max(genuine, key=lambda r: r[9])
    print(f"  >>> MAX-EXCESS genuine dir: a={gx[0]} b={gx[1]} d={gx[2]} max-excess={gx[9]} "
          f"(at |S|={gx[10]});  binding |S|={binding[5]}")
    # decisive: is there a genuine dir with excess > core AND |S| >= sqrt(nk)?
    bite = [r for r in genuine if r[7] > r[6] and r[5] >= math.sqrt(n*k)]
    print(f"  >>> #genuine dirs where EXCESS>core AND |S|>=sqrt(nk) (R-thin bites & dominant): {len(bite)}")
    for r in bite[:5]:
        print(f"        a={r[0]} b={r[1]} d={r[2]} |S|={r[5]} core={r[6]} excess={r[7]}")

if __name__ == "__main__":
    # small for sanity (corroborate claim)
    analyze(8, 2)
    analyze(12, 3)
    analyze(16, 4)
    # PUSH: larger divisor lattice; cap subset enumeration where C(n,k) is big
    analyze(24, 3, gamma_sample=40, subset_cap=4000)   # C(24,3)=2024 fine
    print("DONE", flush=True)
