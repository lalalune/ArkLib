#!/usr/bin/env python3
"""
Door-(iv) Lane 1 — the 2-adic phase-alignment RECURSION as a coherence-PRODUCT.

Object. mu_n = order-n (n=2^a) subgroup of F_p*, eta_b = sum_{y in mu_n} e_p(b*y).
The proven prize-equivalent target is the half-mass H(n) = max_b (||A|| + ||B||) where
A,B are the two half-period sums over the index-2 cosets of mu_{n/2} < mu_n.

Single-level coherence rho(b) = ||A+B|| / (||A||+||B||) = |eta_b| / (||A||+||B||) is proven
to be =1 at the prize-worst b* (collinear, same-ray).  THIS PROBE asks the DYADIC-TOWER
question the single-level result does NOT address:

  Walk the chain  mu_n  ⊃ mu_{n/2} ⊃ ... ⊃ mu_1 = {1}.
  At each level the order-2^j period splits into two order-2^{j-1} coset sub-sums.
  Define the per-LEVEL worst-coherence telescoping:
     |eta_b| = ||sum over mu_n|| , and recursively at level j the 2^{a-j} pieces
     of size 2^j combine.  The per-level coset-half coherence
        rho_j(b) = || (piece_+ + piece_-) || / ( ||piece_+|| + ||piece_-|| )
     averaged/maxed over the 2^{a-j} pairs at level j.

  Q1 (TELESCOPE): is   |eta_{b*}| = ( prod_j rho_j ) * 2^a * (avg single-term modulus) ?
      i.e. does the coset-half coherence chain-multiply down to the L1 term mass?
  Q2 (FORCED-1): at the GLOBAL worst b*, is EACH level coherence rho_j -> 1, or is there
      per-level slack (rho_j bounded below 1-c) a product bound could exploit for sqrt-cancel?
  Q3 (THINNESS): compare the worst-b per-level coherence profile to a random b and to a
      random same-size additive set; is any per-level slack thinness-essential?

If every per-level rho_j is forced ~1 at b* (telescoping COLLAPSE), then the 2-adic
phase-alignment recursion is a DEAD lever (no per-level slack to multiply) — a Lane-3
constraint lemma.  If real per-level slack survives adversarial re-check, formalize the
observed fact (Lane 1).

RULES: PROPER mu_n only (n < p-1), p >> n^3, structured odd-m primes, multiple primes,
NEVER n=q-1, EXACT complex arithmetic via cmath with integer phase indices.
"""
import cmath, math, random

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def find_prime(n, beta):
    """smallest prime p = k*n+1 with p ~ n^beta and p >> n^3 (proper subgroup mu_n)."""
    target = int(round(n**beta))
    k0 = max(2, target // n)
    for dk in range(0, 400000):
        for k in (k0+dk, k0-dk):
            if k < 2: continue
            p = k*n + 1
            if p > n*n*n and is_prime(p):  # enforce p >> n^3
                return p
    return None

def subgroup(p, n):
    """order-n subgroup mu_n of F_p*, returned as a list in 'powers of g' order g^0..g^{n-1}."""
    # find element of order exactly n: take a generator^((p-1)/n)
    # find a primitive root g
    def order(a):
        o=1; x=a%p
        while x!=1:
            x=x*a%p; o+=1
            if o>p: return None
        return o
    # primitive root search
    g=None
    for cand in range(2,p):
        # quick: check g^((p-1)/q)!=1 for prime q | p-1
        m=p-1; ok=True
        # factor m lightly
        qs=set(); mm=m; d=2
        while d*d<=mm:
            while mm%d==0: qs.add(d); mm//=d
            d+=1
        if mm>1: qs.add(mm)
        for q in qs:
            if pow(cand,m//q,p)==1: ok=False; break
        if ok: g=cand; break
    h=pow(g,(p-1)//n,p)  # order n
    elts=[pow(h,j,p) for j in range(n)]
    return elts, h

def e_p(t, p):
    return cmath.exp(2j*math.pi*(t % p)/p)

def eta(b, mu, p):
    return sum(e_p(b*y, p) for y in mu)

def coherence(vecs):
    """rho = ||sum|| / sum||.|| for a list of complex pieces."""
    s = sum(vecs)
    denom = sum(abs(v) for v in vecs)
    if denom == 0: return 1.0
    return abs(s)/denom

def tower_profile(b, mu, h, p, n):
    """
    Walk dyadic tower. mu is g^0..g^{n-1} (h = generator of mu, order n).
    At level j (subgroup order 2^j), the order-n period is sum over n terms; group them
    into 2^{a-j} consecutive blocks of size 2^j in the cyclic index, each block = a coset
    of mu_{2^j}.  Coherence at level j = how the 2^{a-j} block-sums (the order-2^j
    sub-periods) combine: we report, per level j (the SPLIT mu_{2^{j}} -> two mu_{2^{j-1}}):
      for each of the 2^{a-j} cosets of mu_{2^j}, its two mu_{2^{j-1}} half-sums A,B and
      rho = ||A+B||/(||A||+||B||).  Report the WORST (min) and MEAN rho over the cosets.
    """
    a = n.bit_length()-1  # n = 2^a
    # term phases: phase of term for index i is e_p(b * mu[i]); the subgroup index order
    # is g^i.  mu_{2^j} = { g^{i*(n/2^j)} } = indices that are multiples of n/2^j.
    terms = [e_p(b*mu[i], p) for i in range(n)]
    levels = []
    # level j from a down to 1: split order-2^j coset into two order-2^{j-1}
    for j in range(a, 0, -1):
        sz = 1 << j            # coset size at this level (order of mu_{2^j})
        half = sz >> 1         # mu_{2^{j-1}}
        step = n // sz         # there are 'step' cosets of mu_{2^j} of size sz
        # mu_{2^j} as index set = multiples of step: {0, step, 2*step, ...} has size sz
        # its cosets are r + step*{0..sz-1} for r in 0..step-1
        rhos = []
        for r in range(step):
            idx = [(r + step*t) % n for t in range(sz)]
            # split into two mu_{2^{j-1}} cosets: even/odd t  -> sub-step = 2*step
            A = sum(terms[(r + step*t) % n] for t in range(0, sz, 2))
            B = sum(terms[(r + step*(t)) % n] for t in range(1, sz, 2))
            rhos.append(coherence([A, B]))
        levels.append((j, min(rhos), sum(rhos)/len(rhos)))
    return levels

def run(n, beta, n_primes=2, seed=0):
    random.seed(seed)
    out = []
    primes = []
    # gather a few structured primes p = k*n+1, p>>n^3
    target = int(round(n**beta)); k0 = max(2, target//n); found=0; dk=0
    seen=set()
    while found < n_primes and dk < 400000:
        for k in (k0+dk, k0-dk):
            if k<2: continue
            p=k*n+1
            if p>n*n*n and is_prime(p) and p not in seen:
                seen.add(p); primes.append(p); found+=1
                if found>=n_primes: break
        dk+=1
    for p in primes:
        mu, h = subgroup(p, n)
        # global worst-b scan over a representative set of b (full F_p* too big for huge p;
        # mu_n-coset blind => scan ONE rep per (mu_n ∪ -mu_n) orbit by sampling many b and
        # also do a dense small-b scan; take global max).
        best_b=None; best_mag=-1
        # dense scan of b in 1..min(p-1, cap); plus random sample for large p
        cap = min(p-1, 60000)
        cands = list(range(1, cap+1))
        if p-1 > cap:
            cands += [random.randrange(1,p) for _ in range(40000)]
        for b in cands:
            m = abs(eta(b, mu, p))
            if m>best_mag: best_mag=m; best_b=b
        # tower profile at worst b
        prof = tower_profile(best_b, mu, h, p, n)
        prod_min = 1.0; prod_mean=1.0
        for (j,mn,mean) in prof:
            prod_min*=mn; prod_mean*=mean
        l1 = sum(abs(e_p(best_b*y,p)) for y in mu)  # = n (each term unit modulus)
        # telescope check: |eta| =? (prod of level rho) * L1   -- using the per-level
        # coherence as defined; report ratio
        # random-b control
        rb = random.randrange(1,p)
        rprof = tower_profile(rb, mu, h, p, n)
        rmin = min(mn for (_,mn,_) in rprof)
        wmin = min(mn for (_,mn,_) in prof)
        out.append(dict(p=p, best_b=best_b, best_mag=best_mag, sqrt_n=math.sqrt(n),
                        l1=l1, prof=prof, prod_min=prod_min, prod_mean=prod_mean,
                        worst_level_min_rho=wmin, rand_level_min_rho=rmin,
                        eta_over_l1=best_mag/l1))
    return out

if __name__ == "__main__":
    print("="*100)
    print("Door-(iv) dyadic coherence-tower PRODUCT probe — per-level coset-half coherence at worst b")
    print("PROPER mu_n, p>>n^3, structured primes p=k*n+1, never n=q-1")
    print("="*100)
    for n in (8, 16, 32):
        for beta in (4.0, 4.5):
            res = run(n, beta, n_primes=2, seed=12345+n)
            for r in res:
                a = n.bit_length()-1
                profstr = " ".join(f"j{j}:min{mn:.3f}/mean{mean:.3f}" for (j,mn,mean) in r['prof'])
                print(f"\nn={n} (a={a}) p={r['p']} (p/n^3={r['p']/n**3:.1f})  worst_b={r['best_b']}")
                print(f"  |eta_b*|={r['best_mag']:.4f}  sqrt(n)={r['sqrt_n']:.3f}  |eta|/n={r['eta_over_l1']:.4f}  (L1=n={r['l1']:.0f})")
                print(f"  per-level coherence: {profstr}")
                print(f"  PROD of per-level MIN rho = {r['prod_min']:.4f}   PROD of per-level MEAN rho = {r['prod_mean']:.4f}")
                print(f"  worst-b min-over-levels rho = {r['worst_level_min_rho']:.4f}   random-b min-over-levels rho = {r['rand_level_min_rho']:.4f}")
    print("\n" + "="*100)
    print("VERDICT KEYS:")
    print("  Q1 telescope: does some product of per-level coherences track |eta|/n? (compare prod vs eta_over_l1)")
    print("  Q2 forced-1: is worst-b min-over-levels rho ~1 (collapse, no slack) or <1 (slack to exploit)?")
    print("  Q3 thinness: worst-b vs random-b per-level min rho — is any slack worst-b-selected?")
