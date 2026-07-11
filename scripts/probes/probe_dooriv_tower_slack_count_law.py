#!/usr/bin/env python3
"""
probe_dooriv_tower_slack_count_law.py  (#464, door-(iv) Lane 1 — the ONE surviving tower-collapse crack)

The dyadic coherence-tower is ALREADY collapsed + banked (1acd54023, _DoorIVCoherenceTowerCollapse):
upper levels pin at coherence rho_j ~ 1, so the per-level coherence PRODUCT equals the product over the
nontrivial-slack levels only. The banked VERDICT explicitly names the TWO (and only two) surviving
escape hatches for any dyadic-tower attack to deliver a sqrt(log n)-many damping factor:

  > "A successful door-(iv) coherence-tower attack must prove EITHER that the number of genuinely
  >  nontrivial levels GROWS with n OR that the bottom factors themselves SHRINK with n."

The original tower probe ran n=8,16,32 and measured worst-b min-over-levels rho. It did NOT extract,
as a FUNCTION OF n, the decisive quantities:
  (1) K(n,tau) = #{ levels j : worst-coset slack (1 - rho_j) >= tau } at the GLOBAL worst b*.
      A successful product attack needs K(n) ~ log2(n) = a (slack at a constant FRACTION of levels).
      If K(n) = O(1) (saturates), escape hatch (1) is DEAD.
  (2) bottomMinRho(n) = the smallest per-coset rho_j over the bottom region, as n grows.
      A successful attack needs bottomMinRho(n) -> 0 (factors shrink). If it is bounded below by a
      constant c>0, escape hatch (2) is DEAD.
  (3) DAMP(n) = prod over levels of (worst-coset rho_j at b*) -- the actual achievable tower damping.
      Compare DAMP(n) to the rho_needed = sqrt(n log(p/n))/n (what the trivial L1 ceiling H<=n needs).
      If DAMP(n) does NOT decay like a negative power of n, the product route cannot reach sqrt-cancel.

DECONFLICTION (distinct from EVERY prior tower/rho probe):
  * coherence_tower_product: measured per-level min/mean rho + telescope at n=8,16,32. Did NOT extract
    K(n) slack-COUNT scaling or bottomMinRho(n) scaling -- the two NAMED open hatches.
  * worstb_coherence_deficit_law: single-LEVEL (1-rho(b*)) deficit scaling. NOT the per-LEVEL tower count.
  * worstb_plateau / worstb_nesting / non-nested: argmax-IDENTITY recursion + extreme-value tail. Different.
This probe measures EXACTLY the K(n) and bottomMinRho(n) scaling laws the banked verdict left open.

HARD RULES honored: PROPER mu_n (n = 2^a, n < p-1), p >> n^3 (multiple structured primes p=k*n+1),
NEVER n=q-1, EXACT complex arithmetic (cmath, integer phase indices), full F_p* worst-b scan for
small n then sampled for large n. probe-first; formalize a kernel ONLY if a real, adversarially-rechecked
structure survives. A clean K(n)=O(1) + bottomMinRho>=c result is a REFUTATION-with-mechanism (HARD RULE 4)
that LOCKS both named escape hatches shut -> closes the dyadic-tower lever fully. CORE stays OPEN regardless.
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

def find_primes(n, beta, count):
    """`count` smallest primes p = k*n+1 with p ~ n^beta and p >> n^3 (proper subgroup mu_n)."""
    target = int(round(n**beta))
    k0 = max(2, target // n)
    found = []
    dk = 0
    while len(found) < count and dk < 2000000:
        for k in (k0+dk, k0-dk):
            if k < 2: continue
            p = k*n + 1
            if p > n*n*n and is_prime(p) and p not in found:
                found.append(p)
                if len(found) >= count: break
        dk += 1
    return found

def primitive_root(p):
    m = p-1
    qs = set(); mm = m; d = 2
    while d*d <= mm:
        while mm % d == 0: qs.add(d); mm //= d
        d += 1
    if mm > 1: qs.add(mm)
    for cand in range(2, p):
        if all(pow(cand, m//q, p) != 1 for q in qs):
            return cand
    return None

def subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)          # element of order exactly n
    return [pow(h, j, p) for j in range(n)], h

def e_p(t, p):
    return cmath.exp(2j*math.pi*(t % p)/p)

def coherence(A, B):
    denom = abs(A) + abs(B)
    return 1.0 if denom == 0 else abs(A+B)/denom

def tower_levels(b, mu, p, n):
    """
    Per-level coset-half coherence at frequency b, walking mu_n ⊃ mu_{n/2} ⊃ ... ⊃ mu_1.
    Index convention (validated in coherence_tower_product): mu[i] = g^i (g order n);
    mu_{2^j} = indices that are multiples of step = n/2^j. Cosets of mu_{2^j}: r + step*{0..2^j-1}.
    Split each into two mu_{2^{j-1}} halves (even/odd t). Report per level j: WORST (min) rho over cosets.
    Returns list of (j, worst_rho_over_cosets) for j = a..1.
    """
    a = n.bit_length() - 1
    terms = [e_p(b*mu[i], p) for i in range(n)]
    levels = []
    for j in range(a, 0, -1):
        sz = 1 << j
        step = n // sz
        rhos = []
        for r in range(step):
            A = sum(terms[(r + step*t) % n] for t in range(0, sz, 2))
            B = sum(terms[(r + step*t) % n] for t in range(1, sz, 2))
            rhos.append(coherence(A, B))
        levels.append((j, min(rhos)))
    return levels

def find_worst_b(mu, p, n, full_scan_cap=70000):
    """worst b = argmax_b |eta_b| over b in 1..p-1 (full scan if p-1 small, else sample)."""
    def mag(b):
        return abs(sum(e_p(b*y, p) for y in mu))
    if p - 1 <= full_scan_cap:
        bs = range(1, p)
    else:
        random.seed(99001 + p)
        bs = random.sample(range(1, p), full_scan_cap)
    best_b, best_m = 1, -1.0
    for b in bs:
        m = mag(b)
        if m > best_m:
            best_m, best_b = m, b
    return best_b, best_m

def run_one(n, beta, seed=0):
    res = []
    primes = find_primes(n, beta, 2)
    for p in primes:
        mu, h = subgroup(p, n)
        b_star, M = find_worst_b(mu, p, n)
        levels = tower_levels(b_star, mu, p, n)
        a = n.bit_length() - 1
        # DAMP = product of per-level worst rho (the achievable tower damping at b*)
        damp = 1.0
        for (_, r) in levels: damp *= r
        # K(n,tau): count of levels with worst-coset slack >= tau
        def Kcount(tau): return sum(1 for (_, r) in levels if (1.0 - r) >= tau)
        # bottom region = lowest 3 levels (j=1,2,3) per the banked "fixed-width bottom slack" framing
        bottom = [r for (j, r) in levels if j <= 3]
        bottomMinRho = min(bottom) if bottom else 1.0
        rho_needed = math.sqrt(n * math.log(p/n)) / n   # what trivial L1 ceiling H<=n would need
        res.append(dict(n=n, a=a, p=p, beta=beta, b_star=b_star, M=M, M_over_sqrtn=M/math.sqrt(n),
                        levels=levels, damp=damp,
                        K_005=Kcount(0.05), K_010=Kcount(0.10), K_020=Kcount(0.20),
                        bottomMinRho=bottomMinRho, rho_needed=rho_needed))
    return res

if __name__ == "__main__":
    print("="*108)
    print("Door-(iv) Lane 1 — TOWER SLACK-COUNT LAW: does K(n) grow ~log2(n) or saturate O(1)?")
    print("                   and does bottomMinRho(n) shrink to 0 or stay bounded below?")
    print("PROPER mu_n (n=2^a < p-1), p >> n^3, structured primes p=k*n+1, never n=q-1, exact complex eta.")
    print("="*108)
    rows = []
    for n in (16, 32, 64, 128, 256):
        beta = 4.0
        for r in run_one(n, beta, seed=12345+n):
            a = r['a']
            prof = " ".join(f"j{j}:{rho:.3f}" for (j, rho) in r['levels'])
            print(f"\nn={n:>4} (a={a}) p={r['p']} (p/n^3={r['p']/n**3:.1f})  worst_b={r['b_star']}")
            print(f"  M=|eta_b*|={r['M']:.4f}  M/sqrt(n)={r['M_over_sqrtn']:.3f}  rho_needed(L1 ceiling)={r['rho_needed']:.5f}")
            print(f"  per-level WORST rho (j=a..1): {prof}")
            print(f"  DAMP=prod(worst rho)={r['damp']:.5f}   bottomMinRho(j<=3)={r['bottomMinRho']:.4f}")
            print(f"  K(slack>=0.05)={r['K_005']}/{a}   K(>=0.10)={r['K_010']}/{a}   K(>=0.20)={r['K_020']}/{a}")
            rows.append(r)
    print("\n" + "="*108)
    print("SCALING SUMMARY (one row per (n,p)):")
    print(f"{'n':>5} {'a':>3} {'p':>12} {'M/sqrtn':>8} {'DAMP':>8} {'botMinRho':>10} {'K.05':>5} {'K.10':>5} {'K.20':>5} {'rho_need':>9}")
    for r in rows:
        print(f"{r['n']:>5} {r['a']:>3} {r['p']:>12} {r['M_over_sqrtn']:>8.3f} {r['damp']:>8.4f} "
              f"{r['bottomMinRho']:>10.4f} {r['K_005']:>5} {r['K_010']:>5} {r['K_020']:>5} {r['rho_needed']:>9.5f}")
    print("\nVERDICT KEYS:")
    print("  ESCAPE-HATCH-1 (count grows): K(n) vs a=log2(n). If K(n)/a -> const>0, slack at const FRACTION")
    print("    of levels => product route ALIVE. If K(n)=O(1) (column flat as n,a grow), HATCH-1 DEAD.")
    print("  ESCAPE-HATCH-2 (factors shrink): bottomMinRho(n). If -> 0, HATCH-2 ALIVE. If bounded below, DEAD.")
    print("  Cross-check: DAMP(n) vs rho_needed. DAMP must FALL BELOW rho_needed (and keep falling like a")
    print("    negative power of n) for the tower product to even in principle reach sqrt(n log)-cancellation.")
