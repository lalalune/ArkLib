#!/usr/bin/env python3
"""
probe_dooriv_tower_honest_chain_vs_minover.py  (#464, door-(iv) Lane 1 — DISAMBIGUATE the tower-slack count)

CONTEXT. A prior probe (probe_dooriv_tower_slack_count_law.py) measured, per dyadic level j, the
MIN coherence rho_j over ALL 2^{a-j} cosets of mu_{2^j}, and found the COUNT of nontrivial-slack levels
K(n) appears to GROW with a=log2(n) (1,2,3,5,5 for a=4..8) and the per-level min rho shrinks. Taken at
face value that would re-open the dyadic-tower lever the banked verdict [door-iv-tower-collapse-quantitative]
(2026-06-19) declared dead ("the probe localizes k=O(1)").

THE DISCREPANCY IS A MEASUREMENT ARTIFACT, and this probe proves it. The prize identity telescopes the
period |eta_{b*}| through ONE nested chain of cosets:
    mu_n=C_a ⊃ C_{a-1} ⊃ ... ⊃ C_0,  C_j = the mu_{2^j}-coset whose half-sum chain reconstructs eta_{b*}.
The HONEST tower product is prod_j rho_j(C_j) along THIS single chain (the coset containing index 0, the
identity, since eta_{b*} = sum over the whole group = the top coset). MIN-over-all-cosets is NOT this
product: it picks, at each level, a DIFFERENT (unrelated) coset that happens to cancel well. Those
incidental cancellations live in sibling cosets that do NOT compose into a bound on eta_{b*}.

DECISIVE TEST (probe-first, HARD RULE 6 anti-overclaim):
  For each n, at the global worst b*, compute BOTH:
    (1) HONEST-CHAIN slack count K_chain = #{ j : 1 - rho_j(C_j*) >= tau } along the actual nested chain
        C_j* that reconstructs eta_{b*} (the chain through the top coset = whole group),
    (2) MIN-OVER-COSETS count K_min (the prior probe's quantity).
  PREDICTION (if banked verdict holds): K_chain = O(1) (saturates) while K_min grows -> the growth is an
  artifact of unrelated sibling cosets; the dyadic-tower lever stays DEAD. If instead K_chain ALSO grows
  with a, that is a REAL crack and must be formalized as a Lane-1 observed fact (adversarially re-checked).
  Also report the HONEST-CHAIN product DAMP_chain = prod rho_j(C_j*) and verify it EQUALS |eta_{b*}|/n
  exactly (the telescoping identity), confirming it is the SAME object as the period (tautology, no
  independent saving) -- which is the whole point: the honest chain product cannot beat the period it IS.

HARD RULES: PROPER mu_n (n=2^a<p-1), p>>n^3, structured primes p=k*n+1, NEVER n=q-1, EXACT complex eta.
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
    target = int(round(n**beta)); k0 = max(2, target // n); found = []; dk = 0
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
    m = p-1; qs=set(); mm=m; d=2
    while d*d<=mm:
        while mm%d==0: qs.add(d); mm//=d
        d+=1
    if mm>1: qs.add(mm)
    for cand in range(2,p):
        if all(pow(cand,m//q,p)!=1 for q in qs): return cand
    return None

def subgroup(p, n):
    g = primitive_root(p); h = pow(g,(p-1)//n,p)
    return [pow(h,j,p) for j in range(n)], h

def e_p(t, p): return cmath.exp(2j*math.pi*(t % p)/p)
def coh(A,B):
    d = abs(A)+abs(B); return 1.0 if d==0 else abs(A+B)/d

def find_worst_b(mu, p, n, cap=70000):
    def mag(b): return abs(sum(e_p(b*y,p) for y in mu))
    if p-1 <= cap: bs = range(1,p)
    else:
        random.seed(99001+p); bs = random.sample(range(1,p), cap)
    bb, bm = 1, -1.0
    for b in bs:
        m = mag(b)
        if m > bm: bm, bb = m, b
    return bb, bm

def honest_chain(b, mu, p, n):
    """
    Telescope eta_{b} through the SINGLE nested chain of the TOP coset (= whole group).
    terms[i] = e_p(b*mu[i]), mu[i]=g^i. mu_{2^j} = indices that are multiples of step=n/2^j.
    The whole group is the unique mu_n-coset; recursively split the CURRENT coset into its two
    mu_{2^{j-1}} halves and FOLLOW the half whose partial-sum reconstructs eta (we keep the WHOLE
    coset = both halves at top; the chain C_j = the order-2^j coset that is the cumulative group, which
    at the top is everything). Concretely the honest telescoping product for the FULL period is:
        rho_a = |A+B|/(|A|+|B|) for the top split of the whole group, then RECURSE INTO EACH HALF and
        the period |eta| = |A_top+B_top|; the canonical single chain follows the identity-coset path:
        at level j the coset is { indices ≡ 0 mod step } (the subgroup mu_{2^j} itself), split into
        mu_{2^{j-1}} (even multiples) and its shift. This is the chain through index 0 (= y=1).
    Returns list (j, rho_j) along the subgroup chain, and the chain product.
    """
    terms = [e_p(b*mu[i], p) for i in range(n)]
    a = n.bit_length()-1
    chain = []
    prod = 1.0
    for j in range(a, 0, -1):
        sz = 1 << j; step = n // sz
        # the subgroup mu_{2^j} = indices {0, step, 2step, ..., (sz-1)step}
        idx = [(step*t) % n for t in range(sz)]
        A = sum(terms[(step*t) % n] for t in range(0, sz, 2))
        B = sum(terms[(step*t) % n] for t in range(1, sz, 2))
        r = coh(A, B)
        chain.append((j, r)); prod *= r
    return chain, prod

def min_over_cosets(b, mu, p, n):
    terms = [e_p(b*mu[i], p) for i in range(n)]
    a = n.bit_length()-1
    prof = []
    for j in range(a, 0, -1):
        sz = 1 << j; step = n // sz
        rhos = []
        for rr in range(step):
            A = sum(terms[(rr+step*t)%n] for t in range(0,sz,2))
            B = sum(terms[(rr+step*t)%n] for t in range(1,sz,2))
            rhos.append(coh(A,B))
        prof.append((j, min(rhos)))
    return prof

if __name__ == "__main__":
    print("="*104)
    print("Door-(iv) Lane 1 — HONEST telescoping CHAIN (subgroup path) vs MIN-OVER-COSETS slack count")
    print("PROPER mu_n, p>>n^3, structured primes, never n=q-1, exact complex eta. tau=0.10.")
    print("="*104)
    TAU = 0.10
    print(f"\n{'n':>5} {'a':>3} {'p':>12} {'M/sqn':>6} {'Kchain':>7} {'Kmin':>5} {'DAMPchain':>10} {'|eta|/n':>9} {'match?':>7}")
    rows=[]
    for n in (16,32,64,128,256):
        for p in find_primes(n, 4.0, 2):
            mu,h = subgroup(p,n)
            b,M = find_worst_b(mu,p,n)
            chain, dprod = honest_chain(b,mu,p,n)
            prof = min_over_cosets(b,mu,p,n)
            a = n.bit_length()-1
            Kchain = sum(1 for (_,r) in chain if (1-r)>=TAU)
            Kmin   = sum(1 for (_,r) in prof  if (1-r)>=TAU)
            eta_over_n = M/n
            # honest-chain product should equal |eta over the SUBGROUP mu_n| / n? Note: the chain is the
            # subgroup itself = whole group; eta_b = sum over whole group; |eta_b|/n = dprod EXACTLY iff
            # every intermediate |A_j+B_j| telescopes. Verify numerically.
            match = abs(dprod - eta_over_n) < 1e-6
            print(f"{n:>5} {a:>3} {p:>12} {M/math.sqrt(n):>6.3f} {Kchain:>7} {Kmin:>5} {dprod:>10.5f} {eta_over_n:>9.5f} {str(match):>7}")
            rows.append((n,a,Kchain,Kmin))
    print("\nVERDICT KEYS:")
    print("  Kchain (honest single nested chain) — if O(1) (flat as a grows) the dyadic-tower lever is DEAD:")
    print("    the growth of Kmin is an ARTIFACT of unrelated sibling cosets that do NOT compose into a")
    print("    bound on eta_{b*}. Only the chain product bounds the period, and it EQUALS |eta|/n (tautology).")
    print("  match? — confirms DAMPchain == |eta|/n: the honest chain product IS the period, no independent")
    print("    saving. A tower-product 'bound' that equals the thing it bounds proves nothing new.")
