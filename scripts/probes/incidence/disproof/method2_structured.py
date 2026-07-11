"""
method2_structured.py — METHOD 2: exact lists of the campaign's STRUCTURED candidate words,
placed on the proximity window, with growth across n.

GOAL (falsify-first): the floor conjecture says smooth-domain RS lists are SMALL (<= budget ~ q*eps*
~ n in the prize regime) for ALL words at WINDOW-INTERIOR radii (rho*n < a < sqrt(rho)*n).
To DISPROVE it we need ONE structured word whose EXACT list EXCEEDS ~n at an interior radius and
GROWS faster than ~n across n=8,16,32.

This probe builds the candidate "bad" words the campaign flagged and computes, for each:
  - its EXACT list(w, a) at every window-INTERIOR agreement a,
  - whether list > n  (super-budget) at any interior a,
  - the growth of (max-interior-list) across n.

Construction families:
  (a) COSET-UNION words: w is constant on each mu_d-coset (d=2^j | n) -- the all-zero e-symm
      target / dyadic structure (O158). Value chosen so the word matches a structured codeword
      on a coset union. We test: constant-on-cosets, indicator-of-one-coset (lifted to a field
      value), and the "codeword restricted to a coset union, garbage elsewhere" form.
  (b) e2=0 OVER-DETERMINED census words: words whose forced t-core has e_2(core)=0 (the
      over-determined #bad ~ n^2/4 family). We realize them as eval of a codeword PLUS a
      perturbation supported on an e2=0 core, or directly as words built to share many
      codewords through an e2=0 incidence structure.
  (c) SUBFIELD / FROBENIUS words: w_i = (codeword(x_i))^p-style / values pinned to the prime
      subfield, and the multiplicative-subgroup-indicator words.

Exact modular arithmetic only. Reuses fastlist's verified exact counter.
"""
import sys, itertools, math, json, os, random
sys.path.insert(0, '/home/nubs/Git/ArkLib/scripts/probes/incidence/disproof')
from maxlist_core import find_mun, eval_poly, interp_poly, agreement
from fastlist import Field, precompute_subsets, precompute_lagrange, list_count_fast


# ---------------- window helpers ----------------
def interior_radii(n, rho):
    cap = rho * n
    john = math.sqrt(rho) * n
    return [a for a in range(1, n + 1) if cap < a < john]


def divisors_pow2(n):
    """d = 2^j with 1 < d < n that divide n (proper sub-subgroup orders mu_d)."""
    out = []
    d = 2
    while d < n:
        if n % d == 0:
            out.append(d)
        d *= 2
    return out


# ---------------- construction (a): coset-union words ----------------
def coset_index_partition(F, d):
    """Partition index set 0..n-1 into mu_d cosets. mu_d = <g^(n/d)>; coset of i = i mod (n/d).
    Returns list of index-lists, one per coset (there are n/d cosets each of size d)."""
    n = F.n
    step = n // d          # number of cosets
    parts = [[] for _ in range(step)]
    for i in range(n):
        parts[i % step].append(i)
    return parts


def make_coset_words(F, rng):
    """Family (a). Yield (label, w) candidate words built from mu_d-coset structure.
    The campaign's 'coset-union' bad word = the all-zero e-symm target: a word that is
    CONSTANT on each mu_d coset. We also try: a genuine codeword evaluated then quantized to
    be coset-constant, and the indicator-of-coset-union word."""
    q, n, k = F.q, F.n, F.k
    out = []
    for d in divisors_pow2(n):
        parts = coset_index_partition(F, d)   # n/d cosets of size d
        ncos = len(parts)
        # (a1) constant-per-coset with random field constants
        for trial in range(3):
            cvals = [rng.randrange(q) for _ in range(ncos)]
            w = [0] * n
            for c, part in enumerate(parts):
                for i in part:
                    w[i] = cvals[c]
            out.append((f"coset_const_d{d}_t{trial}", w))
        # (a2) indicator-of-one-coset: 1 on coset 0, 0 elsewhere (a "spike" on a subgroup)
        w = [0] * n
        for i in parts[0]:
            w[i] = 1
        out.append((f"coset_indicator_d{d}", w))
        # (a3) codeword on a coset-union, random elsewhere: pick a random low-deg poly,
        #      eval it on a union of ceil(half) cosets, randomize the rest. Forces a big
        #      shared-agreement block on a multiplicative-structured support.
        c = tuple(rng.randrange(q) for _ in range(k))
        cw = [eval_poly(c, F.sub[i], q) for i in range(n)]
        w = list(cw)
        union = set()
        for cidx in range(ncos):
            if cidx % 2 == 1:                  # keep ~half the cosets as codeword
                for i in parts[cidx]:
                    union.add(i)
        for i in range(n):
            if i not in union:                 # randomize the complement
                w[i] = rng.randrange(q)
        out.append((f"coset_codeword_union_d{d}", w))
    return out


# ---------------- construction (b): e2=0 over-determined census words ----------------
def esym2(vals, q):
    """e_1, e_2 of vals mod q."""
    e1 = 0
    for v in vals:
        e1 = (e1 + v) % q
    e2 = 0
    for a, b in itertools.combinations(vals, 2):
        e2 = (e2 + a * b) % q
    return e1 % q, e2 % q


def find_e2zero_cores(F, t, want=8, scan_cap=200000):
    """Find t-subsets S of mu_n whose domain images have e_2 = 0 (and report e_1).
    These are the 'over-determined' cores the campaign claims number ~n^2/4. We scan
    t-subsets and collect those with e2==0; return up to `want` of them grouped by e1."""
    n = F.n
    sub = F.sub
    q = F.q
    by_e1 = {}
    scanned = 0
    for S in itertools.combinations(range(n), t):
        scanned += 1
        if scanned > scan_cap:
            break
        vals = [sub[i] for i in S]
        e1, e2 = esym2(vals, q)
        if e2 == 0:
            by_e1.setdefault(e1, []).append(S)
    return by_e1, scanned


def make_e2zero_words(F, rng):
    """Family (b). Build words designed to admit MANY codewords through an e2=0 incidence
    structure. Strategy: pick a degree< k base codeword; pick an e2=0 t-core S; the word is the
    codeword on the COMPLEMENT plus a different value on S so that any codeword agreeing on
    >= a points must pass through structured subsets. We realize the 'over-determined census'
    word directly: w that on an e2=0 core equals a SECOND codeword (forcing two codewords to
    both be close), garbage elsewhere -- the densest-cluster-style word but on e2=0 support."""
    q, n, k = F.q, F.n, F.k
    out = []
    cap = k          # capacity agreement
    # use t = k+1 and t = k+2 cores (just above capacity; cores carry the over-determination)
    for t in [k + 1, k + 2]:
        if t > n:
            continue
        by_e1, scanned = find_e2zero_cores(F, t, want=12)
        if not by_e1:
            continue
        # pick the e1 value with the MOST e2=0 cores (densest over-determined cluster)
        e1_best = max(by_e1, key=lambda e: len(by_e1[e]))
        cores = by_e1[e1_best]
        # (b1) overlay two codewords on a shared e2=0 core: w = cw1 on core, cw2 elsewhere
        c1 = tuple(rng.randrange(q) for _ in range(k))
        c2 = tuple(rng.randrange(q) for _ in range(k))
        cw1 = [eval_poly(c1, F.sub[i], q) for i in range(n)]
        cw2 = [eval_poly(c2, F.sub[i], q) for i in range(n)]
        S = set(cores[0])
        w = [cw1[i] if i in S else cw2[i] for i in range(n)]
        out.append((f"e2zero_overlay_t{t}", w))
        # (b2) UNION of several e2=0 cores sharing e1: place a single codeword on the union of
        #      up to 4 e2=0 cores, randomize the rest. Many e2=0 cores -> dense structured mass.
        union = set()
        for S in cores[:4]:
            union |= set(S)
        c = tuple(rng.randrange(q) for _ in range(k))
        cw = [eval_poly(c, F.sub[i], q) for i in range(n)]
        w = [cw[i] if i in union else rng.randrange(q) for i in range(n)]
        out.append((f"e2zero_coreunion_t{t}_ncores{min(4,len(cores))}", w))
        # (b3) the raw 'most-shared' word: take the e1_best class; build w so that on EACH
        #      e2=0 core a DISTINCT codeword agrees. Approximate by averaging: place cw1 on the
        #      symmetric-difference-minimal arrangement. Use union of all cores, codeword cw1.
        bigunion = set()
        for S in cores:
            bigunion |= set(S)
        w = [cw1[i] if i in bigunion else rng.randrange(q) for i in range(n)]
        out.append((f"e2zero_allcoreunion_t{t}_n{len(cores)}cores_cov{len(bigunion)}", w))
    return out


# ---------------- construction (c): subfield / Frobenius words ----------------
def make_subfield_words(F, rng):
    """Family (c). Frobenius/subfield-structured words. Over a PRIME field z^q = z so the literal
    Frobenius word is the identity codeword (degenerate, per H-FROB). We instead test the
    multiplicative-subgroup-indicator and small-prime-subfield-value words that the campaign
    flagged as subfield-structured candidates."""
    q, n, k = F.q, F.n, F.k
    out = []
    # (c1) subgroup-indicator: 1 on mu_d, 0 off it (for each proper d) -- a multiplicative char
    for d in divisors_pow2(n):
        step = n // d
        w = [1 if (i % step == 0) else 0 for i in range(n)]   # mu_d = indices 0, step, 2*step,...
        out.append((f"subgroup_indicator_mu{d}", w))
    # (c2) small-subfield-valued word: all word values drawn from {0,1,2,...,small} (a tiny
    #      'subfield-like' alphabet); structured low-entropy word.
    for B in [2, 3]:
        w = [rng.randrange(B) for _ in range(n)]
        out.append((f"small_alphabet_B{B}", w))
    # (c3) quadratic-character word: w_i = 1 if x_i is a QR mod q else -1(=q-1). A genuine
    #      multiplicative character on the domain (subfield/Frobenius-flavored).
    def is_qr(x):
        return pow(x % q, (q - 1) // 2, q) == 1
    w = [1 if is_qr(F.sub[i]) else (q - 1) for i in range(n)]
    out.append(("quad_char", w))
    # (c4) power-map word: w_i = x_i^2 mod q (image of the squaring/Frobenius-flavored map),
    #      then reduced -- the campaign's z^p analog truncated to a low-deg-incompatible map.
    w = [pow(F.sub[i], 2, q) for i in range(n)]
    out.append(("square_map", w))
    return out


# ---------------- driver ----------------
def run(q, n, rho, seed=12345, family="all", verbose=True):
    k = round(rho * n)
    F = Field(q, n, k)
    subs = precompute_subsets(n, k)
    lag = precompute_lagrange(F, subs)
    rng = random.Random(seed)
    interior = interior_radii(n, rho)
    budget = n                      # prize-regime budget ~ q*eps* ~ n
    rows = []
    builders = []
    if family in ("all", "a"):
        builders.append(("a", make_coset_words))
    if family in ("all", "b"):
        builders.append(("b", make_e2zero_words))
    if family in ("all", "c"):
        builders.append(("c", make_subfield_words))
    for fam, builder in builders:
        for label, w in builder(F, rng):
            # exact list at every interior radius
            lists = {a: list_count_fast(w, a, F, subs, lag) for a in interior}
            # also record the agreement-fraction view and whether >n at an interior a
            max_int = max(lists.values()) if lists else 0
            super_budget_a = [a for a, L in lists.items() if L > budget]
            rec = dict(family=fam, label=label, n=n, q=q, rho=rho, k=k,
                       interior_a=interior, budget=budget,
                       lists={str(a): L for a, L in lists.items()},
                       max_interior_list=max_int,
                       super_budget=bool(super_budget_a),
                       super_budget_radii=super_budget_a)
            rows.append(rec)
    rows.sort(key=lambda r: -r["max_interior_list"])
    if verbose:
        print(f"\n{'='*84}\nMETHOD 2  n={n} q={q} rho={rho} k={k}  interior_a={interior}  budget(~n)={budget}\n{'='*84}")
        print(f"{'fam':3s} {'label':40s} {'maxL':>5s} {'>n?':>4s}  list@interior_a")
        for r in rows:
            la = " ".join(f"{a}:{r['lists'][str(a)]}" for a in interior)
            flag = "YES" if r["super_budget"] else "."
            print(f"{r['family']:3s} {r['label']:40s} {r['max_interior_list']:5d} {flag:>4s}  {la}")
    return rows


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--rho", type=float, default=0.25)
    ap.add_argument("--seed", type=int, default=12345)
    ap.add_argument("--family", default="all")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    rows = run(args.q, args.n, args.rho, seed=args.seed, family=args.family)
    if args.out:
        os.makedirs(os.path.dirname(args.out), exist_ok=True)
        json.dump(rows, open(args.out, "w"), indent=1)
        print(f"\n[OUT] {args.out}")
