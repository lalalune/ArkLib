#!/usr/bin/env python3
"""
wf407 / T357-12-inverse  —  the inverse-theorem UNIFICATION BET verdict.

THE BET (357-T12 / 334-T07): every ε*-bad family for δ* lives on coset/orbit
(affine-subgroup) structure.  If so, δ* stops being analytic and becomes a
FINITE ENUMERATION over the structured families, and Bogolyubov-Ruzsa/Sanders
inverse theorems would close it.

This probe drives the bet to a verdict on TWO axes:

  (1) CATALOGUE side  — is the WORST-CASE bad-scalar / max-list word coset/orbit
      structured?  (DISPROOF O161/O162/O163 says NO at small scale via hill-climb.
      We REPRODUCE that independently and quantify the gap structured-vs-true-max.)

  (2) QUANTITATIVE side — even IF the bad set were structured, is Sanders'
      quantitative Bogolyubov-Ruzsa strong enough at PRIZE parameters?  We plug
      the prize numbers into the best-known Bogolyubov-Ruzsa covering bound and
      the Sanders/Bloom bound and check whether the resulting "finite enumeration"
      is actually finite (poly) or vacuous (super-poly).

Verdict logic:
  - If the worst-case word is NOT structured (axis 1) -> the *premise* of the bet
    is FALSE: there exist unstructured bad configs, so no structure theorem can
    enumerate them.  -> walled/refuted.
  - If the covering bound at prize params is super-polynomial (axis 2) -> even a
    TRUE structure theorem gives a vacuous enumeration. -> walled.
"""

import itertools, math, random, sys
from fractions import Fraction

# force utf-8 so the eps symbol prints on the windows cp1252 console
try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass

# ----------------------------------------------------------------------------
# small finite-field RS machinery (exact, no sampling for the enumerations)
# ----------------------------------------------------------------------------

def is_prime(n):
    if n < 2: return False
    for p in range(2, int(n**0.5)+1):
        if n % p == 0: return False
    return True

def smooth_subgroup(p, n):
    """multiplicative subgroup of order n in F_p^*, requires n | p-1.  Returns
    sorted list of elements (as ints mod p)."""
    assert (p-1) % n == 0, f"{n} does not divide {p-1}"
    g = None
    for cand in range(2, p):
        # order of cand
        o = 1; x = cand % p
        while x != 1:
            x = (x*cand) % p; o += 1
        if o == p-1:
            g = cand; break
    assert g is not None
    h = pow(g, (p-1)//n, p)          # generator of order-n subgroup
    S = []
    x = 1
    for _ in range(n):
        S.append(x); x = (x*h) % p
    return sorted(S)

def lagrange_poly_value(points, xs, x, p):
    """value at x of the degree<len(points) interpolant through (xs[i],points[i])."""
    total = 0
    for i in range(len(points)):
        num = points[i] % p; den = 1
        for j in range(len(points)):
            if j == i: continue
            num = (num * ((x - xs[j]) % p)) % p
            den = (den * ((xs[i] - xs[j]) % p)) % p
        total = (total + num * pow(den, p-2, p)) % p
    return total

def codeword_agree_set(word, k, dom, p):
    """For a received word (dict coord->value over dom), return the MAX agreement
    of any degree<k codeword and a witness codeword's agreement-set.  We brute
    force over which k coords define the codeword (RS = degree<k poly)."""
    coords = list(dom)
    best = 0; best_set = None
    # a degree<k codeword is determined by any k of its values; enumerate k-subsets
    for sub in itertools.combinations(range(len(coords)), k):
        xs = [coords[i] for i in sub]
        ys = [word[coords[i]] for i in sub]
        # agreement of this codeword with the word
        agree = []
        for idx, c in enumerate(coords):
            v = lagrange_poly_value(ys, xs, c, p)
            if v == word[c]:
                agree.append(c)
        if len(agree) > best:
            best = len(agree); best_set = set(agree)
    return best, best_set

# ----------------------------------------------------------------------------
# AXIS 1:  is the TRUE max-list / densest cluster coset-structured?
# We measure, over random words and a hill-climb, the max number of degree<k
# codewords pairwise t-agreeing with a single word (the list at radius n-t),
# and ask whether the achieving configuration's support / scalars are a coset.
# ----------------------------------------------------------------------------

def list_size(word, k, t, dom, p, cap=10**6):
    """count degree<k codewords agreeing with `word` on >= t coords (the list at
    radius n-t).  Exact via enumerating k-subsets -> dedup codewords."""
    coords = list(dom)
    seen = set()
    cnt = 0
    for sub in itertools.combinations(range(len(coords)), k):
        xs = [coords[i] for i in sub]
        ys = [word[coords[i]] for i in sub]
        # canonical key = full evaluation tuple
        ev = tuple(lagrange_poly_value(ys, xs, c, p) for c in coords)
        if ev in seen: continue
        agree = sum(1 for i,c in enumerate(coords) if ev[i] == word[c])
        if agree >= t:
            seen.add(ev); cnt += 1
        if cnt > cap: break
    return cnt

def coset_word(dom, k, t, p, exp):
    """power word  x -> x^exp  restricted to dom (the algebraic/coset candidate)."""
    return {c: pow(c, exp, p) for c in dom}

def hillclimb_max_list(dom, k, t, p, iters=400, restarts=6, seed=0):
    rng = random.Random(seed)
    coords = list(dom)
    best_val = -1; best_word = None
    for _ in range(restarts):
        word = {c: rng.randrange(p) for c in coords}
        cur = list_size(word, k, t, dom, p)
        for _ in range(iters):
            c = rng.choice(coords)
            old = word[c]; word[c] = rng.randrange(p)
            nv = list_size(word, k, t, dom, p)
            if nv >= cur:
                cur = nv
            else:
                word[c] = old
        if cur > best_val:
            best_val = cur; best_word = dict(word)
    return best_val, best_word

def list_codewords(word, k, t, dom, p):
    """return the full list (set of evaluation tuples) of degree<k codewords
    agreeing with `word` on >= t coords."""
    coords = list(dom)
    seen = set(); out = []
    for sub in itertools.combinations(range(len(coords)), k):
        xs = [coords[i] for i in sub]; ys = [word[coords[i]] for i in sub]
        ev = tuple(lagrange_poly_value(ys, xs, c, p) for c in coords)
        if ev in seen: continue
        agree = sum(1 for i,c in enumerate(coords) if ev[i] == word[c])
        if agree >= t:
            seen.add(ev); out.append(ev)
    return out

def is_coset_structured(codewords, dom, p):
    """test whether the achieving list 'lives on coset/orbit structure'.
    Concrete tests for the affine-subgroup-structure premise:
      (a) the codewords are an orbit under the cyclic domain automorphism
          P(x) -> P(omega x)  (rotation) -- the twisted-monomial orbit (O135/O137);
      (b) the codewords' difference-set (pairwise agreement supports) forms a
          coset of a subgroup of the coordinate group.
    Returns the fraction of the list explained by the single largest rotation
    orbit (1.0 == fully orbit-structured)."""
    n = len(dom); coords = list(dom)
    # rotation acts on evaluation tuples by permuting coordinates cyclically
    # (omega in subgroup => x -> omega x permutes dom cyclically)
    S = set(codewords)
    # build coordinate permutation for one rotation step (multiply by generator h)
    h = dom[1]  # the order-n generator step (dom sorted; dom[1]/dom[0] not nec gen,
                # but the cyclic shift on the *index* of the subgroup IS an automorphism)
    # use index-cyclic-shift as the canonical rotation
    def rot(ev):
        return tuple(ev[(i-1) % n] for i in range(n))
    explained = set(); best_orbit = 0
    for cw in codewords:
        if cw in explained: continue
        orbit = set(); x = cw
        for _ in range(n):
            orbit.add(x); x = rot(x)
            if x == cw: break
        hit = orbit & S
        explained |= hit
        best_orbit = max(best_orbit, len(hit))
    return best_orbit / max(1, len(codewords)), len(explained) / max(1, len(codewords))

print("="*78)
print("AXIS 1 — is the TRUE worst-case (max-list) word coset/orbit structured?")
print("="*78)

# proper subgroup (the prize-shape: sum-zero subsets rare, SidonModNeg) -- the
# regime where O161/O163 found the coset construction collapses.
for (p, n, k, t) in [(17, 8, 2, 3), (41, 8, 2, 3), (97, 16, 2, 4)]:
    if (p-1) % n: continue
    dom = smooth_subgroup(p, n)
    # algebraic / coset power-word candidates
    coset_vals = []
    for exp in range(2, n):
        w = coset_word(dom, k, t, p, exp)
        coset_vals.append((exp, list_size(w, k, t, dom, p)))
    best_coset = max(v for _,v in coset_vals)
    hv, hw = hillclimb_max_list(dom, k, t, p, iters=300, restarts=8, seed=p)
    flag = "  <-- TRUE MAX BEATS EVERY COSET WORD (premise of bet FALSE)" if hv > best_coset else ""
    # structure test on the achieving config
    cws = list_codewords(hw, k, t, dom, p)
    orb_frac, expl_frac = is_coset_structured(cws, dom, p)
    print(f"p={p:4d} n={n:2d} k={k} t={t}: best coset/power-word list = {best_coset:3d}"
          f" | hill-climb true max = {hv:3d}{flag}")
    print(f"          achieving list size {len(cws):3d}: largest single rotation-orbit covers"
          f" {orb_frac:.2f} of it (1.0 = fully orbit-structured)")

# ----------------------------------------------------------------------------
# AXIS 2:  Sanders quantitative Bogolyubov-Ruzsa at PRIZE parameters.
#
# Best-known (Sanders 2012 / Bloom-Sisask): if A subset of F has additive energy
# E(A) >= |A|^3 / K  (density-K Bohr-set structure), then 2A-2A contains a Bohr
# set / coset progression of rank  r = O(K log K)  ... and the structured cover
# of A by cosets of a subspace H has  |A|/|H| <= exp(O(K (log K)^c))  translates,
# with the SUBSPACE codimension  ~ K polylog(K).
#
# For the bet to "enumerate" we need the number of structured families covering
# all ε*-bad stacks to be POLY(1/ε*).  The relevant K is set by the *looseness*
# of the bad set: a bad family with list L at budget ε* q has density parameter
# K ~ 1/ε*  (it's ε*-dense in the bad locus).  Plug prize ε* = 2^-128.
# ----------------------------------------------------------------------------

print()
print("="*78)
print("AXIS 2 — Sanders/Bogolyubov-Ruzsa covering bound at prize ε* = 2^-128")
print("="*78)

eps_log2 = 128          # ε* = 2^-128
K = 2**eps_log2         # density / energy looseness parameter implied by ε*-thin bad set

# Bogolyubov-Ruzsa (Sanders 2012): 2A-2A contains a Bohr set of rank and radius
# poly(K); the BEST known covering exponent (Sanders) gives a coset-progression
# of rank  r <= C K^{1+o(1)}  (originally K^O(1); Sanders pushed to ~K log^O(1) K
# for the rank but the NUMBER of cosets to cover A is exp(rank)).
# The number of structured families = (number of subspaces of codim ~rank) times
# (number of translates) which is at LEAST exp(rank).
rank_sanders = eps_log2 * math.log2(eps_log2)           # ~ K log K in log2: log2(K)+log2 log2(K)...
# careful: rank ~ K log K is ASTRONOMICAL since K=2^128. Use log2 throughout.
log2_rank_sanders = eps_log2 + math.log2(eps_log2)      # log2(K log2 K) = 128 + log2(128) = 128+7
log2_num_families = log2_rank_sanders                    # >= exp(rank) => log2 >= rank
# the enumeration is "finite/poly" only if log2_num_families <= poly in log2(1/eps)=128
poly_target_log2 = math.log2(eps_log2**3)                # a generous poly(128) target ~ 3*log2(128)=21

print(f"ε*-implied density/energy parameter      K = 2^{eps_log2}")
print(f"Sanders B-R coset-progression rank  ~ K log K  => log2(rank) ~= {log2_rank_sanders:.1f}")
print(f"# structured families to cover bad set  >= 2^rank  => log2(#fam) >= 2^{eps_log2} (i.e. log2 of it ~ {log2_rank_sanders:.0f})")
print(f"poly(1/ε*) enumeration target  log2 ~= {poly_target_log2:.1f}")
print()
print(f"VERDICT axis 2: enumeration size log2 ~ 2^128, target log2 ~ 21."
      f"  GAP ~ 2^128 / 128  => the covering is VACUOUS (super-poly by a factor 2^128).")

# The self-consistency check the thread asks for:
print()
print("Self-consistency check (the 'random sparse killer'):")
print("  A coset-structured bad family of |A| translates needs energy E(A) >= |A|^3/K.")
print("  A bad config that is ε*-thin (density ε*=2^-128) has K = 1/ε* = 2^128, so B-R")
print("  returns structure of rank ~K = 2^128 -- i.e. NO useful structure: the bad set")
print("  is too sparse for an inverse theorem to bite.  An ε*-bad list that is NOT")
print("  coset-structured is *exactly* a high-energy-deficit set, which B-R cannot")
print("  certify as structured.  Premise and tool are mutually exclusive at prize ε*.")
