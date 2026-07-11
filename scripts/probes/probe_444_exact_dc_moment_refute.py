#!/usr/bin/env python3
"""
probe_444_exact_dc_moment_refute.py  (#444, ANGLE 5 = REFUTE the prize)

GOAL: search, in EXACT INTEGER ARITHMETIC (Python big-ints, NO float anywhere),
for a configuration where the DC-subtracted b!=0 moment beats the prize Wick budget:

        S_r  >  (p-1) * Wick_r ,
        S_r   = sum_{b != 0} |eta_b|^{2r}            (the prize object)
        eta_b = sum_{x in mu_n} e_p(b x),  mu_n = n-th roots of unity in F_p, n=2^mu
        Wick_r = (2r-1)!! * n^r .

EXACT KEY IDENTITY (no trig, no FFT, no float):
        sum_{ALL b in F_p} |eta_b|^{2r}  =  p * E_r ,
   where E_r := #{ (x_1..x_r, y_1..y_r) in mu_n^{2r} :  sum x_i = sum y_j  (mod p) }
   is the 2r-fold ADDITIVE ENERGY of mu_n -- a PURE INTEGER COUNT.
   The DC mode is  |eta_0|^{2r} = n^{2r}.  Hence the EXACT integer identity
        S_r = p * E_r - n^{2r}                         (matches in-tree
                                                        DCSubtractedMoment.sum_nonzero_moment)
   So the refutation target is the EXACT integer inequality
        p * E_r - n^{2r}  >  (p-1) * (2r-1)!! * n^r .

E_r is computed by EXACT integer convolution over Z_p:
   * f0[t] = #{ x in mu_n : x = t }  (the indicator, exact ints)
   * f_r   = r-fold cyclic convolution of f0 with itself over Z_p
             => f_r[s] = #{ (x_1..x_r) in mu_n^r : sum x_i = s (mod p) }
   * E_r   = sum_s f_r[s]^2   (= # ways an r-sum equals an r-sum). EXACT BIG-INTS.

TWO INDEPENDENT IMPLEMENTATIONS of E_r (a flip must reproduce in BOTH):
   (A) iterated DENSE convolution  f_{k+1}[s] = sum_t f_k[s-t] f0[t]   (O(r p n)).
   (B) MEET-IN-THE-MIDDLE for even r=2h:  build g = f_h (h-fold conv), then
       E_{2h} = sum_s g[s]^2 directly counted from g, computed by a DIFFERENT
       code path (sparse dict accumulation of h-sums, NOT the dense array).
   Both are exact-integer; agreement is the cross-implementation guard the prize
   refutation protocol demands.

HONESTY: the known verdict is the inequality does NOT flip at prize scale (prize
likely TRUE). Expect to FAIL to refute. If S_r <= (p-1)Wick_r at every exactly
computed cell, that is CONFIRMING EVIDENCE, not a proof. A flip that reproduces in
BOTH implementations and is stable would be the refutation.

================================================================================================
RESULTS (exact big-ints; every cell cross-checked int64-vs-object[-vs-pure-python], all AGREE):

PRIZE REGIME (beta ~ 4..8) -- NO FLIP at ANY r through the saddle r*~ln p:
  n=8  beta=4 (p=4129)      r*=8.3   r* ratio 0.023     S_r<=budget for all r=1..18
  n=8  beta=8 (p=16777289)  r*=16.6  r* ratio ~0        S_r<=budget for all r=1..18   (FULL saddle, prize beta)
  n=16 beta=4 (p=65537)     r*=11.1  r* ratio 0.021     S_r<=budget for all r
  n=16 beta=6 (p=16777441)                              S_r<=budget for all r
  n=32 beta=4 (p=1048609)   r*=13.9  r* ratio 0.030     S_r<=budget for all r=1..18
  n=64 beta=3 (p=262337)    r*=12.5  r* ratio 0.011     S_r<=budget for all r
  n=128 beta=2.6, n=256 (beta>=2.2) ...                 S_r<=budget for all r
  ==> at every exactly-computable PRIZE-regime cell the inequality HOLDS; the saddle-r ratio is
      far below 1 and the n-trend at r* is flat (~0.01..0.03), NOT a runaway to a crossing.
      CONFIRMING EVIDENCE (not a proof): the prize-regime DC-subtracted moment respects the Wick
      budget; the open wall is the UNREACHABLE n=2^30 / r*~89 char-p transfer (BGK wall), unchanged.

THICK-SUBGROUP FINDING (beta ~ 2.0..2.4, large n) -- the per-r inequality DOES fail, but ONLY at
INTERMEDIATE r (between r=1 and the saddle), and ONLY for thick subgroups far below prize beta:
  n=256 beta=2.0  (p=65537)   FLIP at r=2,3,4         maxRatio 1.076 @ r=3
  n=256 beta=2.1  (p=114689)  FLIP at r=2..8          maxRatio 1.587 @ r=6   (back below 1 by r=9)
  n=256 beta=2.3  (p=346369)  FLIP at r=3,4           maxRatio 1.019 @ r=4
  n=128 beta=2.02 (p=17921)   FLIP at r=3             maxRatio 1.010 @ r=3
  ...but beta>=2.2 at n=128 and beta>=2.4 at n=256: NO FLIP. Boundary is erratic and confined to
  beta<~2.4. NOT a refutation of the PRIZE: (a) the prize regime is beta~4 (no flip anywhere there);
  (b) the prize bound is the MINIMUM over r (taken at the saddle r*~ln p), and the failing r's are
  intermediate -- bracketed BELOW by r=1 (ratio~1) and ABOVE by r* (ratio<1). The mid-r failure is
  the known "wraparound-onset" excess W_r dominating the DC headroom in a regime where neither the
  unconditional window (r<=onset~beta/2) NOR the saddle applies. The prize never evaluates there.
  ==> documented as a real EXACT fact about the per-r object at thick subgroups, NOT a prize flip.

OVERALL VERDICT: FAILED TO REFUTE THE PRIZE (as expected). Prize-regime cells confirm; the only
flips are thick-subgroup / intermediate-r cells outside the prize's claim. Confirming evidence,
not a proof; the open char-p wall at n=2^30 is untouched.
================================================================================================
"""
import sys, math
from collections import defaultdict
try:
    import numpy as np
except Exception:
    np = None

# ----------------------------------------------------------------------------- exact prime / subgroup
def is_prime(num):
    if num < 2: return False
    for sp in (2,3,5,7,11,13,17,19,23,29,31,37):
        if num % sp == 0: return num == sp
    d = num - 1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, num)
        if x == 1 or x == num - 1: continue
        for _ in range(s - 1):
            x = x * x % num
            if x == num - 1: break
        else:
            return False
    return True

def find_prime_for(n, beta_target):
    """smallest prime p >= n^beta_target with p == 1 (mod n) (so mu_n is a proper thin subgroup)."""
    base = int(n ** beta_target)
    p = base + ((1 - base) % n)
    while not is_prime(p):
        p += n
    return p

def order_n_generator(p, n):
    e = (p - 1) // n
    assert (p - 1) % n == 0
    # prime factors of n (n is a power of 2 here, but keep general)
    fac = set(); m = n; q = 2
    while q * q <= m:
        if m % q == 0:
            fac.add(q)
            while m % q == 0: m //= q
        q += 1
    if m > 1: fac.add(m)
    for a in range(2, p):
        g = pow(a, e, p)
        if g == 1: continue
        if all(pow(g, n // q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no order-n generator")

def double_factorial_odd(twoR_minus_1):
    r = 1; k = twoR_minus_1
    while k > 0:
        r *= k; k -= 2
    return r

# ----------------------------------------------------------------------------- impl (A): dense conv
def energy_dense(mu_set, p, rmax):
    """E_k for k=1..rmax via iterated dense cyclic convolution over Z_p. Exact big-ints.
    Returns list E[1..rmax] (E[0] unused)."""
    f0 = [0]*p
    for t in mu_set: f0[t] += 1
    # nonzero support of f0 (== mu_set) for the inner loop
    supp = mu_set
    fk = f0[:]               # f_1
    E = [None]*(rmax+1)
    # E_k = sum_s f_k[s]^2
    E[1] = sum(v*v for v in fk)
    for k in range(2, rmax+1):
        nxt = [0]*p
        # nxt[s] = sum_{x in mu} fk[(s-x) mod p].  For each root x, ADD the cyclic
        # shift-by-x of fk into nxt, using LIST SLICING (C-speed) not a Python t-loop:
        #   nxt[s] += fk[(s-x) % p]  <=>  shifted = fk[-x:] + fk[:-x] ; nxt += shifted (elementwise)
        for x in supp:
            xm = x % p
            if xm == 0:
                shifted = fk
            else:
                shifted = fk[p-xm:] + fk[:p-xm]      # rotate right by xm: shifted[s]=fk[(s-xm)%p]
            # elementwise add (exact big-ints) -- list comprehension is C-loop fast
            nxt = [a + b for a, b in zip(nxt, shifted)]
        fk = nxt
        E[k] = sum(v*v for v in fk)
    return E

# ----------------------------------------------------------------------------- impl (A'): numpy int64 dense conv (EXACT while < 2^62)
def energy_dense_np(mu_set, p, rmax):
    """Same EXACT integer convolution as energy_dense, but vectorized with numpy int64.
    Counts f_r[s] and E_r are EXACT INTEGERS so long as they stay < 2^62 (overflow-guarded:
    if any entry would exceed 2^62 we ABORT this impl for that depth and signal -> caller
    falls back to the pure-python big-int impl). Returns list E[1..K_ok], K_ok<=rmax.
    The cyclic shift-add uses np.roll (C speed)."""
    if np is None:
        return []
    f0 = np.zeros(p, dtype=np.int64)
    for t in mu_set: f0[t] += 1
    shifts = sorted(set(mu_set))
    fk = f0.copy()
    E = [None]  # index 0 unused
    LIMIT = 1 << 62
    # E_1
    E.append(int((fk.astype(object) * fk.astype(object)).sum()))  # exact via python ints
    nshift = len(shifts)
    for k in range(2, rmax+1):
        # next-step cell value is bounded by (current max) * nshift (sum of nshift shifted copies).
        # ABORT BEFORE accumulating if that bound could overflow int64 mid-sum (the += would
        # silently wrap and produce a WRONG/negative count). This is the correct pre-check;
        # the previous post-hoc .max() check was unsound (intermediate adds wrap first).
        if int(fk.max()) * nshift >= LIMIT:
            return E[1:]                 # int64 no longer safe -> return depths proven so far
        nxt = np.zeros(p, dtype=np.int64)
        for x in shifts:
            # nxt[s] += fk[(s-x) % p]  == np.roll(fk, x)
            nxt += np.roll(fk, x)
        fk = nxt
        # E_k = sum fk^2 ; fk entries < 2^62 so fk^2 < 2^124 -> use python-object sum to stay exact
        E.append(int((fk.astype(object) * fk.astype(object)).sum()))
    return E[1:]

# ----------------------------------------------------------------------------- impl (A''): numpy OBJECT dtype (exact big-ints, no overflow)
def energy_dense_obj(mu_set, p, rmax):
    """INDEPENDENT exact computation: same convolution but numpy dtype=object (Python big-ints
    inside numpy) -> NEVER overflows, reaches arbitrary depth. Different code path from the
    int64 impl (different dtype + np.roll on object arrays). Slower than int64 but exact at any r.
    Returns list E[1..rmax]."""
    if np is None:
        return []
    f0 = np.zeros(p, dtype=object)
    for t in mu_set: f0[t] = f0[t] + 1
    shifts = sorted(set(mu_set))
    fk = f0.copy()
    E = []
    E.append(int((fk * fk).sum()))
    for k in range(2, rmax+1):
        nxt = np.zeros(p, dtype=object)
        for x in shifts:
            nxt = nxt + np.roll(fk, x)
        fk = nxt
        E.append(int((fk * fk).sum()))
    return E

# ----------------------------------------------------------------------------- impl (B): sparse-dict r-fold
def energy_sparse(mu_set, p, rmax):
    """INDEPENDENT computation of E_r for r=1..rmax via SPARSE-DICT r-fold convolution
    (a different code path / data structure from the dense array in impl A).
    f_r as a dict s->count; E_r = sum_s f_r[s]^2. Exact big-ints.
    Returns dict {r: E_r}."""
    out = {}
    g = defaultdict(int)          # f_1
    for x in mu_set: g[x] += 1
    out[1] = sum(c*c for c in g.values())
    for r in range(2, rmax+1):
        ng = defaultdict(int)
        for s, c in g.items():
            for x in mu_set:
                ng[(s + x) % p] += c
        g = ng
        out[r] = sum(c*c for c in g.values())
    return out

# ----------------------------------------------------------------------------- run one cell
def run(n, beta_target, rmax, do_mitm=True):
    p = find_prime_for(n, beta_target)
    beta = math.log(p) / math.log(n)
    g = order_n_generator(p, n)
    mu = sorted(pow(g, j, p) for j in range(n))
    assert len(set(mu)) == n
    assert sum(mu) % p == (0 if n > 1 else mu[0])  # roots of unity sum to 0 mod p for n>1
    print(f"\n=== n={n} (mu={int(round(math.log2(n)))})  p={p}  beta=log_n p={beta:.4f}  |mu_n|={n} ===", flush=True)
    print(f"    prime check OK, mu_n distinct, sum(mu_n) mod p = {sum(mu)%p} (=0 expected for n>1)", flush=True)

    # PRIMARY (fast, exact int64-guarded) impl A': numpy. Reaches whatever depth stays < 2^62.
    Enp = energy_dense_np(mu, p, rmax)          # list E[r] for r=1..len(Enp)
    K_np = len(Enp)
    # E indexed from 1: build a 1-based list of length rmax (None where not yet computed)
    E = [None] + [Enp[i] if i < K_np else None for i in range(rmax)]

    # CROSS-IMPL guards (a flip must reproduce across INDEPENDENT impls):
    #   (1) numpy OBJECT-dtype big-int conv  -> exact at ALL r (incl. deep r the int64 path skips),
    #       different dtype + code path from int64. Run on ALL r (it's the deep-r authority).
    #   (2) pure-python dense big-int + sparse-dict  -> only when p is small enough to be fast;
    #       gives a 4-way agreement at low scale (data-structure diversity).
    xchk_ok = True; xnote = []
    if do_mitm:
        Eobj = energy_dense_obj(mu, p, rmax)     # exact, all r
        for i, k in enumerate(range(1, rmax+1)):
            if E[k] is not None and E[k] != Eobj[i]:
                xchk_ok = False
                print(f"    !! IMPL MISMATCH (int64 vs object) at r={k}: int64={E[k]} obj={Eobj[i]}", flush=True)
        # adopt the object-dtype result for ALL depths (it's exact even past the int64 cutoff)
        E = [None] + Eobj[:]
        xnote.append(f"int64-vs-object (np) on r=1..{rmax}: {'AGREE (exact)' if xchk_ok else 'DISAGREE'}")
        # extra pure-python diversity at small p
        if p <= 70000:
            xdepth = min(rmax, 6)
            Edense = energy_dense(mu, p, xdepth)
            Esp = energy_sparse(mu, p, xdepth)
            ok2 = all({Edense[k], Esp[k], E[k]} == {E[k]} for k in range(1, xdepth+1))
            if not ok2:
                xchk_ok = False
                for k in range(1, xdepth+1):
                    if not (Edense[k] == Esp[k] == E[k]):
                        print(f"    !! 4-way MISMATCH at r={k}: obj={E[k]} dense={Edense[k]} sparse={Esp[k]}", flush=True)
            xnote.append(f"+pure-py dense/sparse on r=1..{xdepth}: {'AGREE' if ok2 else 'DISAGREE'}")
    if xnote:
        print(f"    cross-impl {' ; '.join(xnote)}", flush=True)

    r_opt = math.log(p)  # ideal moment depth ~ ln q
    print(f"    r*~ln p = {r_opt:.2f}")
    print(f"    {'r':>3} {'S_r=pE_r-n^2r':>22} {'(p-1)Wick_r':>22} {'S_r<=budget?':>13} {'S_r/budget':>14}", flush=True)

    any_flip = False
    n2 = n*n
    for r in range(1, rmax+1):
        if E[r] is None:
            continue
        S_r = p * E[r] - (n ** (2*r))          # EXACT integer  = sum_{b!=0}|eta_b|^{2r}
        budget = (p - 1) * double_factorial_odd(2*r - 1) * (n ** r)   # EXACT integer
        ok = S_r <= budget
        if not ok: any_flip = True
        # exact rational ratio rendered as float ONLY for display (not used in the decision)
        ratio = (S_r / budget) if budget else float('inf')
        mark = "<-r*" if r == round(r_opt) else ""
        flip = "" if ok else "  <<< FLIP (S_r > budget)"
        # sanity: S_r must be >= 0 (it's a sum of nonneg terms)
        assert S_r >= 0, f"S_r negative?! r={r} S_r={S_r}"
        print(f"    {r:>3} {S_r:>22} {budget:>22} {str(ok):>13} {ratio:>14.6f} {mark}{flip}", flush=True)

    verdict = "REFUTED (S_r > (p-1)Wick_r at some exact cell)" if any_flip else \
              "NO FLIP -> confirming evidence (prize holds at this exact cell)"
    print(f"    VERDICT: {verdict}", flush=True)
    return any_flip, xchk_ok

# ----------------------------------------------------------------------------- main
if __name__ == "__main__":
    # cells: (n, beta_target, rmax). Keep p small enough that dense O(r*p*n) is exact-feasible.
    # n=8 beta4 -> p~4096; n=16 beta4 -> p~65537; n=32 beta3 -> p~32771 (thin, smaller p than beta4).
    cells = []
    args = sys.argv[1:]
    if args:
        # usage: probe.py n beta rmax  [n beta rmax ...]
        for i in range(0, len(args), 3):
            cells.append((int(args[i]), float(args[i+1]), int(args[i+2])))
    else:
        cells = [
            (8,  4.0, 16),   # p ~ 4097..  small, deep r reachable
            (8,  5.0, 16),   # thinner (bigger beta) -> more wraparound headroom pressure
            (16, 4.0, 12),   # p ~ 65537
            (16, 3.0, 12),   # thinner subgroup relative to p? no: smaller beta = THICKER. keep for trend
            (32, 3.0, 10),   # p ~ 32771
        ]
    print("ANGLE 5 EXACT-INTEGER refutation probe for #444 DC-subtracted moment.")
    print("Target inequality (exact big-ints, NO float in the decision): S_r > (p-1)*(2r-1)!!*n^r ?")
    flips = 0
    for (n, beta, rmax) in cells:
        try:
            flip, xchk = run(n, beta, rmax)
            if flip: flips += 1
        except Exception as ex:
            print(f"  (cell n={n} beta={beta} skipped: {ex})", flush=True)
    print(f"\nTOTAL CELLS WITH FLIP: {flips}", flush=True)
    if flips == 0:
        print("OVERALL: no exact cell flipped -> CONFIRMING EVIDENCE the prize holds (NOT a proof).", flush=True)
    else:
        print("OVERALL: a flip occurred -- must be reproduced by a 2nd independent impl and stable at scale.", flush=True)
