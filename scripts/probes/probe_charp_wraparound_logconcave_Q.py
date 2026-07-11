#!/usr/bin/env python3
"""
probe_charp_wraparound_logconcave_Q.py  (#444, door-iv Lane-2 char-p transfer)

Tests the SUFFICIENT condition for the open wraparound-control hypothesis `Q >= 0`
in `_CharPTransferDecomposition`:

    Q(r) = gap s W_r W_{r+1} W_{r+2} = (s+2)*W_{r+1}^2 - s*W_r*W_{r+2},   s = 2r+1

where W_r = E_r(F_p) - E_r(C) >= 0 is the char-p WRAPAROUND EXCESS of the
additive-energy ladder of mu_n (n=2^a), and E_r(C) is the char-0 (cyclotomic /
no-wraparound) energy.

CLAIM UNDER TEST (the clean structural sufficient condition):
    wraparound log-concavity   W_r * W_{r+2} <= W_{r+1}^2
    ==>  Q(r) >= (s+2)*W_{r+1}^2 - s*W_{r+1}^2 = 2*W_{r+1}^2 >= 0.

So if the wraparound sequence {W_r} is itself log-concave, the open Q-hypothesis
is DISCHARGED (strictly, with margin 2*W_{r+1}^2). This probe measures whether
W_r*W_{r+2} <= W_{r+1}^2 actually holds in the prize regime, and reports BOTH the
log-concavity verdict AND the resulting Q sign.

Energies computed EXACTLY (Fraction-free integer convolution mod nothing — full Z):
  E_r(F_p) = #{ (x_1..x_r, y_1..y_r) in mu_n^{2r} : sum x_i = sum y_i  (mod p) }
           = sum_{t in F_p} a(t)^2   where a(t) = #{ r-tuples in mu_n with sum = t mod p }.
  E_r(C)   = same but NO modular wraparound: count r-subset-sum coincidences over Z
             via the cyclotomic/antipodal reduction == the "no carry" count.
We get E_r(C) as the r-fold self-convolution of the mu_n indicator over Z (exact),
and E_r(F_p) by folding that Z-convolution mod p. W_r = E_r(F_p) - E_r(C).

This is PROBE-FIRST validation; nothing here is formalized unless it survives.
"""
import sys
from collections import defaultdict

def factorize(m):
    f = {}
    d = 2
    while d * d <= m:
        while m % d == 0:
            f[d] = f.get(d, 0) + 1; m //= d
        d += 1
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f

def primitive_root(p):
    """Find a primitive root mod p using the order-test via prime factors of p-1."""
    facs = list(factorize(p - 1).keys())
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in facs):
            return g
    raise RuntimeError("no primitive root")

def order_subgroup(p, n):
    """Return the n-th roots of unity in F_p^* (mu_n) as a list of residues.
    Requires n | p-1."""
    assert (p - 1) % n == 0, f"n={n} must divide p-1={p-1}"
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)  # generator of mu_n
    S = []
    x = 1
    for _ in range(n):
        S.append(x); x = (x * h) % p
    assert len(set(S)) == n
    return S

def conv_mod(a, b, p):
    """Convolution of two count-vectors over Z/pZ (dict t->count)."""
    out = defaultdict(int)
    for t1, c1 in a.items():
        for t2, c2 in b.items():
            out[(t1 + t2) % p] += c1 * c2
    return out

def conv_Z(a, b):
    """Convolution over Z (dict integer-sum -> count)."""
    out = defaultdict(int)
    for t1, c1 in a.items():
        for t2, c2 in b.items():
            out[t1 + t2] += c1 * c2
    return out

def energy_Fp(S, p, r):
    """E_r(F_p) = sum_t a_r(t)^2, a_r = r-fold conv of indicator(S) mod p."""
    base = defaultdict(int)
    for s in S:
        base[s % p] += 1
    a = dict(base)
    for _ in range(r - 1):
        a = conv_mod(a, base, p)
    return sum(c * c for c in a.values())

def energy_C(S, r):
    """E_r(C): char-0 (cyclotomic) additive energy of mu_n via the ANTIPODAL REDUCTION.

    CORRECTION (2026-06-20): the original naive integer-lift `conv_Z` of residue reps
    in [0,p) was WRONG at r>=4 — it counts integer-sum coincidences of residue
    representatives, NOT the true cyclotomic vanishing-subset-sum count. It disagreed
    with RESULTS-444-RHO-ANTITONE (E_4(C) naive=4650240 vs correct=4649680). Replaced
    with the in-tree antipodal reduction (see probe_444_rho_antitone_recompute.Er_C_2power
    and probe_charp_wraparound_logconcave_Q_v2.py). The wraparound log-concavity verdict
    is ROBUST: it holds under the corrected E_r(C) too (v2 confirms).

    For n = 2^k, z^a -> +e_a (a<n/2) or -e_{a-n/2} (a>=n/2); E_r(C) = sum_v c_v^2 over the
    r-fold convolution in Z^{n/2}. Requires S ordered by generator power so index a = exponent.
    """
    n = len(S)
    half = n // 2
    from collections import Counter
    units = []
    for a in range(n):
        units.append((a, 1) if a < half else (a - half, -1))
    c = Counter({tuple([0] * half): 1})
    for _ in range(r):
        nc = Counter()
        for v, m in c.items():
            for (idx, sgn) in units:
                w = list(v); w[idx] += sgn; nc[tuple(w)] += m
        c = nc
    return sum(m * m for m in c.values())

def main():
    # prize-regime instances: n = 2^a, p ~ n^4 (>> n^3), several structured primes
    cases = [
        (8,   4073),    # beta_eff ~3.67
        (8,   12289),   # Fermat-ish 3*2^12+1
        (16,  65537),   # Fermat F4
        (16,  40961),   # 5*2^13+1
        (32,  1048609), # ~2^20
        (32,  786433),  # 3*2^18+1
        (64,  2752513), # 21*2^17+1, 64 | p-1
    ]
    print("# probe_charp_wraparound_logconcave_Q  (#444)")
    print("# W_r = E_r(F_p) - E_r(C); test W_r*W_{r+2} <= W_{r+1}^2  =>  Q(r)>=2 W_{r+1}^2 >=0")
    all_lc = True
    all_Q = True
    for n, p in cases:
        if (p - 1) % n != 0:
            print(f"## n={n} p={p}: SKIP (n does not divide p-1)")
            continue
        S = order_subgroup(p, n)
        # compute energies up to r where the Z-convolution stays tractable
        rmax = 6 if n <= 16 else (5 if n == 32 else 4)
        W = {}
        ok_base = True
        for r in range(1, rmax + 1):
            efp = energy_Fp(S, p, r)
            ec  = energy_C(S, r)
            w = efp - ec
            W[r] = w
            if w < 0:
                ok_base = False
        print(f"## n={n} p={p}  rmax={rmax}  W_r>=0 all: {ok_base}")
        for r in range(1, rmax + 1):
            print(f"   W_{r} = {W[r]}")
        # log-concavity + Q at each interior r
        for r in range(1, rmax - 1):
            s = 2 * r + 1
            lhs = W[r] * W[r + 2]
            rhs = W[r + 1] ** 2
            lc = lhs <= rhs
            Q = (s + 2) * W[r + 1] ** 2 - s * W[r] * W[r + 2]
            margin_lb = 2 * W[r + 1] ** 2  # the guaranteed lower bound IF lc holds
            all_lc = all_lc and lc
            all_Q = all_Q and (Q >= 0)
            tag = "LC-ok" if lc else "LC-FAIL"
            qtag = "Q>=0" if Q >= 0 else "Q<0!!"
            print(f"   r={r} s={s}: W_r*W_r+2={lhs}  W_r+1^2={rhs}  [{tag}]   "
                  f"Q={Q} [{qtag}]  (lb if LC: {margin_lb})")
    print()
    print(f"=== VERDICT: wraparound log-concavity holds everywhere = {all_lc} ;  Q>=0 everywhere = {all_Q} ===")
    print("If LC=True everywhere: Q>=0 is DISCHARGED by the structural lemma "
          "(s+2)wb^2 - s wa wc >= 2 wb^2 >= 0 under wa*wc<=wb^2.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
