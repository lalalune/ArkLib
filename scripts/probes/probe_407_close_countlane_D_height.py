# probe_407_close_countlane_D_height.py
#
# OPEN ITEM (directive): PROVE the count-lane D height bound.
#
# Goal: determine whether the E2VanishRigidityModP fold+resultant machinery
# (which proves e2_extra_solution_threshold <= (n^2+n)^{n/2}) extends to the
# COUNT-LANE system {e_1(S)=0, e_3(S)=0, F(e_m(S)) != 0} over S subset mu_n.
#
# Key structural question:
#   - In E2VanishRigidityModP, the bad condition e_2(S)=0 is a SINGLE integer
#     polynomial equation R_U(zeta)=0 indexed by the exponent set U.
#     The fold gives ||fold||_1 <= |U|^2+|U| <= n^2+n, hence any NEW mod-p root
#     forces p <= (n^2+n)^{n/2}.  The threshold is UNIFORM over U.
#   - The COUNT lane has TWO vanishing conditions (e_1=0 AND e_3=0) plus a
#     NON-vanishing F(e_m)!=0.  We must ask: what single integer D do all
#     "floor-bad" primes divide, and what is its height?
#
# Two height notions we must NOT conflate (this is the directive's load-bearing point):
#   (H1) max bad prime  <= Threshold  (proven crude:  (n^2+n)^{n/2} = 2^{O(n log n)})
#   (H2) # distinct bad primes  <= log2(D)  (the PIGEONHOLE bound the floor needs)
# These are DIFFERENT.  (H1) follows from the e2-species fold bound directly.
# (H2) requires D itself to have height 2^{O(n log n)}, i.e. log2(D)=O(n log n).
# A prime can be <= 2^{O(n log n)} and still there be 2^{O(n log n)} of them, so
# (H1) does NOT give (H2).  (H2) needs D = a SINGLE integer of bounded height.
#
# This probe:
#   (A) Builds the e2-style integer relation for the e_1=0 condition and the
#       e_3=0 condition per exponent-set U, folds each to deg<n/2, measures ||.||_1.
#   (B) Computes, for n=8 and n=16, the EXACT set of "floor-bad" primes
#       (p ===1 mod n, odd, where some antipodal-free gap-valid config gives e_2 NOT in Sigma),
#       and the integer D = product structure / resultant they divide, exactly.
#   (C) Counts #distinct bad primes and compares to n*log(n) and to log2(D).
#   (D) Reports whether the SINGLE-polynomial fold machinery of E2VanishRigidityModP
#       transfers, or whether the system structure (two conditions) breaks it.

import sympy as sp
from itertools import combinations, product

def analyze(n):
    HALF = n // 2
    z = sp.symbols('z')
    Phi = sp.Poly(sp.cyclotomic_poly(n, z), z)   # degree HALF = n/2

    # element-sum of {zeta^e} reduced via zeta^HALF = -1 to a length-HALF integer vector
    def vec(exps):
        v = [0] * HALF
        for e in exps:
            e %= n
            if e < HALF:
                v[e] += 1
            else:
                v[e - HALF] -= 1
        return v
    def poly(v):
        return sp.Poly(sum(int(c) * z**l for l, c in enumerate(v)), z)
    def Nrm(v):
        return abs(int(sp.resultant(Phi.as_expr(), poly(v).as_expr(), z)))
    def l1(v):
        return sum(abs(int(c)) for c in v)

    # antipodal-free configs of given size: choose 'size' antipodal pairs, one elt each
    def configs(size):
        out = []
        for pr in combinations(range(HALF), size):
            for signs in product([0, 1], repeat=size):
                out.append([pr[i] + (HALF if signs[i] else 0) for i in range(size)])
        return out

    # ---- (A) fold l1 masses for the e_1=0 (linear) relation and e_3=0 relation ----
    # e_1(S)=0  <=> sum_{u in S} u = 0  <=> the integer vector vec(exps) ==0 in Z[zeta]
    #   relation poly is R1_U(X) = sum_{i in U} X^i ; its fold-l1 <= |U| <= n.
    # e_3(S)=0  <=> sum u^3 = 0 ; relation R3_U(X)=sum X^{3i mod ...}, fold-l1 <= |U| <= n.
    # The e_m=e_2 VALUE is e_2(S) = -1/2 sum u^2 ; F(e_2)=prod_{sigma in Sigma}(e_2 - sigma).
    #
    # CRITICAL: e_1=0 and e_3=0 are LINEAR (||.||_1 <= n each), MUCH smaller than the
    # QUADRATIC e_2 relation (||.||_1 <= n^2+n). So the per-config fold masses are SMALL.
    sizes = [s for s in range(2, HALF + 1)] if n <= 16 else [2, 3]
    max_l1_e1 = 0
    max_l1_e3 = 0
    for size in sizes:
        for exps in configs(size):
            a = vec(exps)               # = sum u   (the e_1 relation value as Z[zeta] elt)
            b = vec([3 * e for e in exps])  # = sum u^3
            max_l1_e1 = max(max_l1_e1, l1(a))
            max_l1_e3 = max(max_l1_e3, l1(b))

    print(f"\n=== n={n} (HALF={HALF}, deg Phi_n = {HALF}) ===")
    print(f"  per-config fold-l1 of e_1 relation (sum u):    max over configs = {max_l1_e1}  (<= n = {n})")
    print(f"  per-config fold-l1 of e_3 relation (sum u^3):  max over configs = {max_l1_e3}  (<= n = {n})")
    print(f"  e2-style QUADRATIC relation fold-l1 bound:     n^2+n = {n*n+n}")
    print(f"  E2 single-poly crude threshold (n^2+n)^(n/2) = {n*n+n}^{HALF} = 2^{HALF*sp.log(n*n+n,2).evalf():.1f}")

    # ---- (B) EXACT floor-bad primes for n via the candidate-prime method ----
    # A floor-bad prime p (odd, ===1 mod n) is one where SOME antipodal-free config U
    # has e_1=e_3=0 (mod p) but e_2(U) NOT in Sigma_{|U|/2}.  Candidate primes divide
    # gcd(N(sum u), N(sum u^3)).  Collect the FULL candidate set and the actual bad set.
    cand = {}   # prime -> set of (size, config) witnessing candidacy
    for size in sizes:
        for exps in configs(size):
            a = vec(exps); b = vec([3 * e for e in exps])
            if all(c == 0 for c in a) or all(c == 0 for c in b):
                continue  # char-0 relation, not primitive over any p
            Na, Nb = Nrm(a), Nrm(b)
            g = sp.gcd(Na, Nb)
            if g == 0:
                continue
            for pr, _ in sp.factorint(g).items():
                if pr % 2 == 1 and pr % n == 1:
                    cand.setdefault(int(pr), set()).add((size, tuple(exps)))

    cand_primes = sorted(cand.keys())

    # Sigma_k mod p
    def sigma_set(k, h, p):
        munhalf = [pow(h, 2 * l, p) for l in range(HALF)]
        return set(sum(W) % p for W in combinations(munhalf, k))
    def h_of(p):
        e = (p - 1) // n
        for a in range(2, p):
            hh = pow(a, e, p)
            if pow(hh, n, p) == 1 and pow(hh, HALF, p) == p - 1:
                return hh
        return None

    actual_bad = []
    for p in cand_primes:
        h = h_of(p)
        if h is None:
            continue
        i2 = pow(2, p - 2, p)
        hit = False
        for size in sizes:
            k = size // 2
            Sig = sigma_set(k, h, p)
            for exps in configs(size):
                us = [pow(h, e % n, p) for e in exps]
                if sum(us) % p != 0:
                    continue
                if sum(pow(u, 3, p) for u in us) % p != 0:
                    continue
                e2 = (-i2 * sum(pow(u, 2, p) for u in us)) % p
                if e2 not in Sig:
                    actual_bad.append(p)
                    hit = True
                    break
            if hit:
                break

    actual_bad = sorted(set(actual_bad))
    print(f"  candidate odd primes ===1 mod n (divide gcd(N(sum u),N(sum u^3))): {cand_primes}")
    print(f"  ACTUAL floor-bad primes (e_2 NOT in Sigma for some config):        {actual_bad}")

    # ---- (C) D = the integer the bad primes divide; height + factor count ----
    # Honest D for the count lane = lcm over configs of gcd(N(sum u), N(sum u^3))
    # restricted to its ===1 mod n odd part (the "obstruction integer" of the system).
    D = 1
    for p in cand:
        D *= p  # squarefree product of candidate primes (radical of the obstruction)
    logD = float(sp.log(D, 2).evalf()) if D > 1 else 0.0
    nfac = len(cand_primes)
    nlogn = n * float(sp.log(n, 2).evalf()) if n > 1 else 0.0
    print(f"  radical(D) = product of candidate primes = {D}")
    print(f"  log2(radical D) = {logD:.2f};   #distinct candidate primes = {nfac}")
    print(f"  #distinct ACTUAL bad primes = {len(actual_bad)}")
    print(f"  target O(n log n) = n*log2(n) = {nlogn:.1f}")
    print(f"  => #bad primes ({len(actual_bad)}) <= O(n log n) ({nlogn:.0f}) ?  {len(actual_bad) <= nlogn}")

    return {
        'n': n,
        'max_l1_e1': max_l1_e1,
        'max_l1_e3': max_l1_e3,
        'cand_primes': cand_primes,
        'actual_bad': actual_bad,
        'n_cand': nfac,
        'n_actual': len(actual_bad),
        'logD': logD,
        'nlogn': nlogn,
    }

if __name__ == '__main__':
    res = {}
    for n in [8, 16]:
        res[n] = analyze(n)

    print("\n\n===== SUMMARY: does E2 fold machinery give the count-lane D-height? =====")
    print(f"{'n':>4} {'#cand':>6} {'#bad':>5} {'log2 radD':>10} {'n log n':>8} {'l1(e1)':>7} {'l1(e3)':>7}")
    for n in [8, 16]:
        r = res[n]
        print(f"{n:>4} {r['n_cand']:>6} {r['n_actual']:>5} {r['logD']:>10.2f} {r['nlogn']:>8.1f} {r['max_l1_e1']:>7} {r['max_l1_e3']:>7}")
