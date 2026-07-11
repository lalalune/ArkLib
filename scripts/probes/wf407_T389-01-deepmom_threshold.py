"""
wf407 / T389-01-deepmom : the EXACT char-p->char-0 threshold law for E_r(mu_n).

KEY QUESTION (Q2 sharpened): the char-0 bound E_r^(0) <= (2r-1)!! n^r is a THEOREM
(Bessel lemma, never fails). The wall is therefore ENTIRELY the char-p transfer:
for which primes p does E_r^(p)(mu_n) = E_r^(0)(mu_n)?

We compute, for fixed (n,r), the EXACT smallest threshold prime tau_{n,r} above which
E_r^(p) = E_r^(0) for ALL primes p>=tau (p ≡ 1 mod n). The defect E_r^(p) - E_r^(0) >= 0
is caused by "spurious" mod-p vanishing sums: r-subset multisets of mu_n whose signed
sum is != 0 in Z[zeta_n] but == 0 mod p. We characterize the threshold and fit it to
the claimed law tau_r ~ n^{(r+3)/2}, i.e. r_max = 2 log_n p - 3.
"""

import itertools
from math import log
from collections import Counter
from sympy import primerange


def is_prim_root(g, p):
    x = 1
    seen = 0
    val = 1
    target = p - 1
    # order check via repeated mult; cheap for small p
    cur = g % p
    order = 1
    while cur != 1:
        cur = (cur * g) % p
        order += 1
        if order > p:
            return False
    return order == p - 1


def mu_n_charp(n, p):
    g = None
    for cand in range(2, p):
        if is_prim_root(cand, p):
            g = cand
            break
    h = pow(g, (p - 1) // n, p)
    return [pow(h, k, p) for k in range(n)]


def energy_charp(n, r, p):
    roots = mu_n_charp(n, p)
    sums = Counter()
    for tup in itertools.product(roots, repeat=r):
        sums[sum(tup) % p] += 1
    return sum(c * c for c in sums.values())


def root_vec_char0(n, k):
    half = n // 2
    v = [0] * half
    sign = 1 if (k // half) % 2 == 0 else -1
    v[k % half] += sign
    return v


def energy_char0(n, r):
    half = n // 2
    rc = [root_vec_char0(n, k) for k in range(n)]
    sums = Counter()
    for tup in itertools.product(range(n), repeat=r):
        v = [0] * half
        for k in tup:
            t = rc[k]
            for j in range(half):
                v[j] += t[j]
        sums[tuple(v)] += 1
    return sum(c * c for c in sums.values())


print("=" * 80)
print("EXACT char-p -> char-0 THRESHOLD for E_r(mu_n)")
print("For each (n,r): list E_r^(p) over ALL p<=P, p≡1 mod n, mark = / != char-0.")
print("threshold tau_{n,r} = least p above which it stays = char-0 (within scan).")
print("=" * 80)

# scan primes p ≡ 1 mod n up to a cap
def primes_1_mod_n(n, cap):
    return [p for p in primerange(2, cap) if p % n == 1]

results = {}
for n in (4, 8, 16):
    e0_by_r = {}
    cap = 4000 if n <= 8 else 6000
    plist = primes_1_mod_n(n, cap)
    rmax = 4 if n == 4 else (4 if n == 8 else 3)
    print(f"\n##### n = {n},  primes p≡1 mod {n} up to {cap}: {len(plist)} primes #####")
    for r in range(2, rmax + 1):
        if n ** r > 2_500_000:
            continue
        e0 = energy_char0(n, r)
        e0_by_r[r] = e0
        clean_from = None
        defects = []
        for p in plist:
            ep = energy_charp(n, r, p)
            if ep == e0:
                if clean_from is None:
                    clean_from = p
            else:
                clean_from = None  # reset: a later defect means not yet clean
                defects.append((p, ep))
        # threshold = smallest p s.t. all p'>=p (in scan) are clean
        # recompute: last defect prime
        last_defect = defects[-1][0] if defects else None
        tau = (last_defect + 1) if last_defect is not None else plist[0]
        results[(n, r)] = (e0, tau, last_defect, len(defects), len(plist))
        # predicted threshold n^{(r+3)/2}
        pred = n ** ((r + 3) / 2)
        print(f"  r={r}: E_r^(0)={e0:>8}  #defect-primes={len(defects):>3}/{len(plist)}"
              f"  last_defect_p={str(last_defect):>6}  -> clean threshold tau≈{tau:>6}"
              f"   |  n^{{(r+3)/2}}={pred:>12.0f}  log_n(last_defect)={('%.3f'%log(last_defect,n)) if last_defect else 'n/a'}")

print()
print("=" * 80)
print("FIT: does the empirical threshold obey  tau_r ~ n^{(r+3)/2}  <=>  r_max=2 log_n p - 3 ?")
print("=" * 80)
print(f"{'(n,r)':>10} {'last_defect_p':>14} {'log_n(p_def)':>13} {'(r+3)/2':>9} {'2 log_n(p)-3':>13}")
for (n, r), (e0, tau, ld, nd, npl) in sorted(results.items()):
    if ld is None:
        print(f"{(n,r)!s:>10} {'(none)':>14} {'-':>13} {(r+3)/2:>9.1f} {'-':>13}")
        continue
    lnp = log(ld, n)
    print(f"{(n,r)!s:>10} {ld:>14} {lnp:>13.3f} {(r+3)/2:>9.1f} {2*lnp-3:>13.3f}")
print()
print("Reading: if last-defect prime p_def has log_n(p_def) ~ (r+3)/2, the threshold law")
print("tau_r ~ n^{(r+3)/2} holds, i.e. the char-0 value is reliable EXACTLY for")
print("r <= r_max = 2 log_n p - 3. Compare col (r+3)/2 against log_n(p_def): the LARGEST")
print("p giving a defect at order r tells you the prize-relevant validity boundary.")
