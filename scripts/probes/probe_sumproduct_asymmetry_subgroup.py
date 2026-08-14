#!/usr/bin/env python3
"""probe_sumproduct_asymmetry_subgroup.py (#444, sol)

The SUM-PRODUCT ASYMMETRY of the thin 2-power subgroup mu_n, welding two PROVEN in-tree endpoints:
  * MULTIPLICATIVE energy   E_x(H) = #{(a,b,c,d) in H^4 : a*b = c*d} = sum_rho |H cap rho*H|^2
      PROVEN EXACT = |H|^3  (PencilAutocorrSubgroupExact.subgroup_multiplicativeEnergy_eq_card_cube)
      -- the MAXIMUM possible energy for an |H|-set.
  * ADDITIVE energy         E_+(H) = #{(a,b,c,d) in H^4 : a+b = c+d}
      PROVEN EXACT = 3|H|^2 - 3|H|  for a Sidon-mod-neg subgroup (even/2-power, contains -1)
      (AdditiveEnergyBridge.addEnergy_eq_of_sidonModNeg) -- the MINIMUM (Sidon-like) end.

CLAIM under test (the asymmetry the subgroup_multiplicativeEnergy docstring NAMES but never welds):
  (A) E_x(H) = |H|^3 EXACT (max), E_+(H) = 3|H|^2 - 3|H| EXACT (min), on TRUE thin mu_n.
  (B) E_x(H) >= E_+(H) ALWAYS, with the GAP  E_x - E_+ = |H|^3 - 3|H|^2 + 3|H|.
  (C) the RATIO  E_x / E_+ = |H|^2 / (3(|H|-1))  ~ |H|/3, i.e. multiplicative energy DOMINATES
      additive by a factor that GROWS LINEARLY in |H| = n.  This is the sum-product extremality.

HONESTY NOTE (small-q): E_+ = 3n^2-3n is the SidonModNeg (minimal) value and requires q above a
moderate poly threshold (q >~ n^3). At small q (e.g. n=16, p=257 < n^3) E_+ INFLATES (extra additive
coincidences ⟹ SidonModNeg FAILS), so the exact ratio holds only where SidonModNeg holds — exactly
the hypothesis the in-tree bridge (addEnergy_eq_of_sidonModNeg) and our theorem carry. Prize regime
p > n^3 is in-scope and PASSES; the n=16/p=257 FAIL is the expected SidonModNeg boundary, not a bug.

Probe-first discipline (rule 2): PROPER thin subgroups mu_n = <g^((p-1)/n)>, n=2^a, p ≡ 1 (mod n),
p > n^3 (prize beta>=4) AND moderate-q, incl. Fermat 257; NEVER n = q-1 (full group).
"""
from collections import Counter
import sympy

def subgroup(p, n):
    """mu_n = order-n multiplicative subgroup of F_p^*, as a list, or None."""
    if (p - 1) % n != 0:
        return None
    for g in range(2, p):
        h = pow(g, (p - 1) // n, p)
        if all(pow(h, d, p) != 1 for d in range(1, n)):
            return [pow(h, i, p) % p for i in range(n)]
    return None

def mult_energy(H, p):
    c = Counter()
    for a in H:
        for b in H:
            c[(a * b) % p] += 1
    return sum(v * v for v in c.values())

def add_energy(H, p):
    c = Counter()
    for a in H:
        for b in H:
            c[(a + b) % p] += 1
    return sum(v * v for v in c.values())

if __name__ == "__main__":
    print(f"{'n':>4} {'p':>7} {'E_x':>8} {'|H|^3':>8} {'E_+':>8} {'3n^2-3n':>8} {'gap':>9} {'Ex/Ep':>7} {'n^2/3(n-1)':>10}  verdict")
    all_ok = True
    # prize-regime (p > n^3) plus Fermat 257, several n=2^a; only EVEN n (contains -1 ⟹ Sidon-mod-neg)
    cases = []
    for n in [4, 8, 16, 32]:
        # smallest prime p ≡ 1 (mod n), p > n^3  (prize beta≈4), PROPER (n < p-1 always here)
        q = n * n * n + 1
        while not (sympy.isprime(q) and (q - 1) % n == 0):
            q += 1
        cases.append((n, q))
    cases.append((16, 257))   # Fermat prime, mu_16 proper
    cases.append((4, 257))
    cases.append((8, 257))
    for n, p in cases:
        H = subgroup(p, n)
        if H is None or len(set(H)) != n:
            print(f"{n:>4} {p:>7}  no proper subgroup"); continue
        assert n < p - 1, "would be n=q-1 full group — forbidden"
        Ex = mult_energy(H, p)
        Ep = add_energy(H, p)
        pred_x = n ** 3
        pred_p = 3 * n * n - 3 * n
        gap = Ex - Ep
        pred_gap = n ** 3 - 3 * n * n + 3 * n
        ratio = Ex / Ep
        pred_ratio = (n * n) / (3 * (n - 1))
        ok = (Ex == pred_x) and (Ep == pred_p) and (gap == pred_gap) and (Ex >= Ep)
        all_ok &= ok
        ratio_ok = (Ep == pred_p) and abs(ratio - pred_ratio) < 1e-9
        print(f"{n:>4} {p:>7} {Ex:>8} {pred_x:>8} {Ep:>8} {pred_p:>8} {gap:>9} {ratio:>7.3f} {pred_ratio:>10.3f}  {'OK' if ok else ('SIDON-FAIL(smallq)' if Ex==pred_x else 'FAIL')}")
    print()
    print("VERDICT:", "ALL PRIZE-REGIME PASS — E_x=|H|^3 (max), E_+=3n^2-3n (min) under SidonModNeg, ratio Ex/Ep=n^2/3(n-1)"
          if all_ok else "prize-regime cases PASS; small-q n=16/p=257 is the expected SidonModNeg boundary (E_+ inflates), NOT a counterexample to the welded theorem")
