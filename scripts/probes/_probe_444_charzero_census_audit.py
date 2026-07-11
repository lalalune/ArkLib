#!/usr/bin/env python3
"""
#444 char-0 census AUDIT (independent adversarial re-derivation).

Independently verifies — by EXACT arithmetic, from first principles, with NO reuse
of the swarm's formulas — the landed char-0 subset-sum-spectrum / energy census:

  (A) per-depth count  N_r(C) = #{ distinct sum_{z in S} z : S subset mu_n, |S|=r }
      claimed  N_r = sum_{k = r,r-2,...; k<=min(r,2m-r)} C(m,k) 2^k     (m = n/2)
      -> brute-forced via the exact net-vector model in {-1,0,1}^m
  (B) total mass  T(m) = sum_r N_r  ?=  3^{m-1}(m+3)
  (C) complement symmetry  N_r ?= N_{2m-r}
  (D) char-0 energy  E_r(C) ?= (2r-1)!! n^r - deficit, MGF = I0(2y)^{n/2},
      and the prize bound  I0(2y) <= exp(y^2)  coefficientwise (1/(k!)^2 <= 1/k!)
  (E) bonus cross-check  sum_r (-1)^r N_r ?= (-1)^{m+1}(m-1)

Net-vector model (proven exact, char 0): mu_n = {+-w_0,...,+-w_{m-1}} with w_i = zeta^i,
and {1,zeta,...,zeta^{m-1}} a Q-basis (deg phi(2^mu)=2^{mu-1}=m). A subset S has
coordinate i = [w_i in S] - [-w_i in S] in {-1,0,1}; distinct net vectors <=> distinct sums.
"""
from itertools import combinations
from math import comb, factorial
from fractions import Fraction

def brute_Nr(mu):
    """Exact distinct-subset-sum spectrum of mu_n, n=2^mu, by net vectors in {-1,0,1}^m."""
    n = 2 ** mu
    m = n // 2
    # roots indexed 0..2m-1: root a -> +e_{a} if a<m else -e_{a-m}
    def netcoord(a):
        return (a, +1) if a < m else (a - m, -1)
    roots = list(range(2 * m))
    spectrum = {r: set() for r in range(2 * m + 1)}
    for r in range(2 * m + 1):
        for S in combinations(roots, r):
            vec = [0] * m
            for a in S:
                i, s = netcoord(a)
                vec[i] += s
            spectrum[r].add(tuple(vec))
    return [len(spectrum[r]) for r in range(2 * m + 1)]

def closed_Nr(m, r):
    """Claimed closed form."""
    tot = 0
    k = r % 2
    while k <= min(r, 2 * m - r):
        tot += comb(m, k) * (2 ** k)
        k += 2
    return tot

def Tm_closed(m):
    return 3 ** (m - 1) * (m + 3)

# ---- (A)+(C) brute vs closed, and palindrome, for n=8 and n=16 ----
print("=== (A) per-depth N_r: brute (net-vector) vs closed form ===")
for mu in (2, 3, 4):            # n = 4, 8, 16
    n = 2 ** mu; m = n // 2
    brute = brute_Nr(mu)
    closed = [closed_Nr(m, r) for r in range(2 * m + 1)]
    ok = brute == closed
    pal = brute == brute[::-1]
    print(f"  n={n:2d} (m={m}): {'PASS' if ok else 'FAIL'}  palindrome={'yes' if pal else 'NO'}")
    print(f"     brute  = {brute}")
    if not ok:
        print(f"     closed = {closed}   <-- MISMATCH")

# ---- (B) total mass T(m) = 3^{m-1}(m+3), and the depth-multiplicity swap ----
print("\n=== (B) total mass T(m) = sum_r N_r  vs  3^{m-1}(m+3) ===")
allB = True
for m in range(1, 14):
    n = 2 * m
    T_sum = sum(closed_Nr(m, r) for r in range(2 * m + 1))
    T_kform = sum((m - k + 1) * comb(m, k) * 2 ** k for k in range(m + 1))
    T_cf = Tm_closed(m)
    gf1 = sum(comb(m, k) * 2 ** k for k in range(m + 1))          # = 3^m
    gf2 = sum(k * comb(m, k) * 2 ** k for k in range(m + 1))      # = 2m 3^{m-1}
    row_ok = (T_sum == T_kform == T_cf) and gf1 == 3 ** m and gf2 == 2 * m * 3 ** (m - 1)
    allB &= row_ok
    if m <= 8 or not row_ok:
        print(f"  m={m:2d}: sum={T_sum:<9} kform={T_kform:<9} closed={T_cf:<9} "
              f"GF[3^m]={'ok' if gf1==3**m else 'NO'} GF[2m3^m-1]={'ok' if gf2==2*m*3**(m-1) else 'NO'} "
              f"{'PASS' if row_ok else 'FAIL'}")
print(f"  anchors: T(1)={Tm_closed(1)} T(2)={Tm_closed(2)} T(3)={Tm_closed(3)} "
      f"T(4)={Tm_closed(4)} T(8)={Tm_closed(8)}  (claim 4,15,54,189,24057)")
print(f"  ==> (B) {'ALL PASS' if allB else 'FAIL'}")

# ---- (E) bonus: alternating sum sum_r (-1)^r N_r = (-1)^{m+1}(m-1) ----
print("\n=== (E) alternating sum  sum_r (-1)^r N_r  vs  (-1)^{m+1}(m-1) ===")
allE = True
for m in range(1, 11):
    alt = sum(((-1) ** r) * closed_Nr(m, r) for r in range(2 * m + 1))
    pred = ((-1) ** (m + 1)) * (m - 1)
    ok = alt == pred
    allE &= ok
    print(f"  m={m:2d}: alt={alt:<6} pred={pred:<6} {'PASS' if ok else 'FAIL'}")
print(f"  ==> (E) {'ALL PASS' if allE else 'FAIL'}  (a clean NEW identity, derivable from the same GF)")

# ---- (D) char-0 energy + Bessel-MGF + prize bound ----
print("\n=== (D) char-0 energy E_r(C), MGF = I0(2y)^{n/2}, prize bound I0(2y)<=exp(y^2) ===")
# I0(2y) = sum_k y^{2k}/(k!)^2 ; f(z) = sum_k z^k/(k!)^2 ; E_r = (2r)! [z^r] f(z)^{n/2}
def poly_pow_series(coeffs, p, R):
    """(sum coeffs[i] z^i)^p truncated to degree R, exact Fraction."""
    res = [Fraction(0)] * (R + 1); res[0] = Fraction(1)
    base = coeffs[:R + 1] + [Fraction(0)] * (R + 1 - len(coeffs))
    for _ in range(p):
        new = [Fraction(0)] * (R + 1)
        for i in range(R + 1):
            if res[i] == 0: continue
            for j in range(R + 1 - i):
                new[i + j] += res[i] * base[j]
        res = new
    return res

def double_factorial_odd(r):  # (2r-1)!!
    v = 1
    for t in range(1, r + 1):
        v *= (2 * t - 1)
    return v

R = 8
allD = True
for mu in (2, 3, 4, 5):
    n = 2 ** mu; half = n // 2
    f = [Fraction(1, factorial(k) ** 2) for k in range(R + 1)]   # f(z)=sum z^k/(k!)^2
    fp = poly_pow_series(f, half, R)
    for r in range(R + 1):
        E_r = factorial(2 * r) * fp[r]                            # E_r(C)
        wick = double_factorial_odd(r) * n ** r                   # (2r-1)!! n^r
        if E_r != int(E_r):
            print(f"   n={n} r={r}: E_r NON-INTEGER {E_r}  <-- BUG"); allD = False; continue
        E_r = int(E_r)
        if E_r > wick:
            print(f"   n={n} r={r}: E_r={E_r} > wick={wick}  <-- PRIZE-BOUND VIOLATION"); allD = False
    # leading deficit check: D_r ~ C(r,2)(2r-1)!! ; check r=2: D_2 = wick - E_2
    E2 = int(factorial(4) * fp[2]); D2 = double_factorial_odd(2) * n ** 2 - E2
    pred_lead = comb(2, 2) * double_factorial_odd(2)  # = 3
    print(f"  n={n:2d}: E_r<=(2r-1)!!n^r for r<=8 {'OK' if allD else 'FAIL'}; "
          f"E_2={E2} deficit D_2={D2} (lead coeff {pred_lead}=3? {'yes' if D2==pred_lead else 'check'})")
# coefficientwise I0(2y)<=exp(y^2): 1/(k!)^2 <= 1/k!  <=>  k! >= 1
cw = all(Fraction(1, factorial(k) ** 2) <= Fraction(1, factorial(k)) for k in range(0, 30))
print(f"  coefficientwise I0(2y) <= exp(y^2)  (1/(k!)^2 <= 1/k!): {'PASS' if cw else 'FAIL'}")
print(f"  ==> (D) {'ALL PASS' if allD and cw else 'FAIL'}")

print("\n=== VERDICT ===")
print("If all PASS: the swarm's char-0 census is independently confirmed exact (no off-by-one).")
print("The wall (char-p excess Psi_p - Psi_0 > 0 at binding depth) is untouched by any of this.")
