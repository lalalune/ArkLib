#!/usr/bin/env python3
"""
PROBE: the clique-decay pigeonhole bound D*(m) <= C(n,k+1)/C(k+m,k+1) and its
asymptotic VACUITY (lalalune's #444 22:13 clique reformulation).

CORE FACT being formalized (pure combinatorics, NO cyclotomic structure):
 A (k+m)-clique = a (k+m)-set all of whose (k+1)-subsets lie in a single level set L_gamma.
 So if L_gamma contains a (k+m)-clique it contains >= C(k+m, k+1) of its (k+1)-subsets.
 Total (k+1)-subsets = C(n, k+1) = sum_gamma |L_gamma|.
 D*(m) = #{gamma : L_gamma has a (k+m)-clique}. Each such gamma 'uses' >= C(k+m,k+1) of the
 (k+1)-subsets, and a (k+1)-subset has ONE gamma value, so the used sets are DISJOINT across
 gamma. Hence  D*(m) * C(k+m, k+1) <= C(n, k+1)  =>  D*(m) <= C(n,k+1)/C(k+m,k+1).
 m* = first m with D*(m) <= n. The pigeonhole-implied m_bound = first m with RHS <= n.
We VERIFY: (1) the disjoint-budget bound is a real upper bound (vs lalalune's exact envelope),
           (2) m_bound ~ n (vacuous) while true m* ~ log n.
NEVER uses n=q-1; this is a structural subset-count identity independent of the prime.
"""
from math import comb, log


def pigeonhole_Dstar_upper(n, k, m):
    return comb(n, k + 1) / comb(k + m, k + 1)


def m_bound_pigeonhole(n, k):
    m = 1
    while m <= n - k:
        if pigeonhole_Dstar_upper(n, k, m) <= n:
            return m
        m += 1
    return n - k


print("=== n=16, envelope (m=2..5)=[89,9,9,0]; pigeonhole upper bound per k ===")
env16 = {2: 89, 3: 9, 4: 9, 5: 0}
for k in [3, 4, 5, 6]:
    vals = {m: round(pigeonhole_Dstar_upper(16, k, m), 1) for m in range(2, 6)}
    dominates = all(vals[m] >= env16[m] for m in range(2, 5))
    print(f" k={k}: bound={vals}  dominates_env(m2..4)={dominates}  m_bound(<=n)={m_bound_pigeonhole(16,k)}")

print()
print("=== vacuity: true m* vs pigeonhole m_bound, k=n/4 (binding regime) ===")
true_mstar = {8: 3, 16: 3, 32: 5}
for n in [8, 16, 32, 64, 128, 256]:
    k = max(1, n // 4)
    mb = m_bound_pigeonhole(n, k)
    frac = mb / n
    note = f" true m*={true_mstar[n]}" if n in true_mstar else ""
    print(f" n={n:4d} k={k:3d}: pigeonhole m_bound={mb:4d}  m_bound/n={frac:.3f}  (vacuous if ->1){note}")

print()
print("=== the crossing law: m_bound ~ n^(1-1/(k+1)) -> n as claimed ===")
for n in [16, 32, 64, 128, 256, 512]:
    k = max(1, n // 4)
    mb = m_bound_pigeonhole(n, k)
    approx = n ** (1 - 1 / (k + 1))
    print(f" n={n:4d} k={k:3d}: m_bound={mb:4d}  n^(1-1/(k+1))={approx:.1f}  n-4ln n={n-4*log(n):.1f}")
