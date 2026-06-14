"""
R2 verification: does Kambiré's parameter optimization maximize the bad count
at the delta* threshold? Verify the chain in his 'Setting parameters' + 'Counting' sections.

Kambiré's parameter choices (lines 63-96):
  - rho = u/2^v, u < 2^{v-1}, rate
  - L(rho,C) = max{ C/(rho log(1/2rho)),  (9/2) log 8 }
  - K = power of 2 in [L, 2L]
  - s = 2^alpha (alpha large enough: alpha>=v, alpha>=log2 K, K<=2^alpha)
  - r = rho*s + 2 = u*2^{alpha-v} + 2
  - m = 2^{2^alpha/K - alpha}  (power of 2)
  - n = s*m,  k = (r-2)*m
  - delta = 1 - r/s, so eta = (1-rho)-delta = 2/s

Identities claimed:
  (1) rho = (r-2)/s = (r-2)m/(sm) = k/n
  (2) K log2(n) = s   [the load-bearing one: log2 n = s/K]

Bad-count:  a = |H^{(+r)}(mu_s)| = C(s/2, r) >= (s/(2r))^r ~ (1/2rho)^{rho s + 2}
            >= n^{rho K log(1/2rho)} * (1/2rho)^2 > n^C.
"""
import math
from math import comb, log, log2

def check_identities(u, v, C):
    rho = u / 2**v
    assert 0 < rho < 0.5
    assert u < 2**(v-1), f"u={u} must be < 2^(v-1)={2**(v-1)}"
    L = max(C / (rho * log(1/(2*rho))), 4.5*log(8))
    # K power of 2 in [L,2L]
    K = 2**(math.floor(log2(L))+1)
    assert L <= K <= 2*L, f"K={K} not in [{L},{2*L}]"
    rows = []
    for alpha in range(max(v, math.ceil(log2(K))), max(v, math.ceil(log2(K)))+6):
        if not (K <= 2**alpha): 
            continue
        s = 2**alpha
        if (2**alpha) % K != 0:  # need K | 2^alpha
            continue
        exp_m = 2**alpha // K - alpha
        if exp_m < 0:
            continue
        m = 2**exp_m
        r = u * 2**(alpha - v) + 2   # = rho*s+2
        assert r == rho*s + 2
        n = s * m
        k = (r-2)*m
        # identity (1)
        id1 = abs(rho - k/n) < 1e-12
        # identity (2): K*log2(n) == s
        id2 = abs(K*log2(n) - s) < 1e-6
        # bad count
        if r <= s//2:
            a = comb(s//2, r)
        else:
            a = 0
        a_lb = (s/(2*r))**r  # Kambiré's lower bound (s/2r)^r
        target = n**C
        rows.append(dict(alpha=alpha, s=s, m=m, r=r, n=n, k=k, K=K,
                         rho=round(rho,4),
                         id1=id1, id2=id2,
                         a=a, a_lb=round(a_lb,2), target_nC=round(target,2),
                         beats_nC = a > target,
                         delta=round(1-r/s,4), eta=round(2/s,5),
                         capacity_gap_2_over_s=round(2/s,5)))
    return rho, K, L, rows

print("="*100)
print("KAMBIRE PARAMETER-OPTIMIZATION VERIFICATION")
print("="*100)
for (u,v,C) in [(1,2,1.0),(1,3,1.0),(1,2,2.0),(3,3,1.0),(1,4,1.0)]:
    rho,K,L,rows = check_identities(u,v,C)
    print(f"\n--- rho=u/2^v = {u}/{2**v} = {rho}, C={C} ---  L={L:.3f}, K={K}")
    for row in rows:
        print(f"  alpha={row['alpha']:2d} s={row['s']:5d} m={row['m']:8d} r={row['r']:4d} "
              f"n={row['n']:10d} k={row['k']:9d} | id1(rho=k/n)={row['id1']} "
              f"id2(Klog2n=s)={row['id2']} | a=C(s/2,r)={row['a']:>6} a_lb={row['a_lb']:>10} "
              f"n^C={row['target_nC']:>12} beats_n^C={row['beats_nC']} | delta={row['delta']} eta=2/s={row['eta']}")
