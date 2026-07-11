#!/usr/bin/env python3
"""Verify the closed form  |H^{(+r)}(mu_{2^mu})| = #{d in Z^{s/2}: |d|_1<=r, |d|_1 = r mod 2}
(distinct r-fold sums of 2^mu-th roots of unity), then use it to compute the PRIZE-regime worst
subgroup s* and the Lam-Leung norm-bound closure condition q > (2r)^{phi(s*)} at n=2^30, q=n*2^128.
Char-p count = char-0 count for 2r<q (Lam-Leung), so the closed form is the true F_q bad-count proxy."""
import itertools, math
from fractions import Fraction

# ---- exact distinct r-fold sums of s-th roots of unity (s a power of 2) via d-vectors ----
def Hr_brute(s, r):
    # value of sum determined by d_j=m_j-m_{j+s/2}, j<s/2. Enumerate multisets of size r over s roots.
    D = s // 2
    seen = set()
    for combo in itertools.combinations_with_replacement(range(s), r):
        d = [0]*D
        for idx in combo:
            if idx < D: d[idx] += 1
            else: d[idx-D] -= 1
        seen.add(tuple(d))
    return len(seen)

def L1_parity_count(D, r):
    # #{d in Z^D : |d|_1 <= r and |d|_1 == r mod 2}  via DP on partial L1 norm
    # count of d in Z^D with |d|_1 = t : a[t]
    # 1-D generating: f(x)=1+2x+2x^2+... ; D-fold; coeff of x^t
    a = [0]*(r+1); a[0]=1
    for _ in range(D):
        b=[0]*(r+1)
        for t in range(r+1):
            if a[t]==0: continue
            # add a coordinate value v with |v|=u (u=0:1 way, u>=1:2 ways)
            for u in range(0, r-t+1):
                ways = 1 if u==0 else 2
                b[t+u]+=a[t]*ways
        a=b
    return sum(a[t] for t in range(r+1) if (t%2)==(r%2))

print("=== VERIFY closed form  |H^{(+r)}(mu_s)| = L1-ball-parity count ===", flush=True)
ok=True
for s in (4,8,16):
    D=s//2
    for r in range(1, 7):
        h=Hr_brute(s,r); f=L1_parity_count(D,r)
        flag = "OK" if h==f else "**MISMATCH**"
        if h!=f: ok=False
        print(f"  s={s:2d} r={r}: brute={h:6d}  formula={f:6d}  {flag}", flush=True)
print(f"  --> closed form {'VERIFIED' if ok else 'FAILED'}\n", flush=True)

# ---- max over r of the count (full L1 ball, r=D) ----
print("=== max count per subgroup: |H^{(+inf)}(mu_s)| ~ peak; and 2^{s/2} scale ===", flush=True)
for s in (4,8,16,32,64):
    D=s//2
    peak=L1_parity_count(D, D)  # r=D
    print(f"  s={s:3d}: L1count(r=s/2={D}) = {peak}   2^(s/2)={2**D}", flush=True)
print(flush=True)

# ---- PRIZE regime: n=2^30, q=n*2^128, budget=q*eps*=n. For each divisor s|n (power of 2),
#      find r* with L1count(s/2,r*) ~ budget n; that subgroup is "active". Worst s* = largest active s.
#      Then Lam-Leung norm bound: char-p faithful (no spurious) iff q > (2 r*)^{phi(s*)}, phi(2^mu)=s*/2.
print("=== PRIZE: n=2^30, q=n*2^128 (beta~5.27), budget=q*eps*=n=2^30 ===", flush=True)
N_LOG2 = 30                      # n=2^30
Q_LOG2 = N_LOG2 + 128            # q=n*2^128
budget_log2 = N_LOG2             # budget=n
print(f"  log2 n={N_LOG2}, log2 q={Q_LOG2}, log2 budget={budget_log2}", flush=True)
print(f"  {'s(=2^j)':>8} {'r* (L1count~n)':>16} {'2r*':>5} {'phi(s)=s/2':>11} {'(2r*)^(s/2) log2':>17} {'<q?':>5}", flush=True)
worst_s=None
for j in range(1, N_LOG2+1):
    s = 2**j; D = s//2
    # find smallest r with L1count(D,r) >= budget n  (this r is where the subgroup first reaches budget)
    # for large D the count grows fast; use log2 of L1count via incremental until >= budget
    rstar=None
    # L1count(D,r) ~ sum; compute log2 by building up (cap r at D)
    a=[0.0]*(D+1) if D<=200 else None
    # to avoid huge arrays for D up to 2^29, only handle s up to where D manageable; else use approx
    if D<=4096:
        # exact-ish via float DP capped at r<=min(D,80)
        rmax=min(D,80)
        cnt=[0]*(rmax+1); cnt[0]=1
        arr=[0]*(rmax+1); arr[0]=1
        for _ in range(D):
            b=[0]*(rmax+1)
            for t in range(rmax+1):
                if arr[t]==0: continue
                for u in range(0,rmax-t+1):
                    b[t+u]+=arr[t]*(1 if u==0 else 2)
            arr=b
        # cumulative parity count up to r
        for r in range(1,rmax+1):
            tot=sum(arr[t] for t in range(r+1) if t%2==r%2)
            if tot>= 2**budget_log2:
                rstar=r; break
    if rstar is None:
        continue
    phi=s//2
    cond_log2 = phi*math.log2(2*rstar)
    holds = cond_log2 < Q_LOG2
    mark = "YES" if holds else "no"
    print(f"  2^{j:<2}={s:<6} {rstar:>16} {2*rstar:>5} {phi:>11} {cond_log2:>17.1f} {mark:>5}", flush=True)
    if holds: worst_s=s
print(f"\n  Largest subgroup s* that stays char-p-CLEAN (norm bound holds): {worst_s}", flush=True)
print("  (if some active subgroup near s*=2 log2 n has norm bound HOLDING, prize closes clean via Lam-Leung;", flush=True)
print("   if the active s* has norm bound FAILING, that subgroup needs the BGK/Paley wall.)", flush=True)
