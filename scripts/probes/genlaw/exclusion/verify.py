#!/usr/bin/env python3
"""Independent checker for the odd-r tail exclusion theorem.

Implements the ground-truth feasibility rule from scratch (no code shared with
audit_sweep64.c / death.c beyond the published spec), and per-config checks:

  T1 (purity):    O parity-mixed  <=>  odd-balance fails          [exact equivalence]
  T2 (identity):  D(X) = X^rho * (g^2 + q)/2 - X^{A/2} in Z[X]/(X^A+1),
                  coefficient-by-coefficient vs brute d_c          [pure configs]
  T3 (moment):    on every BRUTE-FEASIBLE config:  r^2 <= sum_c P_c^2 <= 5r + 4h + 16
                  (the two ends of the theorem's inequality chain) [feasible configs]
  T4 (criterion): criterion kill => brute infeasible, per-config
                  kill := mixed  OR  r > s/2  OR  r(r-3) > 2s+18
  N_r:            waysum of brute feasibility vs known data

usage: verify.py s r [pure]
"""
import sys
from itertools import combinations
from math import comb

def run(S, R, pureonly=False):
    N, A = 2 * S, S // 2
    B = (S + 1 - R) // 2
    stats = dict(configs=0, mixed=0, mixed_oddpass=0, pure=0, pure_oddfail=0,
                 id_fail=0, t3_fail=0, t4_fail=0, feas=0, ways=0)
    if pureonly:
        osets = [c for par in (0, 1) for c in combinations(range(par, S, 2), R)]
    else:
        osets = combinations(range(S), R)
    for O in osets:
        Oset = set(O)
        pars = {o & 1 for o in O}
        mixed = len(pars) == 2
        for m in range(1 << (R - 1)):
            stats['configs'] += 1
            a = [O[0]] + [O[i] + S * ((m >> (i - 1)) & 1) for i in range(1, R)]
            cnt = [0] * N
            for i in range(R):
                for j in range(i + 1, R):
                    cnt[(a[i] + a[j]) % N] += 1
            for o in O:
                cnt[(2 * o) % N] += 1
            cnt[(3 * S // 2) % N] += 1
            oddok = all(cnt[t] == cnt[t + S] for t in range(1, S, 2))
            # T1
            if mixed:
                stats['mixed'] += 1
                if oddok:
                    stats['mixed_oddpass'] += 1
                    print("T1 VIOLATION (mixed,oddpass)", S, R, O, m)
            else:
                stats['pure'] += 1
                if not oddok:
                    stats['pure_oddfail'] += 1
                    print("T1 VIOLATION (pure,oddfail)", S, R, O, m)
            if not oddok:
                continue
            # brute even-axis feasibility (from the spec, incl. block rule)
            d = [cnt[2 * c] - cnt[2 * c + S] for c in range(A)]
            feasible = all(abs(x) <= 1 for x in d)
            h = sum(1 for x in d if x != 0)
            v = sum(1 for c in range(A)
                    if d[c] == 0 and c not in Oset and c + A not in Oset)
            if feasible:
                for c in range(A):
                    if d[c] == 1 and (c + A) in Oset: feasible = False
                    if d[c] == -1 and c in Oset: feasible = False
            ways = 0
            if feasible and h <= B and (B - h) % 2 == 0 and (B - h) // 2 <= v:
                ways = comb(v, (B - h) // 2)
            if ways > 0:
                stats['feas'] += 1
                stats['ways'] += ways
            # T2: negacyclic identity (pure configs only; mixed never reach here)
            if not mixed:
                rho = O[0] & 1
                u = [(o - rho) // 2 for o in O]
                mu = [1] + [1 - 2 * ((m >> (i - 1)) & 1) for i in range(1, R)]
                g = [0] * A
                for ui, mi in zip(u, mu):
                    g[ui] += mi
                # negacyclic square
                P = [0] * A
                for x in range(A):
                    if g[x] == 0: continue
                    for y in range(A):
                        if g[y] == 0: continue
                        e, co = x + y, g[x] * g[y]
                        if e >= A: e, co = e - A, -co
                        P[e] += co
                q = [0] * A
                for ui in u:
                    e, co = 2 * ui, 1
                    if e >= A: e, co = e - A, -co
                    q[e] += co
                # shift by X^rho (negacyclic)
                def shift(f, k):
                    out = [0] * A
                    for e in range(A):
                        ee, co = e + k, f[e]
                        if ee >= A: ee, co = ee - A, -co
                        out[ee] += co
                    return out
                Ps, qs = shift(P, rho), shift(q, rho)
                ok = all(Ps[c] == 2 * d[c] + (2 if c == A // 2 else 0) - qs[c]
                         for c in range(A))
                if not ok:
                    stats['id_fail'] += 1
                    print("T2 VIOLATION", S, R, O, m)
                # T3 on brute-feasible configs
                if ways > 0:
                    s2 = sum(c * c for c in P)
                    if not (R * R <= s2 <= 5 * R + 4 * h + 16):
                        stats['t3_fail'] += 1
                        print("T3 VIOLATION", S, R, O, m, "sumP2=", s2, "h=", h)
            # T4
            kill = mixed or R > S // 2 or R * (R - 3) > 2 * S + 18
            if kill and ways > 0:
                stats['t4_fail'] += 1
                print("T4 VIOLATION: criterion kills a feasible config", S, R, O, m)
    print(f"VERIFY s={S} r={R} pure={pureonly}: {stats}")
    return stats

if __name__ == "__main__":
    S, R = int(sys.argv[1]), int(sys.argv[2])
    run(S, R, len(sys.argv) > 3 and sys.argv[3] == "pure")
