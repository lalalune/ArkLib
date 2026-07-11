#!/usr/bin/env python3
"""
wf-OT4 (#444): prize-scale guard for the char-0 Lam-Leung ceiling DISCHARGE at r in {2,3}.

The discharge Frontier/_wf9OT4_charzero_ceiling_discharge.lean turns the free hypothesis
`hZceiling : E_r <= (2r-1)!!*n^r` of the slack route (_wf6P2) into a PROVEN input at r=2,3,
using the in-tree exact closed forms E_2 = 3n^2-3n, E_3 = 15n^3-45n^2+40n (BalancedCount carrier)
vs the Lam-Leung ceilings 3!!*n^2 = 3n^2, 5!!*n^3 = 15n^3.

This script verifies the ceiling is GENUINE (strict, slack > 0) through the prize scale n = 2^30,
so the discharge is non-vacuous. It is an exact integer check (no sampling, no good-prime artifact;
char-0 closed forms are field-universal).
"""

def check(mu):
    n = 2**mu
    E2 = 3*n**2 - 3*n
    E3 = 15*n**3 - 45*n**2 + 40*n
    c2 = 3*n**2          # 3!! * n^2
    c3 = 15*n**3         # 5!! * n^3
    s2 = c2 - E2         # Slack_2
    s3 = c3 - E3         # Slack_3
    assert s2 == 3*n,              (n, s2, 3*n)
    assert s3 == 45*n**2 - 40*n,   (n, s3)
    assert E2 <= c2 and s2 > 0,    "ceiling r=2 not genuine"
    assert E3 <= c3 and s3 > 0,    "ceiling r=3 not genuine"
    return n, E2, c2, s2, E3, c3, s3

if __name__ == "__main__":
    print("wf-OT4 char-0 ceiling discharge guard: E_r <= (2r-1)!!*n^r, slack > 0 (exact)")
    for mu in [3, 4, 5, 10, 20, 30]:
        n, E2, c2, s2, E3, c3, s3 = check(mu)
        print(f"  n=2^{mu:<2}={n:>11}:  E2={E2}<=c2={c2} (Slack_2={s2}=3n>0);  "
              f"E3<=c3 (Slack_3={s3}=45n^2-40n>0)")
    print("OK: ceiling strict (genuine) through prize scale n=2^30 -> discharge non-vacuous.")
