#!/usr/bin/env python3
"""
probe_c2_conductor_nscaling.py  (#389 C2 — clean n-scaling of the parameter-family c_eff)

Faster than the full b-sweep: sample b over a large random subset to estimate M and Var,
PLUS exact small cases. Goal: more (n) data points for c_eff = M/sqrt(n) to distinguish
  - c_eff ~ const         (O(1) conductor sheaf -> handle, prize via Deligne)
  - c_eff ~ sqrt(log p)   (log-conductor -> handle up to sqrt-log, EXACTLY the prize target)
  - c_eff ~ n^a (a>0)     (n-dependent conductor -> WALL, relocation failed)
Proper mu_n: n=2^mu, p PRIME, n|p-1, p~n^4 (>>n^3), p-1 != n.

Also the THEORETICAL crux: Var = n EXACTLY (Parseval). For a geom-irreducible
middle-extension sheaf F on A^1 with trace function t(b)=eta_b, the q->inf average
avg_b |t(b)|^2 = (# of geom-irred components counted w/ mult in End) = generically the
RANK of F. So rank(F) = n. Deligne/Weil-II: |t(b)| <= (rank + Swan) * sqrt(q_geom).
Here the "geometric q" per point: eta_b is itself a complete sum over the n-pt fiber, NOT
over F_p, so there is no extra sqrt(p) to spend -- the sheaf trace IS eta_b. The bound
|t(b)| <= cond(F) is the LefSchetz/Betti bound = sum of dims of H^*_c = O(rank) = O(n) = TRIVIAL.
The sqrt-cancellation sqrt(rank) ~ sqrt(n) requires the n rank-1 pieces to be in GENERAL
POSITION (random phases), which is the equidistribution/RH-on-average -- NOT a pointwise
Deligne output. This probe shows c_eff sits at sqrt(rank)-scale (handle-ish) but tests if
it is PROVABLY so (uniform) or just generically so.
"""
import math, random

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a % m == 0: continue
        x = pow(a,d,m); ok = (x==1)
        for _ in range(s):
            if x == m-1: ok=True; break
            x = x*x % m
        if not ok: return False
    return True

def find_prime(n, beta):
    target = int(round(n**beta))
    base = target - (target % n) + 1
    for d in range(0, 2000*n, n):
        p = base + d
        if p > 100*n**3 and is_prime(p) and (p-1) != n:
            return p
    return None

def subgroup(p, n):
    for g0 in range(2, 2000):
        g = pow(g0, (p-1)//n, p)
        H = set(); x = 1
        for _ in range(n):
            H.add(x); x = x*g % p
        if len(H) == n:
            return sorted(H)
    raise RuntimeError("no subgroup")

def sup_var_sampled(p, n, H, nsamp):
    tp = 2*math.pi/p
    M = 0.0; S2 = 0.0; cnt = 0
    # if p-1 small, do exact; else sample
    if p-1 <= nsamp:
        bs = range(1, p)
    else:
        bs = random.sample(range(1, p), nsamp)
    for b in bs:
        c = 0.0; s = 0.0
        for x in H:
            ang = tp*((b*x) % p)
            c += math.cos(ang); s += math.sin(ang)
        mag2 = c*c + s*s
        if mag2 > M: M = mag2
        S2 += mag2; cnt += 1
    return math.sqrt(M), S2/cnt

random.seed(12345)
print("C2 c_eff n-scaling (sampled M is a LOWER bound on the true sup; the true sup is >=).")
print("Compare growth of M/sqrt(n) to sqrt(log p) (prize-target slack).")
print()
print(f"{'n':>4} {'p':>11} {'beta':>5} {'Var~':>7} {'M(samp)':>8} {'M/sqrtVar':>10} {'M/sqrt(n)':>10} {'sqrt(log p)':>11} {'M/sqrt(n log(p/n))':>18}")
for mu in [3,4,5,6,7]:
    n = 2**mu
    p = find_prime(n, 4.0)
    if p is None: 
        print(f"{n:>4} (no prime)"); continue
    H = subgroup(p, n)
    nsamp = min(p-1, 300000)
    M, Var = sup_var_sampled(p, n, H, nsamp)
    bp = math.log(p)/math.log(n)
    print(f"{n:>4} {p:>11} {bp:>5.2f} {Var:>7.2f} {M:>8.3f} {M/math.sqrt(Var):>10.4f} "
          f"{M/math.sqrt(n):>10.4f} {math.sqrt(math.log(p)):>11.4f} {M/math.sqrt(n*math.log(p/n)):>18.4f}", flush=True)
print()
print("Note: sampled M underestimates true sup (esp at large m), so M/sqrt(n) is a LOWER bound;")
print("trend of the lower bound still informs growth class. Exact sup at n<=16 in the sister probe.")
