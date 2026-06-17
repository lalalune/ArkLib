#!/usr/bin/env python3
"""
probe_c2_weil_paramfamily_conductor.py  (#389 / char-p wall, angle C2-weil-deligne-paramfamily)

THE C2 ANGLE.  Plain Weil on the n-DOMAIN sum  eta_b = sum_{x in mu_n} e_p(bx)  is VACUOUS
(only n terms, Weil error sqrt(p) >> n for prize beta in [4,5]).  C2 instead realizes the
PARAMETER family  b |-> eta_b,  b in (Z/p)^* (m = (p-1)/n distinct values up to the mu_n
symmetry eta_b=eta_{xb}, x in mu_n; really m parameter classes, p-1 ~ q points), as the trace
function of an l-adic sheaf F on the b-line A^1.  IF F is geometrically irreducible with
conductor c = cond(F) = O(1) UNIFORMLY in n, Deligne (Weil II) + Fouvry-Kowalski-Michel give

      sup_{b != 0} |eta_b|  <=  c * (L2 scale)   where L2 scale = sqrt(Var_b eta_b) = sqrt(n).

So the C2 prediction is  M(n) = sup |eta_b| <= c_eff * sqrt(n),  c_eff := sup/sqrt(Var)
BOUNDED in n  =>  prize (up to the bounded c, possibly c ~ sqrt(log) if conductor grows logly).

DECISIVE TEST.  Prize regime: n = 2^mu, p PRIME, n | p-1, p ~ n^beta (beta=4), p >> n^3,
NEVER p-1 = n.  Compute over the FULL parameter family b=1..p-1:
   Var = avg_{b!=0} |eta_b|^2      (the sheaf L2 / Parseval scale; should -> n)
   M   = max_{b!=0} |eta_b|        (the prize sup)
   c_eff = M / sqrt(Var)           (the EFFECTIVE conductor: bounded => sheaf has O(1) cond)
   c_eff' = M / sqrt(n)            (vs the clean Parseval scale)
   M / sqrt(n log(p/n))           (the prize Ramanujan-up-to-sqrt-log target ratio; bounded?)
Grow n; if c_eff is FLAT (or grows only like sqrt(log p)) => the parameter-family sheaf has
bounded (or log) conductor => C2 is a REAL handle.  If c_eff grows like n^c (c>0) => the sheaf
conductor is n-dependent (relocation failed, the family inherits the n-domain pathology) => WALL.

We ALSO probe the SHEAF RANK directly via the variance EXACTNESS: for a geometrically
irreducible middle-extension sheaf of rank rho, Var_b eta_b = rho + o(1) in the q->inf limit
(diagonal / orthogonality).  Var=n exactly (Parseval, proven) => rank rho = n => CONDUCTOR
>= rank = n => c_eff in Deligne is AT LEAST n^{1/2}... THIS IS THE CRUX we test:
   does a rank-n sheaf give a USEFUL bound?  Deligne: |trace| <= (cond) sqrt(q_fiber).
The fiber here is the n-element subgroup, "q_fiber" ~ 1 per point, so naive Deligne on the
b-family gives sup <= cond * sqrt(n) only if the L2 (=n=rank) is the right normalization,
i.e. c_eff = sup/sqrt(rank) = sup/sqrt(n).  So the real question: is sup/sqrt(n) bounded?
"""
import math

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
    """smallest prime p ~ n^beta with n|p-1, p>>n^3, p-1 != n."""
    target = int(round(n**beta))
    base = target - (target % n) + 1
    for d in range(0, 400*n, n):
        p = base + d
        if p > 100*n**3 and is_prime(p) and (p-1) != n:
            return p
    # fall back: any prime > 100 n^3
    base = (100*n**3 // n)*n + 1
    d = 0
    while True:
        p = base + d
        if is_prime(p) and (p-1) != n: return p
        d += n

def subgroup(p, n):
    for g0 in range(2, 1000):
        g = pow(g0, (p-1)//n, p)
        H = set(); x = 1
        for _ in range(n):
            H.add(x); x = x*g % p
        if len(H) == n:
            return sorted(H)
    raise RuntimeError("no subgroup")

def periods_supvar(p, n, H):
    """compute M=max|eta_b|, Var=avg|eta_b|^2 over b=1..p-1, exact-ish via cos/sin."""
    tp = 2*math.pi/p
    M = 0.0; S2 = 0.0
    # eta_b = sum_{x in H} e_p(b x); |eta_b|^2 = (sum cos)^2 + (sum sin)^2
    for b in range(1, p):
        c = 0.0; s = 0.0
        for x in H:
            ang = tp*((b*x) % p)
            c += math.cos(ang); s += math.sin(ang)
        mag2 = c*c + s*s
        if mag2 > M: M = mag2
        S2 += mag2
    M = math.sqrt(M)
    Var = S2/(p-1)
    return M, Var

print("C2 parameter-family sheaf conductor test (prize regime, proper mu_n).")
print("Var->n is Parseval (sheaf L2 = rank). c_eff = M/sqrt(Var): BOUNDED => O(1)-conductor sheaf.")
print()
hdr = (f"{'n':>4} {'p':>10} {'beta':>5} {'m':>7} {'Var':>8} {'M':>8} "
       f"{'c_eff=M/sqrtVar':>15} {'M/sqrt(n)':>10} {'M/sqrt(n*log(p/n))':>18}")
print(hdr)
for mu in [3, 4, 5, 6]:
    n = 2**mu
    beta = 4.0
    p = find_prime(n, beta)
    if p > 6_000_000:  # feasibility cap on the full b-sweep
        print(f"{n:>4} {p:>10} (skipped: p too large for full b-sweep)")
        continue
    H = subgroup(p, n)
    M, Var = periods_supvar(p, n, H)
    m = (p-1)//n
    beta_eff = math.log(p)/math.log(n)
    c_eff = M/math.sqrt(Var)
    Mr = M/math.sqrt(n)
    target = M/math.sqrt(n*math.log(p/n))
    print(f"{n:>4} {p:>10} {beta_eff:>5.2f} {m:>7} {Var:>8.3f} {M:>8.3f} "
          f"{c_eff:>15.4f} {Mr:>10.4f} {target:>18.4f}", flush=True)

print()
print("READING:")
print("  Var = n exactly (Parseval) => the b-family sheaf has RANK n (diagonal/orthogonality).")
print("  A rank-n sheaf has conductor >= n; Deligne |trace| <= cond * sqrt(fiber) does NOT")
print("  automatically give sup <= O(1)*sqrt(n) -- the conductor itself carries the n.")
print("  THE TEST: is c_eff = M/sqrt(Var) bounded (handle) or growing (wall)?")
print("  If M/sqrt(n) ~ const and M/sqrt(n log(p/n)) ~ const-or-decreasing => Ramanujan-up-to-sqrt-log holds")
print("  empirically; the OPEN part is whether a sheaf realization PROVES it (vs the diagonal being")
print("  uniform). Distinguish: does the sheaf give a bound INDEPENDENT of the diagonal/Parseval input?")
