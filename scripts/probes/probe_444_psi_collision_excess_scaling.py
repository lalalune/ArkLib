#!/usr/bin/env python3
"""
probe_444_psi_collision_excess_scaling.py  (#444, door-(iv), A50 follow-on)

THE EXPLICITLY-OPEN OBJECT (Sweep_A50_SpectrumGeneratingFunction.lean honest-scope note):
  The char-0 subset-sum spectrum count N_r = #{ distinct sum_{z in S} z : S ⊆ μ_n, |S|=r }
  is now in CLOSED FORM (A50). A50 states the open core is the F_p / char-0 GAP:
    "at the prize-binding depth r = ρn the F_p count is collision-saturated and p-dependent;
     that excess (Ψ_p − Ψ_0 > 0 = the BGK/BCHKS-1.12 defect) is the open core."

  Ψ_0(r) := N_r (char-0 distinct-sum count, the A50 closed form)
  Ψ_p(r) := #{ distinct (sum_{z∈S} z mod p) : S ⊆ μ_n, |S| = r }   (the F_p count)
  DEFECT(r) := Ψ_0(r) − Ψ_p(r)  ≥ 0   (collisions only REDUCE the distinct count mod p)

NEVER directly measured as a SCALING object across n at binding depth. This probe does ONLY that:
  - Is DEFECT(r) at r≈ρn a smooth scaling law, or does it have arithmetic structure (p-dependence,
    thinness-sensitivity) a door-(iv) non-moment method could grip?
  - Crucially: is the RELATIVE defect Ψ_p/Ψ_0 thinness-essential (different at thin β vs thick)?
    If the collision excess is thickness-MONOTONE it is a wrong lever (HARD RULE 3). If it is
    thinness-ESSENTIAL and structured, it is a candidate door-(iv) object.

PROBE-FIRST. Exact arithmetic. PROPER 2-power subgroup μ_n < F_p^*, p ≡ 1 (mod n),
m = (p-1)/n preferentially ODD, large p (β ≈ 4), NEVER n = q-1. No moment, no Lean (yet).

Honest expectation going in: this likely RE-CONFIRMS the collision-saturation wall (the defect
grows so the F_p count plateaus = the BGK defect). If so it is a MAPPED refutation and I log a
constraint note, no redundant kernel. Only formalize if a genuinely exploitable structure survives.
"""
import math, sys
from itertools import combinations

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    if x % 3 == 0: return x == 3
    i = 5
    while i*i <= x:
        if x % i == 0 or x % (i+2) == 0: return False
        i += 6
    return True

def find_prime(n, beta_target=4.0, prefer_odd_m=True):
    """Smallest prime p ≡ 1 (mod n) with p ≈ n^beta and m=(p-1)/n preferably ODD."""
    target = int(n**beta_target)
    # search k where p = k*n + 1 prime, k ≈ target/n = n^(beta-1)
    k0 = max(2, target // n)
    best = None
    for dk in range(0, 20000):
        for k in (k0 + dk, k0 - dk):
            if k < 2: continue
            p = k*n + 1
            if p <= n: continue
            if isprime(p):
                m = (p-1)//n
                if prefer_odd_m and m % 2 == 0:
                    continue
                return p, m
    # fallback allow even m
    for dk in range(0, 40000):
        for k in (k0 + dk, k0 - dk):
            if k < 2: continue
            p = k*n + 1
            if isprime(p):
                return p, (p-1)//n
    return None, None

def subgroup(n, p):
    """μ_n = the unique order-n subgroup of F_p^*. g = primitive root^((p-1)/n)."""
    # find a generator of F_p^*
    def is_primroot(g):
        # order check via factoring p-1 is expensive; use multiplicative order test on prime factors
        order = p-1
        fs = set()
        x = order
        d = 2
        while d*d <= x:
            while x % d == 0:
                fs.add(d); x//=d
            d += 1
        if x > 1: fs.add(x)
        for q in fs:
            if pow(g, order//q, p) == 1:
                return False
        return True
    g = 2
    while not is_primroot(g):
        g += 1
    h = pow(g, (p-1)//n, p)   # order n
    S = []
    cur = 1
    for _ in range(n):
        S.append(cur); cur = (cur*h) % p
    assert len(set(S)) == n, "subgroup size mismatch"
    return S

def Nr_charzero_closedform(n, r):
    """A50 closed form: N_r = sum_{k ≡ r (2), k ≤ min(r, 2m-r)} C(m,k) 2^k, m=n/2."""
    m = n//2
    tot = 0
    kmax = min(r, 2*m - r)
    k = r % 2  # k ≡ r (mod 2), smallest
    # actually k ranges over same parity as r, from (r-? ) -- net-vector: depth r=k+2i, 0<=i<=m-k
    # so k ≡ r (mod 2), k from max(0, ?) up to min(r, 2m-r). k>=0 and k same parity as r.
    k = r % 2
    while k <= kmax:
        if k <= m:
            tot += math.comb(m, k) * (2**k)
        k += 2
    return tot

def Psi_p_distinct(S, p, r, cap=200000):
    """#{ distinct (sum of r-subset of S) mod p }. Exact for small C(n,r); else None (too big)."""
    n = len(S)
    nck = math.comb(n, r)
    if nck > cap:
        return None, nck
    seen = set()
    for comb in combinations(S, r):
        seen.add(sum(comb) % p)
    return len(seen), nck

def main():
    print("# probe_444_psi_collision_excess_scaling — Psi_p vs Psi_0 (char-0) at binding depth")
    print("# DEFECT = N_r(char0) - #distinct(F_p);  rho = r/n binding fraction\n")
    rhos = [0.25, 0.375, 0.5]   # binding band around r ≈ rho*n
    print(f"{'n':>4} {'p':>11} {'m':>6} {'r':>4} {'rho':>5} {'Psi0=N_r':>12} {'Psi_p':>10} {'defect':>10} {'Psi_p/Psi0':>11} {'C(n,r)':>12}")
    results = []
    for n in [16, 32, 64]:
        p, m = find_prime(n, beta_target=4.0)
        if p is None:
            print(f"{n:>4}  no prime found"); continue
        S = subgroup(n, p)
        for rho in rhos:
            r = max(1, round(rho*n))
            psi0 = Nr_charzero_closedform(n, r)
            psip, nck = Psi_p_distinct(S, p, r)
            if psip is None:
                print(f"{n:>4} {p:>11} {m:>6} {r:>4} {rho:>5.3f} {psi0:>12} {'TOOBIG':>10} {'-':>10} {'-':>11} {nck:>12}")
                continue
            defect = psi0 - psip
            ratio = psip/psi0 if psi0 else float('nan')
            print(f"{n:>4} {p:>11} {m:>6} {r:>4} {rho:>5.3f} {psi0:>12} {psip:>10} {defect:>10} {ratio:>11.4f} {nck:>12}")
            results.append((n, p, r, rho, psi0, psip, defect, ratio))
    # thinness control: same n, vary beta (thin vs thicker prime), watch ratio
    print("\n# THINNESS CONTROL: fix n=16, r=4 (rho=0.25), vary prime size (beta) -> is defect thickness-monotone?")
    n = 16; r = 4
    psi0 = Nr_charzero_closedform(n, r)
    print(f"# char-0 Psi0(n=16,r=4) = {psi0}")
    for beta in [3.0, 4.0, 5.0, 6.0]:
        p, m = find_prime(n, beta_target=beta)
        if p is None: continue
        S = subgroup(n, p)
        psip, _ = Psi_p_distinct(S, p, r)
        ratio = psip/psi0 if psi0 else float('nan')
        print(f"#   beta≈{beta}: p={p:>12} m={m:>8} Psi_p={psip:>6} defect={psi0-psip:>6} ratio={ratio:.4f}")
    print("\n# VERDICT printed by caller after reading the table.")

if __name__ == "__main__":
    main()
