#!/usr/bin/env python3
"""
probe_407_spectral_participation_thinness.py  (#444 -- COLLECTIVE object, uncontested lane)

THE ONE COLLECTIVE OBJECT THE BOARD CONVERGED ON BUT NEVER GATED FOR THINNESS.

Board state (overwhelming): every PER-frequency / PER-line / PER-parity / PER-direction object is
THICKNESS-INVARIANT and Johnson-tracking. The open prize content is asserted to live ONLY in the
COLLECTIVE BGK aggregate cancellation among ALL frequencies simultaneously (L7 WorstCaseIncidence
Bounded). CrossParityAggregate.lean proves the cross-parity FIRST MOMENT = -2|G|^2 (suppressive) and
notes the POSITIVE cross-parity spreads over Theta(q) frequencies -- but NEVER asked the rule-3
question: is that COLLECTIVE SPREAD thinness-essential?

A genuine BGK sqrt-cancellation mechanism requires the spectral L^2 mass a_b := |eta_b|^2 to be
DELOCALIZED -- spread across ~q frequencies so no single b carries a sqrt-violating spike. The
COLLECTIVE measure of this is the spectral PARTICIPATION RATIO (inverse participation number):

    PR(set) := (sum_{b!=0} a_b)^2 / sum_{b!=0} a_b^2 ,   a_b = |eta_b|^2.

PR counts the "effective number of frequencies carrying the L^2 mass". PR small => mass localized
(few hot frequencies => big sup => CORE-bad). PR ~ q => mass maximally spread (BGK-good).

By Parseval: sum_{b!=0} a_b = q*n - n^2 (DC-subtracted energy, EXACT, in-tree SubgroupGaussSumMoment).
And sum_b a_b^2 = q*E_2(G) (the 4th-moment / additive-energy backbone, in-tree). So
    PR = (q*n - n^2)^2 / (q*E_2 - n^4)
is an EXACT closed form in n, q, E_2(G). This is COLLECTIVE (all frequencies), NOT a per-frequency or
per-line object -- DISTINCT from the two live workers (per-coset descent; #bad census).

RULE-3 GATE (the decisive test): compare PR for
  - THIN mu_n (2-power subgroup)
  - NEG-CLOSED RANDOM of same size n (isolates 2-power structure from mere negation-closure)
  - THICK control: a composite (non-2-power) multiplicative subgroup of comparable size
A thin-ESSENTIAL spread => PR_thin > PR_negrand robustly AND a thin/thick SEPARATION (PR_thin tracks
prize regime, NOT thickness). A thickness-INVARIANT PR (thin == thick at matched n) => the collective
spread is ALSO walled, and the board converges completely.

E_2(G) = #{(x,y,z,w) in G^4 : x+y = z+w} = additive energy (EXACT integer count). For mu_n we compute
it EXACTLY by counting additive quadruples mod p. PROPER mu_n (m=(p-1)/n>1, NEVER n=q-1), prize p~n^beta.
"""
import sys, math, argparse, random

def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    if x % 3 == 0: return x == 3
    d = 5
    while d*d <= x:
        if x % d == 0 or x % (d+2) == 0: return False
        d += 6
    return True

def next_prime_cong1(n, lo, skip=0):
    p = lo + (1 - lo % n) % n
    if p < lo: p += n
    while True:
        if is_prime(p):
            if skip == 0: return p
            skip -= 1
        p += n

def primitive_root(p):
    # factor p-1
    n = p - 1
    fac = set(); m = n; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.add(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.add(m)
    for g in range(2, p):
        if all(pow(g, n//q, p) != 1 for q in fac):
            return g
    raise ValueError

def subgroup_order_d(p, d):
    """multiplicative subgroup of order d (d | p-1). returns sorted list of residues."""
    assert (p-1) % d == 0
    g = primitive_root(p)
    h = pow(g, (p-1)//d, p)
    S = set()
    x = 1
    for _ in range(d):
        S.add(x); x = (x*h) % p
    assert len(S) == d
    return sorted(S)

def additive_energy(S, p):
    """EXACT E_2 = #{(x,y,z,w) in S^4 : x+y == z+w mod p} = sum_t r(t)^2, r(t)=#{(x,y): x+y=t}."""
    from collections import Counter
    c = Counter()
    for x in S:
        for y in S:
            c[(x+y) % p] += 1
    return sum(v*v for v in c.values())

def participation_ratio_exact(S, p):
    """PR = (sum_{b!=0} a_b)^2 / sum_{b!=0} a_b^2 via Parseval closed form.
       sum_{b in F} a_b = q*|S|  (a_0 = |S|^2);  sum_{b!=0} a_b = q*|S| - |S|^2.
       sum_{b in F} a_b^2 = q*E_2(S)  (a_0^2 = |S|^4);  sum_{b!=0} a_b^2 = q*E_2 - |S|^4.
       (Both identities are the in-tree SubgroupGaussSumMoment / Parseval backbone, EXACT integers.)"""
    q = p
    nn = len(S)
    E2 = additive_energy(S, p)
    num = (q*nn - nn*nn)
    den = (q*E2 - nn**4)
    PR = (num*num) / den
    return PR, E2, num, den

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--betas", default="4.0,5.0")
    ap.add_argument("--ns", default="8,16,32,64")
    ap.add_argument("--draws", type=int, default=6)
    ap.add_argument("--primes", type=int, default=2)
    args = ap.parse_args()
    ns = [int(x) for x in args.ns.split(",")]
    betas = [float(x) for x in args.betas.split(",")]
    random.seed(12345)

    for beta in betas:
        print(f"\n############ beta={beta} : COLLECTIVE spectral participation thinness gate ############", flush=True)
        print(f"{'n':>4} {'p':>10} {'m':>6} {'PR_thin/q':>10} {'PR_neg/q':>10} {'PR_thick/q':>11} {'thin/neg':>9}", flush=True)
        for n in ns:
            lo = max(int(n**beta), n*2+1)
            for off in range(args.primes):
                p = next_prime_cong1(n, lo, skip=off)
                m = (p-1)//n
                if m <= 1:
                    continue
                mu = subgroup_order_d(p, n)
                PRthin, E2t, _, _ = participation_ratio_exact(mu, p)

                # neg-closed random control: n/2 antipodal pairs {t, p-t}, same size, neg-closed
                negs = []
                for _ in range(args.draws):
                    half = random.sample(range(1, p), n//2)
                    R = set()
                    for t in half:
                        R.add(t); R.add((p-t) % p)
                    R = sorted(R)
                    if len(R) != n:
                        continue
                    PRr, _, _, _ = participation_ratio_exact(R, p)
                    negs.append(PRr)
                PRneg = sum(negs)/len(negs) if negs else float('nan')

                # THICK control: composite multiplicative subgroup of order ~n that is NOT a 2-power
                # subgroup. Find a divisor d of (p-1) with d close to n but with an odd prime factor,
                # so it is a genuinely thick/composite subgroup (rule-3 thickness control).
                PRthick = float('nan'); dth = None
                # candidate composite orders near n (prefer 3*2^k, 6*2^k etc -> non-pure-2-power)
                cand = []
                for d in range(max(3, n-4), n+9):
                    if (p-1) % d == 0:
                        # non-pure-2-power if d has an odd factor >1
                        dd = d
                        while dd % 2 == 0: dd //= 2
                        if dd > 1:
                            cand.append(d)
                if cand:
                    dth = min(cand, key=lambda d: abs(d-n))
                    Sth = subgroup_order_d(p, dth)
                    PRt, _, _, _ = participation_ratio_exact(Sth, p)
                    PRthick = PRt

                tn = (PRthin/PRneg) if PRneg==PRneg and PRneg>0 else float('nan')
                tag = f"(thick d={dth})" if dth else "(no thick subgrp)"
                print(f"{n:>4} {p:>10} {m:>6} {PRthin/p:>10.4f} {PRneg/p:>10.4f} {PRthick/p:>11.4f} {tn:>9.4f}  {tag}", flush=True)

if __name__ == "__main__":
    main()
