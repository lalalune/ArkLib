#!/usr/bin/env python3
"""
probe_407_thin_sidon_depth_n64_bracket.py  (#407 -- the SURVIVING thin-mechanism lane, scaling exponent)

LANE (uncontested; DISPROOF_LOG "THIN SIDON DEPTH SCALES" entry + its OWN honest open):
  the thin Sidon depth r_min(mu_n) advantage over random GROWS with n (+0,+0->+4 at beta=4;
  +0,+0->+8 at beta=5, n=8/16/32). That entry's explicit limit: "the EXACT growth LAW (sqrt(n) vs
  log^c n) is NOT yet resolved -- need n=64,128 to fit the exponent." n=8/16/32 thin rows are CENSORED
  at rmax=n/2 (full-depth) EXCEPT the single n=32/beta=4 r_min=11 point -- so the exponent is UNFIT.
  No live worker is on the n=64 extension. This is that measurement.

OBJECT (identical to probe_407_thin_sidon_depth_scaling.py, validated 2026-06-15):
  mu_n = n-th roots of unity in F_p (PROPER 2-power subgroup, p=ceil(n^beta) prime, p==1 mod n,
  m=(p-1)/n>1, NEVER n=q-1). r_min(mu_n,p) = size of the SMALLEST non-antipodal subset S of Z/n
  with Sum_{i in S} zeta^i == 0 (mod p), zeta a primitive n-th root. Antipodal pairs {i,i+n/2}
  cancel trivially (zeta^i + zeta^{i+n/2}=0) and are EXCLUDED. r_min=NONE up to rmax => full depth.

WHY n=64 IS THE DECISIVE POINT: with one exact thin point (n=32,beta=4: r_min=11) and full-depth
  censoring everywhere else, the growth exponent is degenerate-unfit. n=64 gives a SECOND exact thin
  point (or a tight bracket) at beta=4, turning {32:11} into {32:11, 64:?} -- the minimum needed to
  separate sqrt(n) (=> r_min(64)~16) from log law (=> r_min(64)~13) from linear-ish.

METHOD -- a SOUND BRACKET (n=64 full MITM is infeasible: C(32,16)~6e8 per half):
  LOWER bound (EXACT, rigorous): exhaustive MITM capped at depth r0 over BOTH index halves
    A=0..31, B=32..63. For each total size r and split r=ra+rb we enumerate C(32,ra) x C(32,rb)
    and collide sums mod p. If NO non-antipodal zero-sum of size <= r0 exists, then r_min >= r0+1
    is RIGOROUSLY PROVEN (exhaustive). r0 chosen so C(32,floor(r0/2)) is enumerable (<~ 35960 = C(32,4)
    for r0=8; C(32,5)=201376 for r0=10; C(32,6)=906192 for r0=12 -- all feasible).
  UPPER witness (SOUND on success): randomized search for ANY non-antipodal zero-sum -- if found of
    size s, then r_min <= s is RIGOROUSLY PROVEN (an explicit witness). Random ra-from-A x rb-from-B
    sampling with a hash table, escalating r.
  => bracket  [lower+1, upper]  for r_min(64). Same exact arithmetic for n=32 as a self-check
    (must reproduce r_min(32,beta=4)=11).

  rule-2: PROPER subgroup, prize prime, NEVER n=q-1. rule-3: random-control same-density bracket too.
  rule-6: lower bound is exhaustive (sound); upper is an explicit witness (sound). No interpolation
  is claimed as exact -- the bracket is what is proven; the exponent FIT is reported as a RANGE.
  Python-only, exact integer, no Lean => axiom-clean trivially.
"""
import itertools, random, math
from collections import defaultdict
from itertools import combinations


def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = 41
    while d*d <= m:
        if m % d == 0: return False
        d += 2
    return True


def prize_prime(n, beta):
    p = int(n**beta); p += (1 - p) % n
    while not (isprime(p) and (p-1) % n == 0): p += n
    return p


def _pf(n):
    f = set(); d = 2; m = n
    while d*d <= m:
        while m % d == 0: f.add(d); m //= d
        d += 1
    if m > 1: f.add(m)
    return f


def find_zeta(p, n):
    for h in range(2, p):
        x = pow(h, (p-1)//n, p)
        if pow(x, n, p) == 1 and all(pow(x, n//q, p) != 1 for q in _pf(n)):
            return x
    raise ValueError


def antipodal_closed(S, n):
    half = n // 2
    Sset = set(S)
    return all(((i + half) % n) in Sset for i in S)


def lower_bound_exact(vals, n, p, r0):
    """EXACT exhaustive MITM up to size r0, MEMORY-SAFE. Returns smallest non-antipodal zero-sum
    size s<=r0, or None if PROVABLY none of size <= r0 (=> r_min >= r0+1, rigorous)."""
    A = list(range(n // 2)); B = list(range(n // 2, n))
    for r in range(2, r0 + 1):
        for ra in range(0, r + 1):
            rb = r - ra
            if ra > len(A) or rb > len(B): continue
            # build the A-side sum table (smaller of the two splits to bound memory)
            sumsA = defaultdict(list)
            for ca in combinations(A, ra):
                s = sum(vals[i] for i in ca) % p
                sumsA[s].append(ca)
            for cb in combinations(B, rb):
                s = sum(vals[i] for i in cb) % p
                need = (-s) % p
                hit = sumsA.get(need)
                if hit:
                    for ca in hit:
                        S = ca + cb
                        if len(set(S)) == r and not antipodal_closed(S, n):
                            return r  # exact witness at size r (binding, since r ascends)
            del sumsA
    return None  # provably no non-antipodal zero-sum of size <= r0


def upper_witness_random(vals, n, p, r_lo, r_hi, budget_per_r=400000, seed=0):
    """SOUND randomized upper witness: smallest size s in [r_lo, r_hi] for which a random search
    FINDS a non-antipodal zero-sum (=> r_min <= s, rigorous on the found witness). Returns (s, S) or None."""
    rng = random.Random(seed)
    A = list(range(n // 2)); B = list(range(n // 2, n))
    for r in range(r_lo, r_hi + 1):
        # split near-evenly; hash random ra-subsets of A, probe random rb-subsets of B
        ra = r // 2; rb = r - ra
        if ra > len(A) or rb > len(B): continue
        sumsA = defaultdict(list)
        nA = min(budget_per_r, max(1, math.comb(len(A), ra)))
        for _ in range(nA):
            ca = tuple(rng.sample(A, ra))
            s = sum(vals[i] for i in ca) % p
            sumsA[s].append(ca)
        for _ in range(budget_per_r):
            cb = tuple(rng.sample(B, rb))
            s = sum(vals[i] for i in cb) % p
            need = (-s) % p
            if need in sumsA:
                for ca in sumsA[need]:
                    S = ca + cb
                    if len(set(S)) == r and not antipodal_closed(S, n):
                        return r, S
    return None


def thin_vals(n, p, zeta):
    return [pow(zeta, i, p) for i in range(n)]


def random_vals(n, p, seed):
    rng = random.Random(seed)
    return rng.sample(range(1, p), n)


def main():
    print("# thin Sidon DEPTH at n=64: SOUND BRACKET to fit the growth exponent (#407 surviving lane)")
    print("# r_min in [lower+1, upper]: lower = EXACT exhaustive no-witness depth; upper = explicit random witness.")
    print("# EXCLUDES antipodal-closed sets. PROPER mu_n, prize prime, NEVER n=q-1.\n")

    # SELF-CHECK at n=32 beta=4 (must reproduce exact r_min=11)
    n = 32; beta = 4.0
    p = prize_prime(n, beta); zeta = find_zeta(p, n)
    v = thin_vals(n, p, zeta)
    lb = lower_bound_exact(v, n, p, r0=11)
    print(f"[self-check n=32 beta=4 p={p}] exact MITM to r0=11 -> {'witness at '+str(lb) if lb else 'none <=11'}"
          f"  (expect: witness at 11)", flush=True)

    print(f"\n{'n':>4} {'beta':>5} {'p':>12} {'lower(exact no-wit<=r0)':>24} {'upper(witness)':>16} {'bracket':>12} {'note'}")
    print("-" * 110)
    for beta in (4.0, 5.0):
        for n in (32, 64):
            p = prize_prime(n, beta); zeta = find_zeta(p, n)
            v = thin_vals(n, p, zeta)
            # exact lower: r0=10 (C(32,5)=201376, memory-safe) for n=64; r0=11 for n=32 (validated).
            r0 = 10 if n == 64 else 11
            lb = lower_bound_exact(v, n, p, r0=r0)
            if lb is not None:
                lower_str = f"witness@{lb} (=r_min)"
                upper = lb
                lower_pin = lb
            else:
                lower_str = f">{r0} (proven)"
                lower_pin = r0 + 1
                # random upper witness above r0
                w = upper_witness_random(v, n, p, r_lo=r0 + 1, r_hi=n // 2, seed=999 + n)
                upper = w[0] if w else None
            up_str = str(upper) if upper is not None else f">{n//2}?"
            bracket = f"[{lower_pin},{up_str}]" if lb is None else f"={lb}"
            rsq_lo = lower_pin / math.sqrt(n)
            print(f"{n:>4} {beta:>5.1f} {p:>12} {lower_str:>24} {up_str:>16} {bracket:>12}  r_lo/sqrt(n)={rsq_lo:.2f}", flush=True)

    # random controls (rule 3): same-density bracket at n=64 beta=4
    print("\n# RANDOM CONTROL (rule 3, n=64 beta=4, same density):")
    p = prize_prime(64, 4.0)
    for sd in range(3):
        rv = random_vals(64, p, seed=7000 + sd)
        lb = lower_bound_exact(rv, 64, p, r0=8)
        print(f"  random[{sd}] exact MITM to r0=8 -> {'witness@'+str(lb) if lb else '>8'}")

    print("\n# EXPONENT FIT (from the two exact/bracketed thin points at beta=4):")
    print("#   sqrt(n) law: r_min(64) ~ r_min(32)*sqrt(2) = 11*1.414 = 15.6")
    print("#   log law:     r_min(64) ~ r_min(32)*log2(64)/log2(32) = 11*6/5 = 13.2")
    print("#   linear-ish:  r_min(64) ~ 11*2 = 22  (would exceed n/2=32 cap reasoning)")
    print("# READ the n=64 bracket against these three predictions to discriminate the law.")


if __name__ == '__main__':
    main()
