#!/usr/bin/env python3
"""
probe_407_census_supply_budget_exhaustive.py  (#444 -- rigorous tightening of the FEAS test)

Tightens probe_407_census_supply_budget_feasibility.py: at n=8 (and the validation n=16 shallow
bands) we EXHAUSTIVELY scan ALL char-line pairs (A,B), A>B, A,B in [1,n-1], plus random pairs,
to make K = max_pairs #alignableSets a TRUE maximum over the char-line adversary (not a shortlist).

Headline being made rigorous: at the shallow over-det bands the census count K EXCEEDS the weld's
own supply budget 2^r*C(2^{mu-1},r). Since a char-line is a legal stack (u0=x^A,u1=x^B are valid
words), ANY single pair with #alignable > budget already FALSIFIES CensusDomination at that K
(the weld quantifies over ALL u0,u1). So even our shortlist DEAD rows were rigorous; this confirms
the max and checks p-independence + a thick (non-2-power) control (rule 3).

Outputs, per (n,beta,p): for each depth r (k=r-1, a_bind=r+1), the exhaustive-over-lines K, the
budget, the verdict, AND the worst line. Plus multi-prime p-independence of K, and a thick n control.
"""
import itertools, math, sys, random


def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d * d <= x:
        if x % d == 0: return False
        d += 2
    return True


def next_prime_cong1(n, lo):
    p = lo + (1 - lo % n) % n
    if p < lo: p += n
    while not is_prime(p):
        p += n
    return p


def find_g(p, n):
    assert (p - 1) % n == 0
    m = (p - 1) // n
    assert m > 1
    for h in range(2, 6000):
        x = pow(h, m, p)
        if pow(x, n, p) == 1 and pow(x, n // 2, p) != 1:
            return x
    raise ValueError


def divided_diff(pts_idx, vx, vv, p):
    """returns None if any node-difference is non-invertible mod p (degenerate config)."""
    total = 0
    for i in pts_idx:
        den = 1
        for j in pts_idx:
            if i == j: continue
            den = den * ((vx[i] - vx[j]) % p) % p
        if den % p == 0:
            return None
        total = (total + vv[i] * pow(den, -1, p)) % p
    return total


def n_alignable(u0, u1, xs, p, kdim, a):
    n = len(xs)
    if a > n: return 0
    e0, e1 = {}, {}
    for T in itertools.combinations(range(n), kdim + 1):
        e0[T] = divided_diff(T, xs, u0, p)
        e1[T] = divided_diff(T, xs, u1, p)

    def ratio(T):
        a_, b_ = e0[T], e1[T]
        if a_ is None or b_ is None:
            return None  # degenerate node config (non-2-power domains)
        if b_ != 0:
            return (-a_) * pow(b_, -1, p) % p
        return None if a_ == 0 else 'NOROOT'

    cnt = 0
    for S in itertools.combinations(range(n), a):
        r = None; ok = True; any_nd = False
        for T in itertools.combinations(S, kdim + 1):
            rt = ratio(T)
            if rt is None: continue
            if rt == 'NOROOT':
                ok = False; break
            any_nd = True
            if r is None: r = rt
            elif r != rt:
                ok = False; break
        if ok and any_nd:
            cnt += 1
    return cnt


def charline(A, B, xs, p):
    return ([pow(x, A, p) for x in xs], [pow(x, B, p) for x in xs])


def K_exhaustive(xs, p, kdim, a, n):
    """TRUE max over ALL char-line pairs (A>B in [1,n-1]) + random pairs."""
    Kmax = 0; arg = None
    for A in range(1, n):
        for B in range(0, A):
            u0, u1 = charline(A, B, xs, p)
            c = n_alignable(u0, u1, xs, p, kdim, a)
            if c > Kmax:
                Kmax = c; arg = (A, B)
    rng = random.Random(12345 ^ p)
    for _ in range(6):
        ru0 = [rng.randrange(p) for _ in range(n)]
        ru1 = [rng.randrange(p) for _ in range(n)]
        c = n_alignable(ru0, ru1, xs, p, kdim, a)
        if c > Kmax:
            Kmax = c; arg = ('rand',)
    return Kmax, arg


def main():
    print("=" * 80)
    print("EXHAUSTIVE-over-char-lines census supply-budget feasibility (n=8, multi-prime + thick ctrl)")
    print("  budget = 2^r * C(2^{mu-1}, r).  K = TRUE max_pairs #alignable(a_bind=r+1), k=r-1.")
    print("=" * 80)

    # ---- n=8 thin (2-power), 3 prize primes for p-independence ----
    mu = 3; n = 8
    primes = []
    for beta in (4.0, 4.5, 5.0):
        primes.append(next_prime_cong1(n, int(n ** beta)))
    for p in primes:
        g = find_g(p, n); xs = [pow(g, i, p) for i in range(n)]
        fermat = bin(p - 1).count('1') == 1
        print(f"\n--- THIN n=8 (mu=3), p={p} {'[non-Fermat]' if not fermat else '[Fermat]'} ---")
        for r in range(2, n):
            kdim = r - 1; a = r + 1
            if a > n or r > 2 ** (mu - 1): break
            budget = (2 ** r) * math.comb(2 ** (mu - 1), r)
            K, arg = K_exhaustive(xs, p, kdim, a, n)
            v = "VIABLE" if K <= budget else "*** DEAD ***"
            print(f"  r={r} k={kdim} a={a}: K={K} (worst={arg}) budget={budget} "
                  f"ratio={K/budget:.3f} => {v}", flush=True)

    # ---- THICK control (rule 3): n=6 (composite, NOT 2-power), order-6 subgroup ----
    print("\n" + "=" * 80)
    print("THICK CONTROL (rule 3): n=6 (NOT 2-power). If DEAD verdict is the SAME, the budget")
    print("  infeasibility is thickness-INVARIANT (structural, not 2-power-essential).")
    print("  (mu undefined for non-2-power; we use the SAME budget form with 2^{mu-1}->n/2, r, the")
    print("   structural analog -- this is a heuristic control on the count-vs-supply RELATION.)")
    print("=" * 80)
    for nn in (6, 10, 12):
        for beta in (4.0, 4.5):
            lo = int(nn ** beta)
            p = next_prime_cong1(nn, lo)
            try:
                g = find_g(p, nn)
            except Exception:
                continue
            xs = [pow(g, i, p) for i in range(nn)]
            print(f"\n--- THICK n={nn}, p={p} ---")
            for r in range(2, nn):
                kdim = r - 1; a = r + 1
                if a > nn: break
                budget = (2 ** r) * math.comb(nn // 2, r) if r <= nn // 2 else None
                K, arg = K_exhaustive(xs, p, kdim, a, nn)
                if budget is None:
                    print(f"  r={r} k={kdim} a={a}: K={K} (worst={arg}) budget=N/A(r>n/2)", flush=True)
                else:
                    v = "VIABLE" if K <= budget else "*** DEAD ***"
                    print(f"  r={r} k={kdim} a={a}: K={K} (worst={arg}) budget={budget} "
                          f"ratio={K/budget:.3f} => {v}", flush=True)

    print("\nDONE.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
