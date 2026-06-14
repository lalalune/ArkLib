#!/usr/bin/env python3
"""Probe: dimension-2 (k=2, r=3) InteriorCeiling triple-ownership bound (#357).

Validates, for the affine evaluation code C = {i -> c0 + c1*g^i} on the smooth
8-point domain <g> in F_p (p = 1 mod 8):

  C1: criterion equivalence -- gamma is mcaEvent-bad at agreement threshold a=4
      iff some affine interpolant's FULL agreement set T (|T| >= 4) of
      w = u0 + gamma*u1 is not jointly explained (u0,u1 simultaneously affine on T).
      Cross-checked against faithful subset enumeration (any S subset of an
      agreement set, |S| >= 4, unexplained).
  C2: triple ownership -- (a) every bad gamma's witness has >= 3 unexplained
      triples; (b) an unexplained triple is affine-collinear for at most one gamma.
  C3: #bad <= floor(C(8,3)/3) = 18 for every stack (hill-climb + structured),
      and < 32 = 2^3*C(4,3) (the KKH26 ceiling count at mu=3).

The Lean theorem (KKH26DimTwoPin.lean) is kernel-checked directly from mcaEvent,
so this probe is a semantic cross-check (non-vacuity + faithfulness), not the proof.
"""
import itertools, random, sys

def order(g, p):
    x, k = g % p, 1
    while x != 1:
        x = x * g % p
        k += 1
        if k > p: return 0
    return k

def find_g(p, n):
    for g in range(2, p):
        if order(g, p) == n:
            return g
    raise ValueError(f"no element of order {n} mod {p}")

def setup(p, n=8):
    g = find_g(p, n)
    xs = [pow(g, i, p) for i in range(n)]
    assert len(set(xs)) == n
    return g, xs

def interp2(x1, y1, x2, y2, p):
    """affine c0 + c1*x through two points with distinct x."""
    c1 = (y1 - y2) * pow(x1 - x2, -1, p) % p
    c0 = (y1 - c1 * x1) % p
    return c0, c1

def explained(T, u0, u1, xs, p):
    """u0 AND u1 both restrictions of affine functions on index set T."""
    T = sorted(T)
    if len(T) <= 1: return True
    i, j = T[0], T[1]
    for u in (u0, u1):
        c0, c1 = interp2(xs[i], u[i], xs[j], u[j], p)
        if any((c0 + c1 * xs[l]) % p != u[l] for l in T[2:]):
            return False
    return True

def agreement_sets(w, xs, p, a):
    """all maximal agreement sets (size >= a) of affine functions with w."""
    n = len(xs)
    seen, out = set(), []
    for i, j in itertools.combinations(range(n), 2):
        c0, c1 = interp2(xs[i], w[i], xs[j], w[j], p)
        T = frozenset(l for l in range(n) if (c0 + c1 * xs[l]) % p == w[l])
        if len(T) >= a and T not in seen:
            seen.add(T)
            out.append(T)
    return out

def bad_criterion(gamma, u0, u1, xs, p, a=4):
    w = [(u0[i] + gamma * u1[i]) % p for i in range(len(xs))]
    return any(not explained(T, u0, u1, xs, p) for T in agreement_sets(w, xs, p, a))

def bad_bruteforce(gamma, u0, u1, xs, p, a=4):
    """faithful: exists S subset of an agreement set, |S| >= a, S unexplained."""
    w = [(u0[i] + gamma * u1[i]) % p for i in range(len(xs))]
    for T in agreement_sets(w, xs, p, a):
        for s in range(a, len(T) + 1):
            for S in itertools.combinations(sorted(T), s):
                if not explained(S, u0, u1, xs, p):
                    return True
    return False

def bad_count(u0, u1, xs, p, a=4):
    return sum(1 for gamma in range(p) if bad_criterion(gamma, u0, u1, xs, p, a))

def main():
    rng = random.Random(357)
    report = []

    # ---- C1: criterion vs brute force, p=17 ----
    p = 17
    g, xs = setup(p)
    mismatch = 0
    nonempty = 0
    for trial in range(300):
        if trial % 3 == 0:  # low-entropy stress: explained blocks + noise
            c = [rng.randrange(p) for _ in range(8)]
            u0 = [(c[0] + c[1] * x) % p for x in xs]
            u1 = [(c[2] + c[3] * x) % p for x in xs]
            for _ in range(rng.randrange(1, 5)):
                u0[rng.randrange(8)] = rng.randrange(p)
                u1[rng.randrange(8)] = rng.randrange(p)
        else:
            u0 = [rng.randrange(p) for _ in range(8)]
            u1 = [rng.randrange(p) for _ in range(8)]
        bs1 = {gam for gam in range(p) if bad_criterion(gam, u0, u1, xs, p)}
        bs2 = {gam for gam in range(p) if bad_bruteforce(gam, u0, u1, xs, p)}
        if bs1 != bs2:
            mismatch += 1
            print("C1 MISMATCH:", u0, u1, sorted(bs1 ^ bs2))
        if bs1: nonempty += 1
    report.append(("C1 criterion==brute (300 stacks, p=17)", mismatch, 0))
    report.append(("C1 stacks with nonempty bad set", nonempty, None))

    # ---- C2: ownership mechanics, p=17 ----
    viol_a, viol_b = 0, 0
    for trial in range(120):
        u0 = [rng.randrange(p) for _ in range(8)]
        u1 = [rng.randrange(p) for _ in range(8)]
        # (b) unexplained triples collinear at >= 2 gammas?
        for t in itertools.combinations(range(8), 3):
            if explained(t, u0, u1, xs, p): continue
            cnt = 0
            for gam in range(p):
                w = [(u0[i] + gam * u1[i]) % p for i in range(8)]
                c0, c1 = interp2(xs[t[0]], w[t[0]], xs[t[1]], w[t[1]], p)
                if (c0 + c1 * xs[t[2]]) % p == w[t[2]]:
                    cnt += 1
            if cnt >= 2: viol_b += 1
        # (a) every bad gamma has >= 3 unexplained triples in some witness
        for gam in range(p):
            w = [(u0[i] + gam * u1[i]) % p for i in range(8)]
            for T in agreement_sets(w, xs, p, 4):
                if explained(T, u0, u1, xs, p): continue
                cnt = sum(1 for t in itertools.combinations(sorted(T), 3)
                          if not explained(t, u0, u1, xs, p))
                if cnt < 3: viol_a += 1
    report.append(("C2a witnesses with <3 unexplained triples", viol_a, 0))
    report.append(("C2b unexplained triples owning >=2 scalars", viol_b, 0))

    # ---- C3: max bad count, several primes ----
    for p in (17, 41, 113):
        g, xs = setup(p)
        best, bestcfg = 0, None
        # structured: two explained 3-blocks + 2 free
        for _ in range(60):
            u0 = [0] * 8; u1 = [0] * 8
            idx = list(range(8)); rng.shuffle(idx)
            for blk in (idx[0:3], idx[3:6]):
                a0, a1, b0, b1 = (rng.randrange(p) for _ in range(4))
                for i in blk:
                    u0[i] = (a0 + a1 * xs[i]) % p
                    u1[i] = (b0 + b1 * xs[i]) % p
            for i in idx[6:]:
                u0[i] = rng.randrange(p); u1[i] = rng.randrange(p)
            c = bad_count(u0, u1, xs, p)
            if c > best: best, bestcfg = c, ("blocks", list(u0), list(u1))
        # hill-climb
        restarts = 60 if p < 100 else 30
        for _ in range(restarts):
            u0 = [rng.randrange(p) for _ in range(8)]
            u1 = [rng.randrange(p) for _ in range(8)]
            cur = bad_count(u0, u1, xs, p)
            for _ in range(150):
                which, i, v = rng.randrange(2), rng.randrange(8), rng.randrange(p)
                tgt = u0 if which == 0 else u1
                old = tgt[i]; tgt[i] = v
                c2 = bad_count(u0, u1, xs, p)
                if c2 >= cur: cur = c2
                else: tgt[i] = old
            if cur > best: best, bestcfg = cur, ("hill", list(u0), list(u1))
        report.append((f"C3 max #bad at p={p} (bound 18, ceiling 32)", best, "<=18"))
        print(f"p={p}: max #bad = {best}  config={bestcfg[0] if bestcfg else None}")

    print("\n==== VERDICT TABLE ====")
    ok = True
    for name, got, want in report:
        if want == 0:
            verdict = "PASS" if got == 0 else "FAIL"
            if got != 0: ok = False
        elif want == "<=18":
            verdict = "PASS" if got <= 18 else "FAIL"
            if got > 18: ok = False
        else:
            verdict = "info"
        print(f"{name}: {got}  [{verdict}]")
    print("OVERALL:", "ALL PASS" if ok else "FAILURES PRESENT")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
