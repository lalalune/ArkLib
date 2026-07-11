#!/usr/bin/env python3
"""Probe (#371): is the KKH26 family EXTREMAL for the deep alignment census?

At (n=16, k=3, mu=3, m=2, r=3), band a=6 (the KKH26 ceiling band), the census
probe found: KKH26 [x^6,x^4] has 56 alignable 6-sets (the squaring-fibre unions);
every other tested line has 0 (one exotic family pins a single scalar).

THIS PROBE attacks extremality:
 (E1) exhaustive character sweep: #alignable 6-sets for ALL pairs [x^a, x^b];
 (E2) perturbation: does the KKH26 line's 56 survive/grow under 1-3 coordinate
      mutations? (graded objective for gradient);
 (E3) graded hill-climb from random + from KKH26, objective =
      #aligned + 0.001 * sum(max ratio multiplicity - 1)  (near-alignment credit).

If anything beats 56, the deployed extremizer is NOT the KKH26 family (answer-
changing). If nothing does, strong evidence the conjectured delta* value is the
deep-census truth at this scale.
"""
import itertools, random, sys

N, K, P = 16, 3, 12289
A_BAND = 6


def find_g(p, n):
    for h in range(2, 500):
        x = pow(h, (p - 1) // n, p)
        if pow(x, n // 2, p) != 1 and pow(x, n, p) == 1:
            return x
    raise ValueError


G = find_g(P, N)
XS = [pow(G, i, P) for i in range(N)]
TUPLES = list(itertools.combinations(range(N), K + 1))
SIXSETS = list(itertools.combinations(range(N), A_BAND))
SUBT = {S: list(itertools.combinations(S, K + 1)) for S in SIXSETS}
INVDEN = {}
for T in TUPLES:
    for i in T:
        d = 1
        for j in T:
            if i != j:
                d = d * ((XS[i] - XS[j]) % P) % P
        INVDEN[(T, i)] = pow(d, -1, P)


def dd(T, u):
    return sum(u[i] * INVDEN[(T, i)] for i in T) % P


def ratios(u0, u1):
    e0 = {T: dd(T, u0) for T in TUPLES}
    e1 = {T: dd(T, u1) for T in TUPLES}
    r = {}
    for T in TUPLES:
        if e1[T] != 0:
            r[T] = (-e0[T]) * pow(e1[T], -1, P) % P
        elif e0[T] == 0:
            r[T] = None      # degenerate (free)
        else:
            r[T] = 'NR'      # fits no gamma
    return r


def census_graded(u0, u1):
    """(#aligned 6-sets, graded score)."""
    r = ratios(u0, u1)
    aligned, grade = 0, 0
    for S in SIXSETS:
        vals = {}
        bad = False
        nd = 0
        for T in SUBT[S]:
            rt = r[T]
            if rt is None:
                continue
            if rt == 'NR':
                bad = True
                break
            nd += 1
            vals[rt] = vals.get(rt, 0) + 1
        if bad or nd == 0:
            continue
        mx = max(vals.values())
        if mx == nd:
            aligned += 1
        grade += mx - 1
    return aligned, grade


def main():
    rng = random.Random(372)
    kk_u0 = [pow(x, 6, P) for x in XS]
    kk_u1 = [pow(x, 4, P) for x in XS]
    base = census_graded(kk_u0, kk_u1)
    print(f"KKH26 [x^6,x^4] baseline: aligned={base[0]} grade={base[1]}", flush=True)

    # E1: exhaustive character sweep at depth
    best_char, best_pair = 0, None
    for a in range(N):
        for b in range(N):
            if a == b:
                continue
            u0 = [pow(x, a, P) for x in XS]
            u1 = [pow(x, b, P) for x in XS]
            al, _ = census_graded(u0, u1)
            if al > best_char:
                best_char, best_pair = al, (a, b)
    print(f"E1 char sweep: max aligned-6-sets = {best_char} at {best_pair}", flush=True)

    # E2: perturbations of the KKH26 line
    best_pert = base[0]
    for trial in range(120):
        u0, u1 = list(kk_u0), list(kk_u1)
        for _ in range(rng.randrange(1, 4)):
            which, i, v = rng.randrange(2), rng.randrange(N), rng.randrange(P)
            (u0 if which == 0 else u1)[i] = v
        al, _ = census_graded(u0, u1)
        if al > best_pert:
            best_pert = al
            print(f"  E2 BEAT: {al} at trial {trial}", flush=True)
    print(f"E2 perturbation max: {best_pert} (baseline {base[0]})", flush=True)

    # E3: graded hill-climb, random + KKH26 starts
    best_hc = 0
    for restart in range(8):
        if restart < 4:
            u0 = [rng.randrange(P) for _ in range(N)]
            u1 = [rng.randrange(P) for _ in range(N)]
        else:
            u0, u1 = list(kk_u0), list(kk_u1)
        al, gr = census_graded(u0, u1)
        cur = al * 10000 + gr
        for _ in range(120):
            which, i, v = rng.randrange(2), rng.randrange(N), rng.randrange(P)
            tgt = u0 if which == 0 else u1
            old = tgt[i]
            tgt[i] = v
            al2, gr2 = census_graded(u0, u1)
            sc2 = al2 * 10000 + gr2
            if sc2 >= cur:
                cur = sc2
                al = al2
            else:
                tgt[i] = old
        best_hc = max(best_hc, al)
        print(f"  E3 restart {restart}: final aligned = {al}", flush=True)
    print(f"E3 hill-climb max: {best_hc}", flush=True)

    mx = max(best_char, best_pert, best_hc, base[0])
    print("\n==== VERDICT ====")
    print(f"global max found: {mx}; KKH26 baseline: {base[0]}")
    if mx > base[0]:
        print("EXTREMALITY CHALLENGED: something beats the KKH26 deep supply.")
    else:
        print("KKH26 EXTREMAL at this scale: nothing found beats 56 aligned 6-sets.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
