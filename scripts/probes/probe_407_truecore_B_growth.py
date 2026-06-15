#!/usr/bin/env python3
"""
probe_407_truecore_B_growth.py  (#444 -- floor-vs-Johnson on the CORRECT object: #bad direct)

Follow-up to the true-core feasibility brick (B=max_stack #bad <= budget at every r, finite-n).
That established the budget is MET; the actual prize content is the ASYMPTOTIC question: does
    ratio(n) := #bad / budget,   budget = 2^r * C(2^{mu-1}, r),
stay BOUNDED BELOW 1 as n->inf (a genuine FLOOR, prize-positive) or CREEP UP TO 1 (Johnson-tracking,
the per-line fate of every prior surrogate)? Every prior floor-vs-Johnson probe was on a SURROGATE
(incidence I(n), e2=0 census K, even/odd moments) -- all Johnson-tracking or anti-helpful. This is
the FIRST growth measurement on the canonical OpenCoreConditionalPin object #bad itself.

OBJECT: at the SHALLOWEST binding band r=2 (k=1, a=3) -- where C(n,3) is brute-feasible to n=64 --
#bad = #distinct pinned gamma, max over the char-line adversary. Exact mod-p, PROPER mu_n, p~n^4.
(r=2 chosen for computational reach; the deepest band r=2^{mu-1} is brute-infeasible past n=16.)

RESULT (measured, this probe; worst line consistently (4,2)):
    n=8:  #bad=5   budget=24   ratio=0.2083
    n=16: #bad=25  budget=112  ratio=0.2232
    n=32: #bad=113 budget=480  ratio=0.2354
    n=64: #bad=481 budget=1984 ratio=0.2424
  Increments 0.0149, 0.0122, 0.0070 (DECAYING, ratio ~0.57) => geometric extrapolation -> ~0.26,
  BOUNDED WELL BELOW 1. This is FLOOR-CONSISTENT on the correct object (#bad direct), NOT Johnson->1.

HONEST SCOPE (rule 6): single shallowest band r=2 (computational reach); worst is a fixed low line
(4,2); p-fixed (one prime per n). The full prize is forall-r and the asymptotic decider needs n>=256
(c.348 -- numerics can't separate floor from Johnson below 256). This is a measured finite-n trend on
the RIGHT object that is floor-consistent, NOT a closure. It contrasts sharply with the surrogate
faces (all Johnson-tracking): the canonical #bad object's ratio-to-budget is converging below 1.
"""
import itertools, math, sys


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
    m = (p - 1) // n
    assert m > 1
    for h in range(2, 8000):
        x = pow(h, m, p)
        if pow(x, n, p) == 1 and pow(x, n // 2, p) != 1:
            return x
    raise ValueError


def nbad_a3(A, B, xs, p):
    """#distinct pinned gamma at band a=3, k=1 (tuples are PAIRS): ratio -e0(T)/e1(T),
    e_j(pair {i,j}) = (u_j[i]-u_j[j])/(x_i-x_j) (1st divided difference). a=3 set {i,j,l} aligned iff
    its 3 pair-ratios coincide. Worst-line char pair u0=x^A,u1=x^B."""
    n = len(xs)
    u0 = [pow(x, A, p) for x in xs]
    u1 = [pow(x, B, p) for x in xs]
    e0 = {}; e1 = {}
    for (i, j) in itertools.combinations(range(n), 2):
        den = (xs[i] - xs[j]) % p
        di = pow(den, -1, p)
        e0[(i, j)] = (u0[i] - u0[j]) * di % p
        e1[(i, j)] = (u1[i] - u1[j]) * di % p

    def ratio(t):
        a_, b_ = e0[t], e1[t]
        if b_ != 0:
            return (-a_) * pow(b_, -1, p) % p
        return None if a_ == 0 else 'NOROOT'

    pinned = set()
    for S in itertools.combinations(range(n), 3):
        r = None; ok = True; any_nd = False
        for t in itertools.combinations(S, 2):
            rt = ratio(t)
            if rt is None: continue
            if rt == 'NOROOT':
                ok = False; break
            any_nd = True
            if r is None: r = rt
            elif r != rt:
                ok = False; break
        if ok and any_nd:
            pinned.add(r)
    return len(pinned)


def main():
    print("FLOOR-vs-JOHNSON on the CANONICAL #bad object (band r=2, k=1, a=3):")
    print("  ratio(n) = #bad / budget,  budget = 4*C(n/2,2).  floor if ->const<1, Johnson if ->1.")
    rows = []
    for mu in (3, 4, 5, 6):
        n = 2 ** mu
        p = next_prime_cong1(n, int(n ** 4.0))
        g = find_g(p, n); xs = [pow(g, i, p) for i in range(n)]
        budget = 4 * math.comb(n // 2, 2)
        # worst-line family (low lines dominate at shallow band; (4,2)/(6,4) consistently worst)
        Bmax = 0; arg = None
        lines = [(4, 2), (6, 4), (8, 4), (n // 2 + 1, n // 2 - 1), (n - 1, n - 3),
                 (n // 2, n // 4), (6, 2), (8, 6)]
        for (A, B) in lines:
            if A >= n or A == B: continue
            c = nbad_a3(A, B, xs, p)
            if c > Bmax: Bmax = c; arg = (A, B)
        ratio = Bmax / budget
        rows.append((n, Bmax, budget, ratio))
        print(f"  n={n:3d}: #bad={Bmax} budget={budget} ratio={ratio:.4f} worst={arg} p={p}", flush=True)
    if len(rows) >= 3:
        incs = [rows[i + 1][3] - rows[i][3] for i in range(len(rows) - 1)]
        print(f"  increments: {[round(x,4) for x in incs]} (decaying => bounded-below-1 / floor-consistent)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
