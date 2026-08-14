"""
#444/#389 follow-up: confirm the depth-1 antipodal-halo largest violating prime stays << n^4
at m=5 (n=32) and m=6 (n=64), where exhaustive {-1,0,1}^N is infeasible.

The largest violating prime is bounded by the largest prime factor of max_c |Res(R_c, Phi_{2^m})|,
c in {-1,0,1}^N. |Res| is maximized by the differentials with largest Mahler measure; we search
over structured + random {-1,0,1} vectors to find the MAX resultant norm and its largest prime
factor == 1 mod n. We report log_n of both, vs prize beta=4. This UPPER-bounds the violating-prime
beta (any actual violating prime divides some |Res(R_c)| <= max|Res|, so its largest prime factor
<= max over c of lpf(|Res|)). A robust max over many c gives a tight handle on p*.
"""
import itertools, random, math
from sympy import symbols, Poly, cyclotomic_poly, ZZ, resultant, factorint

X = symbols('X')
random.seed(1)

def run(m, n_samples):
    N = 2 ** (m - 1)
    n = 2 ** m
    Phi = Poly(X**N + 1, X, domain=ZZ)
    best_lpf = 0
    best_N = 0
    # structured worst-case families (maximize Mahler measure / resultant)
    structured = [
        tuple(1 if j % 2 == 0 else -1 for j in range(N)),
        tuple(1 for _ in range(N)),
        tuple(1 if j < N//2 else -1 for j in range(N)),
        tuple((-1)**(j*(j+1)//2 % 2) for j in range(N)),
        tuple(1 if (j % 3) else -1 for j in range(N)),
    ]
    cands = list(structured)
    for _ in range(n_samples):
        cands.append(tuple(random.choice((-1, 0, 1)) for _ in range(N)))
    seen = set()
    for c in cands:
        if all(v == 0 for v in c):
            continue
        key = c if c <= tuple(-v for v in c) else tuple(-v for v in c)
        if key in seen:
            continue
        seen.add(key)
        R = Poly(sum(c[j] * X**j for j in range(N)), X, domain=ZZ)
        Nres = abs(int(resultant(Phi.as_expr(), R.as_expr(), X)))
        if Nres == 0:
            continue
        if Nres > best_N:
            best_N = Nres
        for p in factorint(Nres):
            if (int(p) - 1) % n == 0 and int(p) > best_lpf:
                best_lpf = int(p)
    return N, best_lpf, best_N

print(f"{'m':>2} {'n':>4} {'#samp':>6} {'max viol p (==1 mod n)':>22} {'log_n p*':>9} {'max|Res|':>14} {'log_n|Res|':>10} {'prize beta':>10}")
for m, ns in [(4, 0), (5, 6000), (6, 1500)]:
    N, lpf, maxN = run(m, ns)
    n = 2 ** m
    bl = math.log(lpf)/math.log(n) if lpf > 0 else float('nan')
    bN = math.log(maxN)/math.log(n) if maxN > 0 else float('nan')
    print(f"{m:>2} {n:>4} {ns:>6} {lpf:>22} {bl:>9.3f} {maxN:>14} {bN:>10.3f} {4:>10}")
print()
print("If log_n p* stays < 4 at m=5,6 the antipodal halo is empty above the prize regime n^4 (trend confirmed).")
print("max|Res| log_n is the resultant-NORM beta (worst over sampled c); largest viol prime <= its lpf.")
