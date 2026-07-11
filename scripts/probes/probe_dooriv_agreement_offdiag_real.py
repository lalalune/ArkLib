import itertools, cmath, math, random
from collections import defaultdict

# resonance moment T(r) for ZMod m, generic unit-modulus phase u: ZMod m -> C
# phaseSum u r c = sum over X in (Fin r -> ZMod m), all X_i != 0, sum X_i = c, of prod u(X_i)
# T(r) = sum_c |phaseSum|^2
# agreement double = sum_{X,Y both nonzero, sumX=sumY} conj(prod u X) * prod u Y
# diagonal = sum_{X nonzero} |prod u X|^2
# off-diagonal = agreement_double - diagonal  (X != Y, sumX=sumY)
# CLAIM A: agreement_double is REAL (im ~ 0)
# CLAIM B: off-diagonal is REAL (im ~ 0)
# CLAIM C: agreement_double == T(r) (real)

def run(m, r, u):
    nz = [a for a in range(m) if a != 0]
    tuples = list(itertools.product(nz, repeat=r))
    fib = defaultdict(complex)
    for X in tuples:
        c = sum(X) % m
        fib[c] += math.prod(u[a] for a in X)
    T = sum(abs(v) ** 2 for v in fib.values())
    agr = 0j
    diag = 0j
    for X in tuples:
        sx = sum(X) % m
        pX = math.prod(u[a] for a in X)
        for Y in tuples:
            if sum(Y) % m == sx:
                term = pX.conjugate() * math.prod(u[a] for a in Y)
                agr += term
                if X == Y:
                    diag += term
    off = agr - diag
    return T, agr, diag, off

random.seed(1)
maxim = 0.0
for m in [3, 4, 5, 7]:
    for r in [1, 2, 3]:
        for trial in range(4):
            u = {0: 0j}
            for a in range(1, m):
                th = random.uniform(0, 2 * math.pi)
                u[a] = cmath.exp(1j * th)
            T, agr, diag, off = run(m, r, u)
            im_agr = abs(agr.imag)
            im_off = abs(off.imag)
            err_T = abs(agr.real - T)
            maxim = max(maxim, im_agr, im_off, err_T)
            if im_agr > 1e-9 or im_off > 1e-9 or err_T > 1e-9:
                print(f"VIOLATION m={m} r={r}: im_agr={im_agr:.2e} im_off={im_off:.2e} errT={err_T:.2e}")
print(f"max(|im agr|, |im off|, |agr.re - T|) over all trials = {maxim:.2e}")
print("Verdict: agreement double + off-diagonal are REAL, and agr.re == T(r). PASS" if maxim < 1e-9 else "FAIL")
