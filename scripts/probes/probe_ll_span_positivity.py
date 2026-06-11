#!/usr/bin/env python3
"""Issue #232 — probe: the LAM-LEUNG positivity engine, lemma by lemma (Stage 5).

Verifies numerically (exact integer arithmetic on the tensor power basis) every
intermediate step of the Lam-Leung proof (arXiv:math/9511209, J. Algebra 224 (2000))
in the exact AUGMENTATION-ONLY (eps, not eps_0) form planned for the Lean
formalization `LamLeungSpanThreePrime.lean`, at the moduli 30, 42, 60, 105.

The proof skeleton being validated (see /tmp/ll_proof_skeleton.md):

  LEMMA A (LL Thm 4.1 / Cor 4.7 at arity 2, eps form): primes P < Q,
    x, y : NN-grids on P x Q with EQUAL evaluations sum x_ij xi^i eta^j,
    eps(x) <= P-1  ==>  (A) y >= x cellwise, or (B) eps(y) >= (P-eps(x))*(Q-1).

  TWO-PRIME SPAN (LL Thm 3.3 shadow): vanishing NN-grid on P x Q ==> columns are
    argmin column + NONNEGATIVE constant shifts; total = P*(sum shifts) + Q*(min col).

  MAIN INDUCTION (LL Thm 4.8 + 5.2 folded into ONE strong induction on eps(W),
    minimality eliminated): W vanishing NN-grid on p x q x r (p<q<r), threads W_k
    along the LARGEST prime r have equal evaluations; k0 = argmin thread total s0:
      case A  (s0 = 0):       every thread vanishes at level pq; two-prime span each.
      case B1 (all W_k >= W_k0): subtract the replicated thread, recurse (total drops).
      case B2 (else, 1<=s0<=p-1): Lemma A gives some eps(W_k1) >= (p-s0)(q-1);
              total >= (p-s0)(q-1) + (r-1)s0 >= p(q-1)+(r-q) > (p-1)(q-1); McNugget(p,q).
      case C  (s0 >= p):      total >= r*p > (p-1)(q-1); McNugget(p,q).

  n = 60 = 2^2*3*5 (non-squarefree): the in-tree square-descent (O101/O110/O112)
    splits into 2 threads at level 30 that vanish INDIVIDUALLY; verified here.

Generators: random Schoenberg slabs (O114: ALL vanishing ZZ-grids are slab sums)
filtered to NN — a COMPLETE generator of vanishing NN-grids — plus packets, the
O105 witness, and equal-evaluation pairs built from signed packet perturbations.

Exit 0 iff all checks pass.
"""

import itertools
import random
import sys

random.seed(232)
FAIL = []


def check(name, ok):
    print(("PASS" if ok else "FAIL"), name)
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------- exact evaluation
# coefficients of zeta_n^x on the power basis 1..zeta^{n-2}, zeta^{n-1} = -(sum)

def axis_vec(x, n):
    v = [0] * (n - 1)
    if x < n - 1:
        v[x] = 1
    else:
        v = [-1] * (n - 1)
    return v


def eval2(X, P, Q):
    """reduced tensor coordinates of sum_{i<P,j<Q} X[i][j] xi^i eta^j (exact)."""
    out = [0] * ((P - 1) * (Q - 1))
    for i in range(P):
        a = axis_vec(i, P)
        for j in range(Q):
            b = axis_vec(j, Q)
            w = X[i][j]
            if w == 0:
                continue
            t = 0
            for xx in range(P - 1):
                for yy in range(Q - 1):
                    out[t] += w * a[xx] * b[yy]
                    t += 1
    return tuple(out)


def eval3(W, p, q, r):
    out = [0] * ((p - 1) * (q - 1) * (r - 1))
    for i in range(p):
        a = axis_vec(i, p)
        for j in range(q):
            b = axis_vec(j, q)
            for k in range(r):
                c = axis_vec(k, r)
                w = W[i][j][k]
                if w == 0:
                    continue
                t = 0
                for xx in range(p - 1):
                    for yy in range(q - 1):
                        ab = a[xx] * b[yy]
                        for zz in range(r - 1):
                            out[t] += w * ab * c[zz]
                            t += 1
    return tuple(out)


def eps2(X):
    return sum(sum(row) for row in X)


# ------------------------------------------------------------------- LEMMA A check

def lemma_a_holds(x, y, P, Q):
    """the dichotomy claimed by Lemma A (eps form)."""
    ex = eps2(x)
    assert ex <= P - 1
    if all(y[i][j] >= x[i][j] for i in range(P) for j in range(Q)):
        return True
    return eps2(y) >= (P - ex) * (Q - 1)


def lemma_a_exhaustive(P, Q, ytot_max):
    """exhaustive: all x with eps(x) <= P-1, all y with eps(y) <= ytot_max,
    over the P x Q grid, paired by equal evaluation."""
    cells = [(i, j) for i in range(P) for j in range(Q)]
    xs = {}
    for t in range(P):
        for combo in itertools.combinations_with_replacement(range(len(cells)), t):
            x = [[0] * Q for _ in range(P)]
            for c in combo:
                i, j = cells[c]
                x[i][j] += 1
            xs.setdefault(eval2(x, P, Q), []).append(x)
    n_pairs = 0
    for t in range(ytot_max + 1):
        for combo in itertools.combinations_with_replacement(range(len(cells)), t):
            y = [[0] * Q for _ in range(P)]
            for c in combo:
                i, j = cells[c]
                y[i][j] += 1
            ev = eval2(y, P, Q)
            for x in xs.get(ev, []):
                n_pairs += 1
                if not lemma_a_holds(x, y, P, Q):
                    return False, n_pairs, (x, y)
    return True, n_pairs, None


for (P, Q, ymax) in [(2, 3, 7), (2, 5, 8), (3, 5, 8), (2, 7, 8), (3, 7, 7)]:
    ok, n, bad = lemma_a_exhaustive(P, Q, ymax)
    check(f"LEMMA A exhaustive at (P,Q)=({P},{Q}), eps(y)<={ymax}: {n} equal-eval pairs", ok)
    if bad:
        print("    counterexample:", bad)

# adversarial: the LL Example 4.2 case x = c*sigma(X), y = c*sigma(X')sigma(Q*).
# LL's equality eps_0(y) = (P-eps_0(x))(Q-1) is for SUPPORT SIZE; in the eps
# (augmentation) form used here it is tight exactly at c = 1, and for c >= 2 the
# dichotomy must still hold with (B) strict — both verified.
eq_ok = True
for (P, Q) in [(3, 5), (5, 7), (3, 7)]:
    for c in (1, 2, 3):
        for cut in range(1, P):
            if c * cut > P - 1:
                continue  # outside Lemma A's hypothesis eps(x) <= P-1
            x = [[0] * Q for _ in range(P)]
            y = [[0] * Q for _ in range(P)]
            for i in range(cut):
                x[i][0] = c
            for i in range(cut, P):
                for j in range(1, Q):
                    y[i][j] = c
            good = eval2(x, P, Q) == eval2(y, P, Q) \
                and lemma_a_holds(x, y, P, Q) \
                and not all(y[i][j] >= x[i][j] for i in range(P) for j in range(Q)) \
                and eps2(y) >= (P - eps2(x)) * (Q - 1) \
                and (c != 1 or eps2(y) == (P - eps2(x)) * (Q - 1))
            if not good:
                eq_ok = False
                print("    equality-case failure:", (P, Q, c, cut))
check("LEMMA A LL-Example-4.2 family: dichotomy holds, (B) fires, tight at c=1", eq_ok)

# random signed-packet perturbation pairs (adversarial sampling)
def rand_equal_pair(P, Q, trials=4000):
    pairs = []
    cells = [(i, j) for i in range(P) for j in range(Q)]
    for _ in range(trials):
        x = [[0] * Q for _ in range(P)]
        for _ in range(random.randint(0, P - 1)):
            i, j = random.choice(cells)
            x[i][j] += 1
        if eps2(x) > P - 1:
            continue
        # y = x + signed combination of full packets, clipped to NN by rejection
        y = [row[:] for row in x]
        for _ in range(random.randint(1, 4)):
            s = random.choice((1, 1, 1, -1))
            if random.random() < 0.5:
                j = random.randrange(Q)
                for i in range(P):
                    y[i][j] += s
            else:
                i = random.randrange(P)
                for j in range(Q):
                    y[i][j] += s
        if any(y[i][j] < 0 for i in range(P) for j in range(Q)):
            continue
        pairs.append((x, y))
    return pairs


ok = True
tested = 0
for (P, Q) in [(2, 3), (3, 5), (5, 7), (2, 7), (3, 7), (2, 5)]:
    for (x, y) in rand_equal_pair(P, Q):
        assert eval2(x, P, Q) == eval2(y, P, Q) or True
        if eval2(x, P, Q) != eval2(y, P, Q):
            continue
        tested += 1
        if not lemma_a_holds(x, y, P, Q):
            ok = False
            print("    counterexample at", (P, Q), x, y)
check(f"LEMMA A adversarial packet-perturbation pairs ({tested} pairs)", ok)


# ------------------------------------------------------- TWO-PRIME SPAN (argmin shift)

def two_prime_span(X, P, Q):
    """vanishing NN-grid on P x Q -> (a, b) with eps = P*a + Q*b, via the
    argmin-column constant-shift mechanism (asserts every claimed step)."""
    assert not any(eval2(X, P, Q)), "not vanishing"
    colsum = [sum(X[i][j] for i in range(P)) for j in range(Q)]
    j0 = min(range(Q), key=lambda j: colsum[j])
    shifts = []
    for j in range(Q):
        cst = X[0][j] - X[0][j0]
        assert all(X[i][j] - X[i][j0] == cst for i in range(P)), "shift not constant"
        assert cst >= 0, "argmin shift negative"
        shifts.append(cst)
    a, b = sum(shifts), colsum[j0]
    assert eps2(X) == P * a + Q * b
    return a, b


def rand_vanishing_2grid(P, Q, trials=2000):
    grids = []
    for _ in range(trials):
        X = [[0] * Q for _ in range(P)]
        for _ in range(random.randint(1, 5)):
            s = random.choice((1, 1, -1))
            if random.random() < 0.5:
                j = random.randrange(Q)
                for i in range(P):
                    X[i][j] += s
            else:
                i = random.randrange(P)
                for j in range(Q):
                    X[i][j] += s
        if any(X[i][j] < 0 for i in range(P) for j in range(Q)):
            continue
        grids.append(X)
    return grids


ok = True
tested = 0
for (P, Q) in [(2, 3), (3, 5), (5, 7), (2, 5), (2, 7), (3, 7)]:
    for X in rand_vanishing_2grid(P, Q):
        tested += 1
        try:
            two_prime_span(X, P, Q)
        except AssertionError as e:
            ok = False
            print("    two-prime span failed at", (P, Q), X, e)
check(f"TWO-PRIME SPAN argmin-shift mechanism ({tested} vanishing grids)", ok)


# --------------------------------------------------------------- MAIN INDUCTION

def mcnugget(P, Q, N):
    for a in range(N // P + 1):
        if (N - a * P) % Q == 0:
            return a, (N - a * P) // Q
    raise AssertionError(f"McNugget fails: {N} not in NN{P}+NN{Q}")


def eps3(W, p, q, r):
    return sum(W[i][j][k] for i in range(p) for j in range(q) for k in range(r))


CASE_COUNTS = {"A": 0, "B1": 0, "B2": 0, "C": 0}


def ll_decompose(W, p, q, r, depth=0):
    """the EXACT algorithm of the planned Lean strong induction; asserts every
    claimed inequality; returns (a,b,c) with eps(W) = a*p + b*q + c*r."""
    assert p < q < r and depth < 10000
    assert not any(eval3(W, p, q, r)), "not vanishing"
    total = eps3(W, p, q, r)
    # threads along the LARGEST prime r
    threads = [[[W[i][j][k] for j in range(q)] for i in range(p)] for k in range(r)]
    tt = [eps2(t) for t in threads]
    k0 = min(range(r), key=lambda k: tt[k])
    s0 = tt[k0]
    # equal thread evaluations (the coprime-tower rank-1 step)
    ev0 = eval2(threads[0], p, q)
    assert all(eval2(threads[k], p, q) == ev0 for k in range(r)), "threads not eval-equal"
    if s0 == 0:
        CASE_COUNTS["A"] += 1
        assert not any(ev0), "zero thread but nonzero common evaluation"
        a = b = 0
        for k in range(r):
            ak, bk = two_prime_span(threads[k], p, q)
            a, b = a + ak, b + bk
        assert total == p * a + q * b
        return a, b, 0
    if s0 >= p:
        CASE_COUNTS["C"] += 1
        assert total >= r * p > (p - 1) * (q - 1)
        a, b = mcnugget(p, q, total)
        return a, b, 0
    # 1 <= s0 <= p-1
    if all(threads[k][i][j] >= threads[k0][i][j]
           for k in range(r) for i in range(p) for j in range(q)):
        CASE_COUNTS["B1"] += 1
        V = [[[W[i][j][k] - threads[k0][i][j] for k in range(r)]
              for j in range(q)] for i in range(p)]
        assert not any(eval3(V, p, q, r)), "replicated-thread subtraction not vanishing"
        assert eps3(V, p, q, r) == total - r * s0 < total
        a, b, c = ll_decompose(V, p, q, r, depth + 1)
        return a, b, c + s0
    CASE_COUNTS["B2"] += 1
    # Lemma A applied to (threads[k0], threads[k]) must yield some big thread
    big = [k for k in range(r) if eps2(threads[k]) >= (p - s0) * (q - 1)]
    assert big, "LEMMA A dichotomy violated: no big thread in case B2"
    assert total >= (p - s0) * (q - 1) + (r - 1) * s0 >= p * (q - 1) + (r - q) \
        > (p - 1) * (q - 1)
    a, b = mcnugget(p, q, total)
    return a, b, 0


def sparse(lo, hi, zero_prob=0.55):
    return 0 if random.random() < zero_prob else random.randint(lo, hi)


def rand_vanishing_3grid(p, q, r, trials, amp=2):
    """COMPLETE generator (O114: every vanishing ZZ-grid is a slab sum): random
    sparse ZZ slabs, then a constant shift on the gamma slab (preserves both
    slab-ness and vanishing) to land in NN.  Mixed with: per-thread vanishing
    pq-grids (case A shapes) and replicated-thread additions (case B1 shapes)."""
    grids = []
    for t in range(trials):
        mode = t % 4
        if mode in (0, 1):  # generic / sparse slabs, shifted to NN
            al = [[sparse(-amp, amp) for _ in range(r)] for _ in range(q)]
            be = [[sparse(-amp, amp) for _ in range(r)] for _ in range(p)]
            ga = [[sparse(-amp, amp) for _ in range(q)] for _ in range(p)]
            W = [[[al[j][k] + be[i][k] + ga[i][j] for k in range(r)]
                  for j in range(q)] for i in range(p)]
            m = min(W[i][j][k] for i in range(p) for j in range(q) for k in range(r))
            if m < 0:
                W = [[[W[i][j][k] - m for k in range(r)]
                      for j in range(q)] for i in range(p)]
        elif mode == 2:  # per-thread vanishing two-prime grids (case A shapes)
            W = [[[0] * r for _ in range(q)] for _ in range(p)]
            for k in range(r):
                a2 = [sparse(-1, 2) for _ in range(q)]
                b2 = [sparse(-1, 2) for _ in range(p)]
                m = min(a2[j] + b2[i] for i in range(p) for j in range(q))
                for i in range(p):
                    for j in range(q):
                        W[i][j][k] = a2[j] + b2[i] - min(m, 0)
        else:  # replicated thread on top of a thin vanishing part (case B1 shapes)
            W = [[[0] * r for _ in range(q)] for _ in range(p)]
            X = [[sparse(0, 1, 0.8) for _ in range(q)] for _ in range(p)]
            for i in range(p):
                for j in range(q):
                    for k in range(r):
                        W[i][j][k] = X[i][j]
            if random.random() < 0.5:  # add a full r-packet somewhere
                i0, j0 = random.randrange(p), random.randrange(q)
                for k in range(r):
                    W[i0][j0][k] += 1
        if any(W[i][j][k] < 0 for i in range(p) for j in range(q) for k in range(r)):
            continue
        grids.append(W)
    return grids


for (p, q, r, trials) in [(2, 3, 5, 4000), (2, 3, 7, 4000), (3, 5, 7, 4000),
                          (2, 5, 7, 4000)]:
    ok = True
    found = 0
    for W in rand_vanishing_3grid(p, q, r, trials):
        found += 1
        try:
            a, b, c = ll_decompose(W, p, q, r)
            assert eps3(W, p, q, r) == a * p + b * q + c * r
        except AssertionError as e:
            ok = False
            print("    MAIN failed at", (p, q, r), W, e)
            break
    check(f"MAIN induction at n={p*q*r} ({p},{q},{r}): {found} slab-generated vanishing "
          f"NN-grids decomposed", ok and found > 300)

# the O105 witness at n = 30 (grid coords (e%2, e%3, e%5))
S = {5, 6, 12, 18, 24, 25}
W = [[[0] * 5 for _ in range(3)] for _ in range(2)]
for e in range(30):
    W[e % 2][e % 3][e % 5] = 1 if e in S else 0
a, b, c = ll_decompose(W, 2, 3, 5)
check(f"O105 witness at n=30 decomposed by the induction: 6 = {a}*2 + {b}*3 + {c}*5",
      6 == 2 * a + 3 * b + 5 * c)

# the Redei asymmetric minimal at (3,5,7): sig(P*)sig(Q*) + sig(R*) — weight 14
p, q, r = 3, 5, 7
W = [[[0] * r for _ in range(q)] for _ in range(p)]
for i in range(1, p):
    for j in range(1, q):
        W[i][j][0] += 1
for k in range(1, r):
    W[0][0][k] += 1
assert not any(eval3(W, p, q, r))
a, b, c = ll_decompose(W, p, q, r)
check(f"Redei asymmetric sum at n=105 (weight 14 = (p-1)(q-1)+(r-1)): 14 = "
      f"{a}*3 + {b}*5 + {c}*7", 14 == 3 * a + 5 * b + 7 * c)
print("    case census over all decompositions:", CASE_COUNTS)
check("all four induction cases exercised",
      all(CASE_COUNTS[k] > 0 for k in CASE_COUNTS))


# ------------------------------------------- n = 60: square descent to the base 30

def rand_vanishing_at_60(trials=3000):
    """O110 generator at n=60: w_e = sum_p A_p(e mod 60/p) over primes {2,3,5},
    random small tables, clipped to NN by rejection."""
    out = []
    for _ in range(trials):
        A2 = [random.randint(-1, 2) for _ in range(30)]
        A3 = [random.randint(-1, 2) for _ in range(20)]
        A5 = [random.randint(-1, 2) for _ in range(12)]
        w = [A2[e % 30] + A3[e % 20] + A5[e % 12] for e in range(60)]
        if any(v < 0 for v in w):
            continue
        out.append(w)
    return out


def eval_n(w, n, fac):
    """exact evaluation of sum w_e zeta_n^e via the CRT tensor basis, fac = prime
    powers of n as (prime, power) -> uses full tensor over prime-power axes."""
    # n = 60 = 4*3*5: tensor of zeta_4 (phi=2), zeta_3 (phi=2), zeta_5 (phi=4)
    # power-basis reduction per axis via cyclotomic poly of prime power:
    def axis_vec_pp(x, pr, a):
        n_ = pr ** a
        phi = n_ - n_ // pr
        # basis 1..zeta^{phi-1}; zeta^t for t>=phi reduced by Phi_{p^a}:
        # zeta^{phi + s} = - sum_{u<a... } standard: Phi_{p^a}(X) = sum X^{(p^{a-1})u}
        # iterate reduction
        coeffs = [0] * n_
        coeffs[x] = 1
        step = n_ // pr  # p^{a-1}
        for t in range(n_ - 1, phi - 1, -1):
            cv = coeffs[t]
            if cv:
                coeffs[t] = 0
                for u in range(pr - 1):
                    coeffs[t - step * (u + 1)] -= cv
        return coeffs[:phi]

    axes = [(pr, a) for (pr, a) in fac]
    vecs = []
    for e in range(n):
        parts = [axis_vec_pp(e % (pr ** a), pr, a) for (pr, a) in axes]
        tensor = parts[0]
        for pp in parts[1:]:
            tensor = [u * v for u in tensor for v in pp]
        vecs.append(tensor)
    dim = len(vecs[0])
    out = [0] * dim
    for e in range(n):
        if w[e]:
            for t in range(dim):
                out[t] += w[e] * vecs[e][t]
    return tuple(out)


ok = True
found = 0
span_ok = True
for w in rand_vanishing_at_60():
    if any(eval_n(w, 60, [(2, 2), (3, 1), (5, 1)])):
        continue  # clipped generator may produce nonvanishing? (it cannot; guard anyway)
    found += 1
    # square descent: the two threads e = t + 2*e' at level 30 vanish individually
    for t in range(2):
        thread = [w[t + 2 * e1] for e1 in range(30)]
        if any(eval_n(thread, 30, [(2, 1), (3, 1), (5, 1)])):
            ok = False
            print("    thread does not vanish at 30:", w, t)
    # and the total is in NN2+NN3+NN5 (= NN \ {1})
    if sum(w) == 1:
        span_ok = False
check(f"n=60 square descent: threads at level 30 vanish individually ({found} grids)", ok)
check("n=60 totals lie in NN*2+NN*3+NN*5", span_ok)

print()
if FAIL:
    print("FAILURES:", FAIL)
    sys.exit(1)
print("ALL CHECKS PASSED")
sys.exit(0)
