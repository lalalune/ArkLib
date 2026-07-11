#!/usr/bin/env python3
"""Probe: Lam-Leung positivity bricks A and B (weight/augmentation form), pre-formalization.

Pre-registered hypotheses (from LL00 Thm 4.1 / Cor 4.7 / Thm 4.8, transcribed for the
CRT-grid weight forms about to be formalized):

  BRICK A (comparison engine, weight form, squarefree pq, p < q):
    for x, y : N-grids on range p x range q with eval(x) = eval(y) at (xi, eta)
    and weight(x) <= p-1:
      (A) y >= x pointwise, OR (B) weight(y) >= (p - weight(x)) * (q - 1).

  BRICK B (minimal-element lower bound, weight form, squarefree pqr, p < q < r):
    every minimal vanishing N-grid W on p x q x r has
      weight(W) in {p, q, r}  OR  weight(W) >= p*(q-1) + r - q.

Method: exact integer arithmetic in Z[zeta_n] via coefficient vectors mod Phi_n
(divisibility test by exact monic polynomial division). Enumeration of equal-eval
partners via the Redei-de Bruijn-Schoenberg Z-kernel basis (row/column packets),
which spans the full eval kernel at squarefree moduli (in-tree O108).

Exit 0 iff both hypotheses survive every generated instance.
"""
import itertools, random, sys
random.seed(357)

def poly_mul(a, b):
    out = [0]*(len(a)+len(b)-1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                out[i+j] += ai*bj
    return out

def poly_divmod_exact(num, den):
    # den monic; exact integer division
    num = num[:]
    dd = len(den)-1
    q = [0]*(max(len(num)-dd, 1))
    while len(num)-1 >= dd and any(num):
        while num and num[-1] == 0:
            num.pop()
        if len(num)-1 < dd:
            break
        c = num[-1]
        k = len(num)-1-dd
        q[k] = c
        for i, dco in enumerate(den):
            num[k+i] -= c*dco
    while num and num[-1] == 0:
        num.pop()
    return q, num

def cyclotomic(n, _cache={}):
    if n in _cache:
        return _cache[n]
    # Phi_n = (X^n - 1) / prod_{d|n, d<n} Phi_d
    num = [-1] + [0]*(n-1) + [1]
    for d in range(1, n):
        if n % d == 0:
            num, rem = poly_divmod_exact(num, cyclotomic(d))
            assert not rem
    _cache[n] = num
    return num

def vanishes(vec, n):
    # vec: length-n integer exponent vector; test Phi_n | sum vec[e] X^e
    _, rem = poly_divmod_exact(vec[:], cyclotomic(n))
    return not rem

def crt_index(p, q, i, j):
    # exponent e < p*q with e = i mod p, e = j mod q
    for e in range(p*q):
        if e % p == i and e % q == j:
            return e
    raise AssertionError

def grid_to_vec2(p, q, W):
    v = [0]*(p*q)
    for i in range(p):
        for j in range(q):
            v[crt_index(p, q, i, j)] = W[i][j]
    return v

def crt_index3(p, q, r, i, j, k):
    for e in range(p*q*r):
        if e % p == i and e % q == j and e % r == k:
            return e
    raise AssertionError

def grid_to_vec3(p, q, r, W):
    v = [0]*(p*q*r)
    for i in range(p):
        for j in range(q):
            for k in range(r):
                v[crt_index3(p, q, r, i, j, k)] = W[i][j][k]
    return v

def weight2(W):
    return sum(sum(row) for row in W)

# ---------------- BRICK A ----------------
def brick_A(p, q, coef_lo=-2, coef_hi=2, verbose=False):
    """Exhaustive over x with weight(x) <= p-1 (entries placed anywhere) and ALL y
    with eval(y) = eval(x) reachable by kernel shifts with coefficients in box."""
    n = p*q
    cells = [(i, j) for i in range(p) for j in range(q)]
    # all x with total weight <= p-1
    xs = []
    for w in range(p):  # 0..p-1
        for combo in itertools.combinations_with_replacement(cells, w):
            W = [[0]*q for _ in range(p)]
            for (i, j) in combo:
                W[i][j] += 1
            xs.append(W)
    checked = 0
    viol = 0
    rng = range(coef_lo, coef_hi+1)
    for x in xs:
        wx = weight2(x)
        # kernel basis: p rows (each = mu_q coset, all-ones in row i), q cols
        for acoefs in itertools.product(rng, repeat=p):
            for bcoefs in itertools.product(rng, repeat=q):
                y = [[x[i][j] + acoefs[i] + bcoefs[j] for j in range(q)] for i in range(p)]
                if any(y[i][j] < 0 for i in range(p) for j in range(q)):
                    continue
                checked += 1
                geA = all(y[i][j] >= x[i][j] for i in range(p) for j in range(q))
                wy = weight2(y)
                geB = wy >= (p - wx) * (q - 1)
                if not (geA or geB):
                    viol += 1
                    if verbose:
                        print("VIOLATION A", p, q, x, y)
    # sanity: equal evals by construction (kernel shifts); spot-verify a few
    for _ in range(50):
        x = random.choice(xs)
        acoefs = [random.randint(coef_lo, coef_hi) for _ in range(p)]
        bcoefs = [random.randint(coef_lo, coef_hi) for _ in range(q)]
        y = [[x[i][j] + acoefs[i] + bcoefs[j] for j in range(q)] for i in range(p)]
        d = [[y[i][j] - x[i][j] for j in range(q)] for i in range(p)]
        assert vanishes(grid_to_vec2(p, q, d), n), "kernel basis broken"
    return checked, viol

# ---------------- BRICK B ----------------
def submultisets_vanishing_proper(p, q, r, W, wtot):
    """Search a proper nonzero vanishing submultiset (early exit)."""
    cells = [(i, j, k) for i in range(p) for j in range(q) for k in range(r)
             if W[i][j][k] > 0]
    ranges = [range(W[i][j][k]+1) for (i, j, k) in cells]
    n = p*q*r
    for combo in itertools.product(*ranges):
        s = sum(combo)
        if s == 0 or s == wtot:
            continue
        V = [[[0]*r for _ in range(q)] for _ in range(p)]
        for (idx, (i, j, k)) in enumerate(cells):
            V[i][j][k] = combo[idx]
        if vanishes(grid_to_vec3(p, q, r, V), n):
            return True
    return False

def brick_B(p, q, r, trials=4000, max_weight=None, verbose=False):
    """Random mixed-sign A+B+C kernel points >= 0; minimality by exhaustive
    submultiset search (bounded weight); check the weight law."""
    n = p*q*r
    bound = p*(q-1) + r - q
    if max_weight is None:
        max_weight = bound + max(p, 4)  # look past the bound a bit
    found_minimal = 0
    viol = 0
    seen = set()
    for _ in range(trials):
        A = [[random.randint(-1, 1) for _ in range(r)] for _ in range(q)]
        B = [[random.randint(-1, 1) for _ in range(r)] for _ in range(p)]
        C = [[random.randint(-1, 1) for _ in range(q)] for _ in range(p)]
        W = [[[A[j][k] + B[i][k] + C[i][j] for k in range(r)] for j in range(q)]
             for i in range(p)]
        if any(W[i][j][k] < 0 for i in range(p) for j in range(q) for k in range(r)):
            continue
        wtot = sum(W[i][j][k] for i in range(p) for j in range(q) for k in range(r))
        if wtot == 0 or wtot > max_weight:
            continue
        key = tuple(W[i][j][k] for i in range(p) for j in range(q) for k in range(r))
        if key in seen:
            continue
        seen.add(key)
        assert vanishes(grid_to_vec3(p, q, r, W), n)
        if submultisets_vanishing_proper(p, q, r, W, wtot):
            continue
        found_minimal += 1
        ok = (wtot in (p, q, r)) or (wtot >= bound)
        if not ok:
            viol += 1
            if verbose:
                print("VIOLATION B", (p, q, r), "weight", wtot, W)
    return found_minimal, viol

def main():
    ok = True
    for (p, q) in [(2, 3), (2, 5), (3, 5)]:
        c, v = brick_A(p, q, verbose=True)
        print(f"BRICK A ({p},{q}): {c} equal-eval pairs checked, {v} violations")
        ok = ok and v == 0
    # the LL asymmetric minimal at n=30 must appear and have weight exactly 6 = bound
    for (p, q, r, t) in [(2, 3, 5, 6000), (3, 5, 7, 1500)]:
        m, v = brick_B(p, q, r, trials=t, verbose=True)
        bound = p*(q-1) + r - q
        print(f"BRICK B ({p},{q},{r}): {m} minimal elements found, bound {bound}, "
              f"{v} violations")
        ok = ok and v == 0 and m > 0
    print("PROBE", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
