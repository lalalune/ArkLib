#!/usr/bin/env python3
"""
G3 probe: M(d, w, n) = max # of projectively-distinct SPLIT members (monic,
w distinct roots all in D) of a d-dimensional subspace W of F[X]_{<=w} that
CONTAINS a domain-nonvanishing degree-w member l0.

Conjecture G3-a: for the fiber spaces arising in the WB window
(W = lifts of {m-hat == u*g mod l0, deg g <= D_def}, dim = D_def + 2),
   M <= (D_def + 1) + floor(n/w)   [= w+1 at the deepest window row].

Tests:
 (1) Fiber-shaped spaces: sample (l0, u) at (11,10,4) and (13,12,4),
     D_def = 1, 2 (dims 3, 4): exhaustively count split members in W.
 (2) Adversarial general subspaces of dim d containing some nonvanishing l0:
     spanned by split members (greedy adversarial): how big can M get?
 (3) The structure of maximizers (coset towers? partial fractions?).

Method: a split member with root set T (|T| = w) is c*m_T; m_T in W is a rank
condition: rank(W-basis + m_T) == dim W. Enumerate all C(n, w) candidate T.
Also count smaller-degree split members (|T| < w) projectively.
"""
import itertools, random

def order_subgroup(q, n):
    for cand in range(2, q):
        seen = set(); x = 1
        for _ in range(q - 1):
            x = (x * cand) % q; seen.add(x)
        if len(seen) == q - 1:
            g = cand; break
    h = pow(g, (q - 1) // n, q)
    return sorted({pow(h, j, q) for j in range(n)})

def polmul(a, b, q):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % q
    return out

def poleval(p, x, q):
    return sum(c * pow(x, i, q) for i, c in enumerate(p)) % q

def polmod(a, b, q):
    a = [x % q for x in a]
    db = max(i for i in range(len(b)) if b[i] % q)
    inv = pow(b[db], q - 2, q)
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i] % q
        if c:
            f = (c * inv) % q
            for j in range(db + 1):
                a[i - db + j] = (a[i - db + j] - f * b[j]) % q
    return [x % q for x in a[:db]]

def rank(M, q, width):
    M = [r[:] + [0] * (width - len(r)) for r in M]
    r = 0
    for col in range(width):
        piv = None
        for row in range(r, len(M)):
            if M[row][col] % q:
                piv = row; break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        ip = pow(M[r][col], q - 2, q)
        for row in range(len(M)):
            if row != r and M[row][col] % q:
                f = (M[row][col] * ip) % q
                for cc in range(width):
                    M[row][cc] = (M[row][cc] - f * M[r][cc]) % q
        r += 1
    return r

def m_of(T, q):
    out = [1]
    for x in T:
        out = polmul(out, [(-x) % q, 1], q)
    return out

def count_split_members(basis, q, n, w, D):
    """count T (|T| <= w) with m_T in span(basis) (projectively distinct
       automatically: distinct T give non-proportional m_T)."""
    width = w + 1
    r0 = rank(basis, q, width)
    cnt = 0
    members = []
    for size in range(1, w + 1):
        for T in itertools.combinations(D, size):
            mT = m_of(T, q)
            if rank(basis + [mT], q, width) == r0:
                cnt += 1
                members.append(T)
    return cnt, members

def fiber_space_basis(l0, u_class, D_def, q, w):
    """W = {m-hat deg<=w : exists g deg<=D_def, m-hat == u*g mod l0}.
       Basis: lifts of u*X^j mod l0 (j=0..D_def) extended by l0-multiples
       up to deg w: l0 * F[X]_{<= w - deg l0}."""
    w0 = max(i for i in range(len(l0)) if l0[i] % q)
    basis = []
    for j in range(D_def + 1):
        # u * X^j mod l0, lifted (degree < w0 <= w)
        xj = [0] * j + [1]
        prod = polmul(u_class, xj, q)
        basis.append(polmod(prod, l0, q))
    for j in range(w - w0 + 1):
        xj = [0] * j + [1]
        basis.append(polmul(l0, xj, q))
    return basis

random.seed(31)
for (q, n, w) in [(11, 10, 4), (13, 12, 4)]:
    D = order_subgroup(q, n)
    print(f"\n=== (q,n,w) = ({q},{n},{w}), D = mu_{n} ===")
    # genuine l0 pool (monic deg w, nonvanishing on D)
    pool = []
    while len(pool) < 200:
        l0 = [random.randrange(q) for _ in range(w)] + [1]
        if all(poleval(l0, x, q) for x in D):
            pool.append(l0)
    for D_def in (0, 1, 2):
        budget = (D_def + 1) + n // w
        mx = 0; arg = None
        for trial in range(120):
            l0 = random.choice(pool)
            u = [random.randrange(q) for _ in range(w)]  # class mod l0
            if all(c == 0 for c in u):
                continue
            basis = fiber_space_basis(l0, u, D_def, q, w)
            cnt, members = count_split_members(basis, q, n, w, D)
            if cnt > mx:
                mx = cnt; arg = (l0, u, members[:8])
        print(f"  D_def={D_def} (dim {D_def+2}): max split members over 120 fiber spaces"
              f" = {mx}   (conjecture <= {budget})")
        if arg and mx > 0:
            print(f"     l0={arg[0]}  members T: {arg[2]}")

    # adversarial: spaces SPANNED by split members + l0
    print(f"  --- adversarial spans (split-member generated + l0) ---")
    for d in (3, 4):
        mx = 0; arg = None
        for trial in range(2500):
            l0 = random.choice(pool)
            # pick d-1 random disjoint-ish w-subsets as generators
            gens = [m_of(sorted(random.sample(D, w)), q) for _ in range(d - 1)]
            basis = gens + [l0]
            if rank(basis, q, w + 1) != d:
                continue
            cnt, members = count_split_members(basis, q, n, w, D)
            if cnt > mx:
                mx = cnt; arg = (l0, members)
        budget = (d - 1) + n // w
        print(f"  dim {d}: max split members over 2500 adversarial spans = {mx}"
              f"  (conjecture <= {budget})")
        if arg and mx >= budget:
            print(f"     AT/OVER budget: l0={arg[0]}")
            print(f"     members: {arg[1]}")
