#!/usr/bin/env python3
"""
probe_c21_genpos_affine_rank.py   (issue #444, conjecture C21 attack)

C21 claims: the worst-case far-line candidate LIST (the bad-alpha messages m_alpha
in RS[k] that delta-agree with x^a + alpha x^b) is AFFINELY INDEPENDENT in the
window interior, so mds_genpos_list_bound (the affinely-INDEPENDENT in-tree MDS
list bound) caps it at L < budget, pinning delta* past Johnson.

mds_genpos_list_bound's HYPOTHESIS is:
    hindep : LinearIndependent K (fun j => m_{j+1} - m_0)
i.e. the L difference functionals (messages-minus-base) are linearly independent.
The bound it then gives is (L+1)*a <= L*n + (k - L), i.e. for the LIST to have
size > L the family must be affinely DEPENDENT.

THE TEST.  For a far monomial pencil (a,b) over a PROPER subgroup mu_n (p prime,
p >> n^3, NEVER n=p-1), at a window-interior agreement threshold thr (rho*n < thr,
deep enough that the list is large), enumerate the bad-alpha candidate messages
m_alpha in RS[k] (deg < k polys, given by their k coefficient vectors), and compute
the AFFINE RANK of the family {m_alpha} =
    1 + dim span{ m_alpha - m_alpha0 : alpha in bad }.
C21 is TRUE only if affine_rank == list_size (affinely independent).
C21 FAILS if affine_rank < list_size (the family is affinely DEPENDENT) -- which
is exactly when mds_genpos_list_bound is VACUOUS and the open higher-order-MDS /
line-incidence case applies.

We report, per pencil and threshold in the interior:
    I = list size (# bad alpha)
    R = affine rank of the message family
    "AFF-DEP" flag when R < I  (mds_genpos_list_bound cannot cap the list)

If, in the deep interior, I is large (>> k, >> budget n) but R is small/capped at k
(forced: deg<k messages live in a k-dim space, so affine rank <= k), then the list
is MASSIVELY affinely dependent and C21's premise is false: the worst-case list is
NOT affinely independent.

HONESTY: exact over F_p, p >> n^3, mu_n proper subgroup.  Small n only (subset
enumeration). The k-dimensional cap on affine rank is the structural disproof; the
probe makes it concrete with witness counts.
"""
import itertools
from math import gcd, sqrt, ceil, floor
import math

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def prime_ge(lo, n):
    p = lo - (lo % n) + 1
    while not (is_prime(p) and (p-1) % n == 0): p += n
    return p

def find_gen(p, n):
    for g0 in range(2, p):
        w = pow(g0, (p-1)//n, p)
        if pow(w, n, p) == 1 and all(pow(w, n//q, p) != 1 for q in (2,3,5,7) if n % q == 0):
            return w
    raise RuntimeError

def inv(a, p): return pow(a % p, p-2, p)

def interp_coeffs(Xs, Ys, k, p):
    """Unique deg<k poly through k points (Xs,Ys); returns coeff vector length k, or None."""
    # Vandermonde solve (k x k)
    M = [[pow(Xs[r], c, p) for c in range(k)] + [Ys[r] % p] for r in range(k)]
    for c in range(k):
        piv = None
        for rr in range(c, k):
            if M[rr][c] % p != 0: piv = rr; break
        if piv is None: return None
        M[c], M[piv] = M[piv], M[c]
        iv = inv(M[c][c], p)
        M[c] = [(x*iv) % p for x in M[c]]
        for rr in range(k):
            if rr != c and M[rr][c] % p != 0:
                f = M[rr][c]; M[rr] = [(a - f*b) % p for a, b in zip(M[rr], M[c])]
    return [M[r][k] % p for r in range(k)]

def eval_poly(coeffs, x, p):
    t = 0
    for c in reversed(coeffs): t = (t*x + c) % p
    return t

def alpha_and_msg_for_subset(Tidx, X, a, b, p, k):
    """(k+1)-subset Tidx: find the unique alpha s.t. word y=X^a+alpha X^b is interpolable
    by a deg<k poly on those k+1 points, and return (alpha, message coeffs on those points)."""
    Xs = [X[j] for j in Tidx]; m = k+1
    # Build the k x (k+1) eval matrix of monomials 1..x^{k-1}; find its left-null (lambda)
    M = [[pow(Xs[c], i, p) for c in range(m)] for i in range(k)]
    rows = [r[:] for r in M]; pivots = []; r = 0
    for c in range(m):
        piv = None
        for rr in range(r, k):
            if rows[rr][c] % p != 0: piv = rr; break
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        iv = inv(rows[r][c], p); rows[r] = [(xx*iv) % p for xx in rows[r]]
        for rr in range(k):
            if rr != r and rows[rr][c] % p != 0:
                f = rows[rr][c]; rows[rr] = [(aa - f*bb) % p for aa, bb in zip(rows[rr], rows[r])]
        pivots.append(c); r += 1
    free = [c for c in range(m) if c not in pivots]
    if not free: return None
    fc = free[0]; lam = [0]*m; lam[fc] = 1
    for i, c in enumerate(pivots): lam[c] = (-rows[i][fc]) % p
    U = sum(lam[c]*pow(Xs[c], a, p) for c in range(m)) % p
    V = sum(lam[c]*pow(Xs[c], b, p) for c in range(m)) % p
    if V % p == 0: return None
    alpha = (-U*inv(V, p)) % p
    return alpha

def max_agree_and_best_msg(n, k, p, X, a, b, alpha):
    """exact max-agreement of y=X^a+alpha X^b with RS[k]; return (best_agree, best_msg_coeffs)."""
    y = [(pow(X[j], a, p) + alpha*pow(X[j], b, p)) % p for j in range(n)]
    best = 0; best_msg = None
    for comb in itertools.combinations(range(n), k):
        bx = [X[i] for i in comb]; by = [y[i] for i in comb]
        coeffs = interp_coeffs(bx, by, k, p)
        if coeffs is None: continue
        cnt = sum(1 for jx in range(n) if eval_poly(coeffs, X[jx], p) == y[jx])
        if cnt > best:
            best = cnt; best_msg = coeffs
    return best, best_msg

def affine_rank(msgs, p):
    """affine rank = 1 + dim span{m - m0}; msgs is list of coeff vectors (Fp^k)."""
    if not msgs: return 0
    base = msgs[0]
    diffs = [[(m[i]-base[i]) % p for i in range(len(base))] for m in msgs[1:]]
    # row-reduce diffs over Fp
    rows = [r[:] for r in diffs]; rank = 0; ncol = len(base); rr = 0
    for c in range(ncol):
        piv = None
        for i in range(rr, len(rows)):
            if rows[i][c] % p != 0: piv = i; break
        if piv is None: continue
        rows[rr], rows[piv] = rows[piv], rows[rr]
        iv = inv(rows[rr][c], p); rows[rr] = [(x*iv) % p for x in rows[rr]]
        for i in range(len(rows)):
            if i != rr and rows[i][c] % p != 0:
                f = rows[i][c]; rows[i] = [(a-f*b) % p for a, b in zip(rows[i], rows[rr])]
        rr += 1; rank += 1
    return 1 + rank

def main():
    print("C21 TEST: affine rank R of the worst-case bad-alpha message list vs list size I", flush=True)
    print("(C21 needs R==I = affinely INDEPENDENT; deg<k messages cap R<=k. Prize-faithful p>>n^3, mu_n proper.)", flush=True)
    for (n, k) in [(8, 2), (8, 4), (16, 4), (16, 2)]:
        if math.comb(n, k+1) > 3_000_000 or math.comb(n, k) > 3_000_000:
            print(f"\nn={n} k={k}: skip (subset enumeration too big)", flush=True); continue
        p = prime_ge(8*n**3, n); w = find_gen(p, n); X = [pow(w, j, p) for j in range(n)]
        rho = k/n; lo_ag = rho*n; hi_ag = sqrt(rho)*n
        thrs = [t for t in range(floor(lo_ag)+1, ceil(hi_ag)+1)]
        if not thrs: thrs = [ceil(hi_ag)]
        print(f"\nn={n} k={k} p={p} rho={rho:.3f} budget(n)={n} dimcap(k)={k}: window agr ({lo_ag:.2f},{hi_ag:.2f}], thrs={thrs}", flush=True)
        seen_d = set(); b = k
        for de in range(1, n):
            a = (b + de) % n
            if a < k or a == b: continue
            d = gcd((b-a) % n, n)
            if d in seen_d: continue
            seen_d.add(d)
            cand = set()
            for Tidx in itertools.combinations(range(n), k+1):
                al = alpha_and_msg_for_subset(Tidx, X, a, b, p, k)
                if al is not None: cand.add(al)
            results = {}
            for al in cand:
                ag, msg = max_agree_and_best_msg(n, k, p, X, a, b, al)
                results[al] = (ag, msg)
            line = f"  (a,b)=({a},{b}) gcd={d}: "
            for thr in thrs:
                bad = [al for al in cand if results[al][0] >= thr]
                msgs = [results[al][1] for al in bad if results[al][1] is not None]
                R = affine_rank(msgs, p)
                I = len(bad)
                flag = " AFF-DEP(C21-FALSE)" if (I > R and I > 0) else ""
                line += f"[thr{thr}:I={I},R={R}{flag}] "
            print(line, flush=True)
    print("\nVERDICT: wherever the deep-interior list is large (I >> k) the affine rank R is capped at k", flush=True)
    print("(deg<k messages live in a k-dim space), so I >> R: the worst-case list is MASSIVELY affinely", flush=True)
    print("DEPENDENT. mds_genpos_list_bound's hypothesis (affine independence) FAILS exactly where C21", flush=True)
    print("needs it. C21's premise 'worst-case far-line list is affinely independent' is REFUTED:", flush=True)
    print("the worst-case list is the affinely-DEPENDENT (line/higher-order-MDS) case -- the open core.", flush=True)

if __name__ == "__main__":
    main()
