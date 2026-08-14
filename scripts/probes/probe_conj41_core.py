#!/usr/bin/env python3
"""
Conj 41 (Open-Set Rank Lemma) of ePrint 2026/858 — core computational attack (solo, main loop).
M_true(s) = # w-subsets E admitting a genuine weight-w error with syndrome s; the prize bound is
max_{s!=0} M_true(s) <= floor((2D-1)/c), D=n-k, w=D-c.
(1) Exact M_true/M_compat + reproduce the paper's anchor table (validation).
(2) Reproduce the small-p counterexamples (triangle p=113, tetrahedron p=61) + show they vanish at large p.
(3) Q-rank reduction: (s1,s2) with M_true=m <=> ker(A), A=stack[N_Ei | gamma_i N_Ei]; Conj41 <=>
    rank(A)=min(mc,2D) generically. Check generic rank at the critical m=ceil(2D/c).
"""
import itertools, functools
print = functools.partial(print, flush=True)

def matmod_rank(rows, p):
    """rank over F_p of a list of row-vectors (python ints)."""
    M = [r[:] for r in rows]; R = len(M); C = len(M[0]) if M else 0; rank = 0; pr = 0
    for c in range(C):
        piv = next((i for i in range(pr, R) if M[i][c] % p != 0), None)
        if piv is None: continue
        M[pr], M[piv] = M[piv], M[pr]
        inv = pow(M[pr][c] % p, p-2, p)
        M[pr] = [(x*inv) % p for x in M[pr]]
        for i in range(R):
            if i != pr and M[i][c] % p != 0:
                f = M[i][c] % p; M[i] = [(M[i][j]-f*M[pr][j]) % p for j in range(C)]
        pr += 1; rank += 1
        if pr == R: break
    return rank

def solve_unique(V, s, p):
    """solve V v = s over F_p (V is D x w, rank w expected); return v (len w) if unique consistent else None."""
    D = len(V); w = len(V[0])
    A = [V[i][:] + [s[i]] for i in range(D)]   # augmented D x (w+1)
    pr = 0; where = [-1]*w
    for c in range(w):
        piv = next((i for i in range(pr, D) if A[i][c] % p != 0), None)
        if piv is None: return None  # rank < w (V degenerate); skip
        A[pr], A[piv] = A[piv], A[pr]
        inv = pow(A[pr][c] % p, p-2, p)
        A[pr] = [(x*inv) % p for x in A[pr]]
        for i in range(D):
            if i != pr and A[i][c] % p != 0:
                f = A[i][c] % p; A[i] = [(A[i][j]-f*A[pr][j]) % p for j in range(w+1)]
        where[c] = pr; pr += 1
    # consistency: rows pr..D-1 must have 0 = rhs
    for i in range(pr, D):
        if A[i][w] % p != 0: return None
    v = [0]*w
    for c in range(w):
        v[c] = A[where[c]][w] % p
    return v

def vander(E, L, D, p):
    return [[pow(L[e], j, p) for e in E] for j in range(D)]  # D x w

def M_counts(n, k, p, L=None, exhaustive=True, sample=None, seed=0):
    D = n - k; c = None  # c = D - w, w chosen as D-... actually w is a parameter; here w = n-k-c? 
    # The paper's convention: w=D-c. We sweep over the natural w = error weight; caller passes via globals.
    raise NotImplementedError

def maxM(n, k, w, p, L=None):
    """exhaustive max over s!=0 of (M_compat, M_true). D=n-k, c=D-w."""
    D = n - k; c = D - w
    if L is None: L = list(range(n))
    assert len(set(L)) == n and p > max(L)
    subs = list(itertools.combinations(range(n), w))
    Vs = [vander(E, L, D, p) for E in subs]
    best_t = 0; best_c = 0; arg_t = None
    for s in itertools.product(range(p), repeat=D):
        if all(x == 0 for x in s): continue
        mc = 0; mt = 0
        for E, V in zip(subs, Vs):
            v = solve_unique(V, list(s), p)
            if v is not None:           # s in colspan(V_E)  => compatible
                mc += 1
                if all(x % p != 0 for x in v): mt += 1
        if mt > best_t: best_t = mt; arg_t = s
        if mc > best_c: best_c = mc
    return best_c, best_t, arg_t, D, c

print("=== (1) Reproduce paper anchor table (n,w,c) -> (maxM_compat, maxM_true) ===")
# (n, w, c, expected M_compat, expected M_true, p)
anchors = [
    (5,2,1,4,2,5), (5,2,1,4,2,7), (5,2,1,4,2,11),
    (6,3,1,10,4,7), (6,3,1,10,4,13),
    (7,3,1,15,5,7), (7,3,1,15,5,11),
    (8,3,1,21,6,11),
    (6,3,2,10,2,7), (8,3,2,21,2,11),
]
for (n,w,c,emc,emt,p) in anchors:
    k = n - (w+c)              # D=w+c, k=n-D
    mc, mt, arg, D, cc = maxM(n, k, w, p)
    bound = (2*D - 1)//c
    ok = (mc==emc and mt==emt)
    print(f"  n={n} w={w} c={c} k={k} D={D} p={p}: maxM_compat={mc}(exp {emc}) maxM_true={mt}(exp {emt}) "
          f"floor((2D-1)/c)={bound}  {'OK' if ok else 'MISMATCH!!'}  M_true<=bound: {mt<=bound}")
