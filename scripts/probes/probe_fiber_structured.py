# The consumer uses supply only at w_γ = Q₀.eval + γ·xᵏ (structured u₀ = Q₀, a generated poly).
# Measure the actual per-γ fiber: #{coherent (k+m+1)-cores T of Q₀ with pinned scalar val(T)=γ}.
# val(T) = -(coreInterp_T Q₀).coeff k. If fibers are small, the effective supply is small.
from itertools import product, combinations
from math import comb
import random
def lagrange_interp_coeff(pts, vals, Fq, deg_k):
    # interpolate (pts,vals) by poly of degree < len(pts); return coeff at deg_k
    m = len(pts)
    # build via solving Vandermonde (small)
    # coeff vector c: sum c_j x^j = vals; solve
    import itertools
    # Gaussian elimination over F_q
    A = [[pow(pts[i], j, Fq) for j in range(m)] + [vals[i]] for i in range(m)]
    for col in range(m):
        piv = next(r for r in range(col, m) if A[r][col] % Fq != 0)
        A[col], A[piv] = A[piv], A[col]
        inv = pow(A[col][col], Fq-2, Fq)
        A[col] = [(x*inv) % Fq for x in A[col]]
        for r in range(m):
            if r != col and A[r][col] % Fq != 0:
                f = A[r][col]
                A[r] = [(A[r][t] - f*A[col][t]) % Fq for t in range(m+1)]
    return A[deg_k][m] % Fq if deg_k < m else 0

def is_coherent(pts, vals, Fq, k, m):
    # coreInterp coeffs k+1..k+m all zero
    sz=len(pts)
    A = [[pow(pts[i], j, Fq) for j in range(sz)] + [vals[i]] for i in range(sz)]
    for col in range(sz):
        piv = next(r for r in range(col, sz) if A[r][col] % Fq != 0)
        A[col], A[piv] = A[piv], A[col]
        inv = pow(A[col][col], Fq-2, Fq)
        A[col] = [(x*inv) % Fq for x in A[col]]
        for r in range(sz):
            if r != col and A[r][col] % Fq != 0:
                f = A[r][col]
                A[r] = [(A[r][t] - f*A[col][t]) % Fq for t in range(sz+1)]
    coeffs=[A[j][sz] % Fq for j in range(sz)]
    return all(coeffs[k+1+j]==0 for j in range(m)), (-coeffs[k] % Fq)

random.seed(23)
for (Fq,n,k,m) in [(11,8,2,1),(13,8,2,1),(11,9,2,1),(13,9,3,1)]:
    a=k+m+1
    if a>n: continue
    dom=list(range(1,n+1))
    # generated Q₀: random deg ≤ k+m poly
    maxfib=0; totcoh=0
    for _ in range(15):
        qc=[random.randrange(Fq) for _ in range(k+m+1)]
        Q0=[sum(qc[j]*pow(dom[i],j,Fq) for j in range(k+m+1))%Fq for i in range(n)]
        fibers={}
        for T in combinations(range(n),a):
            pts=[dom[i] for i in T]; vals=[Q0[i] for i in T]
            coh,g=is_coherent(pts,vals,Fq,k,m)
            if coh:
                fibers[g]=fibers.get(g,0)+1; totcoh+=1
        if fibers: maxfib=max(maxfib, max(fibers.values()))
    print(f"F{Fq} n{n} k{k} m{m} a{a}: max per-γ fiber = {maxfib}, "
          f"C(n,a)={comb(n,a)}, n²/(a²-nk)={n*n//(a*a-n*k) if a*a>n*k else 'shallow'}, "
          f"deep={'Y' if a*a>n*k else 'N'}")
