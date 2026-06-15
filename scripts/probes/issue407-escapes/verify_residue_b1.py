"""
Verify the lean-sharpen brick's numeric claims about the residue-degree object.

Brick claim (2): general realizable prize-shape S = core ∪ stragglers, worst residue degree
by realized k is k=1->0, k=2->2, k=4->1; the k=2 residue=2 case (roots [0,5,10,13],
support {0,1,3,4}) shows residue CAN equal k, so deg d < k is NOT unconditional.

We test: given an agreement set S in mu_n that is the root set of a (k+2)-sparse poly,
decompose Q_S = (maximal mu_g coset-core) * (residue d). What is deg(d), and is it
< k or = k or even larger? Does deg(d) track sparsity (k+2) or degree?

We work over C with mu_n = n-th roots of unity. We test the brick's specific exhibited
example AND search for the worst-case residue degree at the prize-shape directions.
"""
import numpy as np
import itertools
from numpy.polynomial import polynomial as P

def roots_of_unity(n):
    return np.exp(2j*np.pi*np.arange(n)/n)

def poly_from_roots(rootset):
    # monic poly with given roots
    p = np.poly(rootset)  # highest-degree first
    return p

def support_of_poly_coeffs(coeffs, tol=1e-7):
    # coeffs highest->lowest from np.poly; return set of EXPONENTS with nonzero coeff
    deg = len(coeffs)-1
    supp = set()
    for i,c in enumerate(coeffs):
        e = deg - i
        if abs(c) > tol:
            supp.add(e)
    return supp

def maximal_coset_granularity(S_exps, n):
    """Given root set as a set of exponent-indices (roots = omega^e), find the largest g|n
    such that S is a union of mu_g cosets, i.e. S is invariant under e -> e + n/g (mod n).
    Returns g (1 if fully ragged)."""
    Sset = set(S_exps)
    best = 1
    for g in range(2, n+1):
        if n % g != 0:
            continue
        step = n//g  # mu_g = {omega^{step*j}}; coset of e is {e + step*j mod n}
        # S invariant under +step?
        if all(((e+step)%n) in Sset for e in Sset):
            best = max(best, g)
    return best

def residue_degree(S_exps, n):
    """deg of the residue after stripping the maximal coset core.
    coset core size = (|S| // g) * g if S is exactly a union... but in general S may be
    (coset-union of size g*c) + ragged stragglers. We define residue = |S| - g*c where
    g*c = largest coset-union subset. We approximate by: g = max granularity of WHOLE S
    only works if all of S is one granularity. For mixed, find largest g-coset-union subset."""
    Sset = set(S_exps)
    n_S = len(Sset)
    # find max coset-union subset over all divisors g>1: subset closed under +n/g
    best_core = 0
    best_g = 1
    for g in range(2, n+1):
        if n % g != 0: continue
        step = n//g
        # orbits under +step
        seen = set()
        core = 0
        for e in Sset:
            if e in seen: continue
            orbit = set()
            x = e
            for _ in range(g):
                orbit.add(x)
                x = (x+step)%n
            seen |= orbit
            if orbit <= Sset:  # whole coset is in S
                core += len(orbit)
        if core > best_core:
            best_core = core
            best_g = g
    residue = n_S - best_core
    return residue, best_core, best_g

# ---- Test the brick's exhibited example: roots [0,5,10,13] over mu_16 ----
n = 16
ex = [0,5,10,13]
roots = roots_of_unity(n)[ex]
coeffs = poly_from_roots(roots)
supp = support_of_poly_coeffs(coeffs)
res, core, g = residue_degree(ex, n)
print(f"Brick example roots(exps)={ex} over mu_{n}: support={sorted(supp)} (#terms={len(supp)}), "
      f"residue_deg={res}, core={core}, g={best_g if (best_g:=g) else 1}")

# ---- Now the central correctness question: does residue track SPARSITY or DEGREE? ----
# Build genuine far prize-shape agreement sets and measure residue vs (k+2) and vs |S|.
# An agreement set of x^a + gamma x^b - c(x) (deg c < k): we enumerate small ones.

def agreement_set(n, a, b, gamma, c_coeffs, tol=1e-6):
    """c_coeffs: list of length k giving c(x)=sum c_j x^j. Return exps e in [0,n) where
    omega^{ea} + gamma omega^{eb} - c(omega^e) = 0."""
    om = roots_of_unity(n)
    S = []
    for e in range(n):
        x = om[e]
        val = x**a + gamma*(x**b) - sum(c_coeffs[j]*x**j for j in range(len(c_coeffs)))
        if abs(val) < tol:
            S.append(e)
    return S

print("\n--- Residue vs sparsity sweep over genuine far directions (n=16,32) ---")
print("We look for the WORST residue degree (max over choices) for fixed k, varying n.")
for n in [16, 32, 64]:
    om = roots_of_unity(n)
    for k in [2, 3, 4]:
        worst_res = -1
        worst_info = None
        # sweep directions a>b with d=gcd(a-b,n) >= 2 (genuinely imprimitive far), small samples of c
        rng = np.random.default_rng(0)
        trials = 0
        for a in range(k, n):
            for b in range(k, a):
                d = np.gcd(a-b, n)
                if d < 2:  # require imprimitive (genuinely ragged) direction
                    continue
                # try a handful of gamma, c that produce a large agreement set
                for _ in range(40):
                    gamma = np.exp(2j*np.pi*rng.random())
                    # pick c to interpolate the line at some chosen points to force big agreement
                    # simpler: random small c
                    c_coeffs = [np.exp(2j*np.pi*rng.random()) for _ in range(k)]
                    S = agreement_set(n, a, b, gamma, c_coeffs)
                    trials += 1
                    if len(S) < 2: continue
                    res, core, g = residue_degree(S, n)
                    if res > worst_res:
                        worst_res = res
                        worst_info = (a,b,d,len(S),core,g)
        print(f" n={n} k={k}: worst residue_deg={worst_res}  (k+2={k+2})  info(a,b,d,|S|,core,g)={worst_info}")
