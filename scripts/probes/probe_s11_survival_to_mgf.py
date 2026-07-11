#!/usr/bin/env python3
"""
probe_s11_survival_to_mgf.py  (#444, S11 concentration — UN-TAKEN layer-cake half)

GOAL: find a FULLY DISCRETE, provable, TRUE-on-real-spectra inequality that turns the literal
spectral SURVIVAL tail  S(s) = #{b : t_b >= s} / P  into the MGF bound MGFBound (Sum_b exp(c t_b) <= A*P)
that _wfS11_layercake_moment.lean consumes.  No continuous layer-cake integral.

We test the ABEL / SUMMATION-BY-PARTS identity over the sorted distinct spectral values:
  let distinct sorted values  v_0 < v_1 < ... < v_K  (all >= 0),
  survival counts             N_j = #{b : t_b >= v_j}   (N_0 = P, decreasing),
  THEN exactly:
    Sum_b exp(c t_b) = Sum_j N_j * (exp(c v_j) - exp(c v_{j-1})),   v_{-1} := 0, but careful.

Actually the clean exact identity for a NONNEGATIVE spectrum and increasing g with g(0):
  Sum_b g(t_b) = g(v_0)*N_0  +  Sum_{j>=1} g(v_j)*(N_j' )   ... let's just verify the
  Abel form:  Sum_b g(t_b) = sum over level COUNTS  c_j = #{b: t_b = v_j},
              Sum_j c_j g(v_j),  and  c_j = N_j - N_{j+1}  (N_{K+1}=0).
  Summation by parts: Sum_j (N_j - N_{j+1}) g(v_j)
       = Sum_j N_j g(v_j) - Sum_j N_{j+1} g(v_j)
       = N_0 g(v_0) + Sum_{j>=1} N_j (g(v_j) - g(v_{j-1})).
  This IS exact. Verify numerically, then test the SURVIVAL-BOUND consequence:
  if N_j <= A * P * exp(-cc * v_j) for a rate cc > c, does Sum_b exp(c t_b) <= (something clean)*P ?
"""
import numpy as np
from sympy import primerange, isprime

def gauss_period_spectrum(p, n):
    """True normalized period spectrum t_b = |eta_b|^2 / n over the THIN subgroup mu_n < F_p^*.
    Proper subgroup only: requires n | p-1 and (p-1)/n >= 2. NEVER n=q-1."""
    assert (p - 1) % n == 0
    cof = (p - 1) // n
    assert cof >= 2, "must be PROPER subgroup"
    # primitive root
    def is_primroot(g):
        seen = set(); x = 1
        for _ in range(p-1):
            x = (x*g) % p; seen.add(x)
        return len(seen) == p-1
    g = 2
    while not is_primroot(g):
        g += 1
    # mu_n = <g^cof>
    h = pow(g, cof, p)
    H = []
    x = 1
    for _ in range(n):
        H.append(x); x = (x*h) % p
    H = np.array(H, dtype=np.int64)
    # eta_b = sum_{x in H} e_p(b x);  t_b = |eta_b|^2 / n  for b=1..p-1
    bs = np.arange(1, p)
    # phases
    ang = 2*np.pi/p
    # eta[b] = sum_x exp(i*ang*b*x)
    # build via outer product (small p)
    M = np.exp(1j*ang*np.outer(bs, H))   # (p-1, n)
    eta = M.sum(axis=1)
    t = (np.abs(eta)**2) / n
    return t  # length p-1

def abel_identity_check(t, c):
    """Verify Sum_b exp(c t_b) == N_0 g(v_0) + sum_{j>=1} N_j (g(v_j)-g(v_{j-1}))."""
    vals = np.sort(np.unique(np.round(t, 9)))
    g = lambda v: np.exp(c*v)
    # survival N_j = #{t_b >= v_j}
    N = np.array([np.sum(t >= v - 1e-9) for v in vals], dtype=float)
    direct = np.sum(np.exp(c*t))
    abel = N[0]*g(vals[0])
    for j in range(1, len(vals)):
        abel += N[j]*(g(vals[j]) - g(vals[j-1]))
    return direct, abel, vals, N

def survival_to_mgf(t, c):
    """If S(s)=N(s)/P <= A_surv * exp(-cc*s) for cc>c, what's the cleanest MGF ceiling?"""
    P = len(t)
    vals = np.sort(np.unique(np.round(t, 9)))
    N = np.array([np.sum(t >= v - 1e-9) for v in vals], dtype=float)
    S = N / P
    # best rate cc and constant for survival tail: A_surv = sup_s S(s) exp(cc s)
    return P, vals, S

if __name__ == "__main__":
    # prize-regime instances: n=2^a, proper subgroup, p > n^3, NEVER n=q-1
    cases = []
    for n in [4, 8, 16]:
        # find primes p with n | p-1, (p-1)/n>=2, p>n^3
        cnt = 0
        for p in primerange(max(50, n**3), n**3 + 5000):
            if (p-1) % n == 0 and (p-1)//n >= 2:
                cases.append((p, n)); cnt += 1
                if cnt >= 2: break
    # plus a structured Fermat-type
    if (257-1) % 16 == 0:
        cases.append((257, 16))

    print("=== ABEL IDENTITY (exact summation-by-parts) ===")
    for (p, n) in cases:
        t = gauss_period_spectrum(p, n)
        for c in [0.3, 0.5, 0.7]:
            direct, abel, vals, N = abel_identity_check(t, c)
            rel = abs(direct-abel)/max(abs(direct),1e-12)
            print(f"p={p:5d} n={n:3d} c={c:.2f}: direct={direct:.6f} abel={abel:.6f} rel_err={rel:.2e} {'OK' if rel<1e-8 else 'FAIL'}")

    print("\n=== SURVIVAL TAIL on true spectra (S(s) <= A_surv*exp(-cc*s)) ===")
    for (p, n) in cases:
        t = gauss_period_spectrum(p, n)
        P, vals, S = survival_to_mgf(t, 0.5)
        tmax = vals.max()
        # fit best (cc, A) so S(s)<=A exp(-cc s) for all sampled s, given cc; report A=sup S exp(cc s)
        for cc in [0.4, 0.6, 0.8, 1.0]:
            A = np.max(S * np.exp(cc*vals))
            print(f"p={p:5d} n={n:3d} cc={cc:.2f}: A_surv={A:.4f} tmax={tmax:.3f} S(0)={S[0]:.3f}")

    # === DOUBLE-COUNTING / layer-cake staircase identity (formalized as layercake_double_count) ===
    # Verify: with a threshold grid Theta and increments delta so the staircase equals the grid-g,
    #   sum_b [staircase_b] == sum_theta delta_theta * #{b: theta<=t_b}   (EXACT rearrangement)
    print("\n=== DOUBLE-COUNTING identity (layercake_double_count) ===")
    def double_count_check(t, c, ngrid=400):
        tmx = t.max()
        Theta = np.linspace(0, tmx, ngrid)
        g = np.exp(c*Theta)
        delta = np.empty_like(g); delta[0] = g[0]; delta[1:] = g[1:] - g[:-1]
        surv = np.array([np.sum(t >= th - 1e-12) for th in Theta], dtype=float)
        rhs = float(np.sum(delta * surv))
        lhs = 0.0
        for tb in t:
            lhs += float(np.sum(delta[Theta <= tb + 1e-12]))
        return lhs, rhs
    for (p, n) in cases:
        t = gauss_period_spectrum(p, n)
        for c in [0.4, 0.6]:
            lhs, rhs = double_count_check(t, c)
            rel = abs(lhs-rhs)/max(abs(lhs), 1e-12)
            print(f"p={p:5d} n={n:3d} c={c:.2f}: lhs={lhs:.4f} rhs={rhs:.4f} rel={rel:.2e} {'OK' if rel<1e-9 else 'FAIL'}")
