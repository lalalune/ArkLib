import numpy as np
from math import log, sqrt, comb

# Thin 2-power subgroup mu_n in F_p.  n=2^mu, n | p-1.
# eigenvalues of Cay(F_p, mu_n): S_b = sum_{x in mu_n} e_p(b x).
# ESD = empirical dist of {S_b : b in F_p} (real-valued, since mu_n closed under negation when n even).
# Kesten-McKay (KM) degree d=n: support [-2 sqrt(n-1), 2 sqrt(n-1)], moments m_2k = sum over closed walks on n-regular tree.
# E_k(mu_n) = (1/p) sum_b |S_b|^{2k}  (the char-p energy, normalized).  Compare to KM 2k-th moment.

def km_moment(d, k):
    # 2k-th moment of Kesten-McKay degree d (return RAW, i.e. moment of eigenvalue, not normalized by d)
    # Closed walks of length 2k on infinite d-regular tree:
    # m_{2k} = sum_{j=0}^{k-1} (1/(j+1)) C(2k, ... )? Use known formula:
    # m_{2k} = sum_{i=0}^{k-1} d (d-1)^i * N(k,i) where N = Narayana-ish. Use direct recurrence via free convolution.
    # Easiest: moments of KM = those of free-prob: use the explicit:
    # m_{2k} = sum_{i=0}^{k-1} (1/(i+1)) C(2k, k-1-i) * ... -- instead simulate via tree walk counting.
    # Tree closed-walk count length L from root on d-regular tree:
    # f(L): number of closed walks length L starting at root.
    # recurrence: g_m = number of walks of length m that start at a node, end at root, never go above root (Dyck-like with d choices down, 1 up)
    # Standard: closed walks on d-reg tree length 2k = sum over Dyck paths, each down-step has (#available children) choices.
    # For tree rooted: first step d choices, subsequent down-steps (d-1) choices.
    # Number = sum over Dyck paths of length 2k of d^{?}... use:
    # C_{2k} = closed walks = sum_{Dyck path P} product over down-steps of (d if from root else d-1)
    # Compute via DP on (position, height).
    from functools import lru_cache
    @lru_cache(maxsize=None)
    def walks(steps_left, height):
        if steps_left == 0:
            return 1 if height == 0 else 0
        total = 0
        # down step (go to a child): increases height
        if True:
            branch = d if height == 0 else (d-1)
            total += branch * walks(steps_left-1, height+1)
        # up step (go to parent): only if height>0
        if height > 0:
            total += walks(steps_left-1, height-1)
        return total
    return walks(2*k, 0)

def gauss_periods(p, n):
    # mu_n = unique subgroup of order n in F_p^*.  Need a generator.
    # find generator g of F_p^* (primitive root), then mu_n = {g^{(p-1)/n * j)}}
    # use sympy-free: find primitive root by trial
    pm1 = p-1
    # factor pm1
    def factor(m):
        f=set(); d=2
        while d*d<=m:
            while m%d==0: f.add(d); m//=d
            d+=1
        if m>1: f.add(m)
        return f
    fs = factor(pm1)
    def is_prim(g):
        return all(pow(g, pm1//q, p)!=1 for q in fs)
    g=2
    while not is_prim(g): g+=1
    h = pow(g, pm1//n, p)  # generator of mu_n
    mu = [pow(h, j, p) for j in range(n)]
    mu = np.array(mu, dtype=np.float64)
    b = np.arange(1, p, dtype=np.float64)  # b != 0
    # S_b = sum_x exp(2pi i b x / p) ; real part suffices for |.|? compute complex
    ang = 2*np.pi*np.outer(b, mu)/p   # (p-1, n)
    S = np.cos(ang).sum(axis=1) + 1j*np.sin(ang).sum(axis=1)
    return np.abs(S)

# small primes p = n^beta-ish with n=2^mu, n|p-1
cases = []
# n=4
for n,p in [(4,13),(4,29),(4,53),(4,1013),(4,4001),
            (8,17),(8,73),(8,1129),(8,10169),
            (16,97),(16,1153),(16,65537),
            (32,193),(32,1217),(32,65921),
            (64,257),(64,65921),
            (128,769),(128,65921)]:
    if (p-1)%n!=0: continue
    absS = gauss_periods(p,n)
    M = absS.max()
    edge = 2*sqrt(n-1)
    bound = sqrt(n*log(p/n))  # the prize RHS (C=1)
    # moment-method estimate of edge at depth k:
    # M^{2k} <= sum_b |S_b|^{2k} = (p-1)*E_k_raw ... = p * (raw 2k-moment incl b=0? exclude)
    cases.append((n,p,M,edge,bound,M/edge,M/bound))

print(f"{'n':>4} {'p':>7} {'M(n)':>9} {'2sqrt(n-1)':>11} {'sqrt(nln(p/n))':>14} {'M/edge':>7} {'M/prize':>8}")
for n,p,M,edge,bound,r1,r2 in cases:
    print(f"{n:>4} {p:>7} {M:9.3f} {edge:11.3f} {bound:14.3f} {r1:7.3f} {r2:8.3f}")
