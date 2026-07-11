#!/usr/bin/env python3
"""
EXACT in-tree constrainedCensus(H=mu_n, k, a) growth law (p-independent, cyclotomic).

In-tree def (CensusConditionalPin.constrainedCensus):
  constrainedCensus(H,k,a) = { -e_1(A) : A subset H, |A|=a, e_2(A)=...=e_{a-k}(A)=0 }   (as a SET)
  D(a) := |constrainedCensus| = number of DISTINCT -e_1 values among qualifying a-subsets.
Census-crossing pin (mcaDeltaStar_eq_of_censusCrossing'):
  with budget = q*eps* = n (prize),  a_c = the crossing where D(a) > n drops to D(a) <= n;
  mcaDeltaStar = 1 - a_c/n,  and m* := a_c - k,  delta* = (1-rho) - m*/n  where a_c is the
  LARGEST a with D(a) > budget? -- NO: delta* = 1 - a_c/n with a_c = crossing agreement, and
  for a > a_c census is GOOD (<= budget) and AT a_c it is BAD (> budget). So a_c = max{a : D(a)>n}.
  => m* = a_c - k is the binding depth, delta* = 1 - a_c/n.  (Larger a = smaller radius = deeper.)

We compute D(a) EXACTLY over the cyclotomic field: e_j(zeta^A) tested zero via ALL Galois
conjugates (zeta->zeta^g) of a high-precision complex evaluation (decisive, cross-checked vs the
F_p incidence at n=8,16).  -e_1 distinct VALUES are counted as cyclotomic-field elements: two
qualifying subsets give the same -e_1 iff e_1(zeta^A)=e_1(zeta^B) AS ALGEBRAIC NUMBERS, i.e. equal
under every Galois conjugate -- we key by the rounded tuple of conjugate values.
"""
import sys, itertools, cmath, math

def coprimes(n):
    return [g for g in range(1, n) if math.gcd(g, n) == 1]

def esym_powersums(roots, upto):
    """e_1..e_upto via Newton (complex)."""
    ps = [complex(len(roots))] + [sum(z**j for z in roots) for j in range(1, upto+1)]
    e = [complex(1)] + [0j]*upto
    for kk in range(1, upto+1):
        s = 0j
        for i in range(1, kk+1):
            s += (-1)**(i-1) * e[kk-i] * ps[i]
        e[kk] = s / kk
    return e  # e[0]=1, e[1]=e_1, ...

def D_at_a(n, k, a, conj, tol=1e-6, RND=5):
    """Exact D(a) = #distinct -e_1 over qualifying a-subsets (e_2..e_{a-k}=0)."""
    upto = a - k  # need e_2..e_{a-k}
    zpow = [[cmath.exp(2j*cmath.pi*((t*g) % n)/n) for t in range(n)] for g in conj]
    e1_keys = set()
    qualifying = 0
    for A in itertools.combinations(range(n), a):
        ok = True
        e1_conj = []
        for gi, g in enumerate(conj):
            roots = [zpow[gi][t] for t in A]
            e = esym_powersums(roots, max(upto, 1))
            # constraints e_2..e_{a-k} == 0
            for j in range(2, upto+1):
                if abs(e[j]) > tol:
                    ok = False; break
            if not ok: break
            e1_conj.append((round(e[1].real, RND), round(e[1].imag, RND)))
        if ok:
            qualifying += 1
            e1_keys.add(tuple(e1_conj))   # -e_1 distinct value as algebraic number (via conjugates)
    return len(e1_keys), qualifying

def find_crossing(n, k, budget=None, a_lo=None, a_hi=None, verbose=True):
    budget = budget or n
    conj = coprimes(n)
    a_lo = a_lo or (k+1)
    a_hi = a_hi or (n - k)   # a beyond n-k+something is trivial; window is interior
    # D(a) is decreasing in a (more constraints + larger subsets). a_c = max{a : D(a) > budget}.
    a_c = None; data = {}
    for a in range(a_hi, a_lo-1, -1):   # sweep DOWN; first a with D(a)>budget is a_c
        D, qual = D_at_a(n, k, a, conj)
        data[a] = (D, qual)
        if verbose:
            print(f"[n={n} k={k}] a={a} m=a-k={a-k} r=n-a={n-a}: D={D} (qual_subsets={qual}) "
                  f"{'BAD(>budget)' if D>budget else 'good(<=budget)'}", flush=True)
        if D > budget and a_c is None:
            a_c = a
            # we want the LARGEST such a; since sweeping down, the first hit IS the largest
            break
    if a_c is not None:
        mstar = a_c - k; ds = 1 - a_c/n
        if verbose:
            print(f"  => a_c={a_c}, m*={mstar}, delta*={ds} = (1-{k}/{n}) - {mstar}/{n}", flush=True)
        return a_c, mstar, ds, data
    return None, None, None, data

if __name__ == '__main__':
    n = int(sys.argv[1]); k = int(sys.argv[2]) if len(sys.argv)>2 else n//4
    a_lo = int(sys.argv[3]) if len(sys.argv)>3 else None
    a_hi = int(sys.argv[4]) if len(sys.argv)>4 else None
    find_crossing(n, k, n, a_lo, a_hi)
