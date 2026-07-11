#!/usr/bin/env python3
"""
probe_wfT22_paley_degeneracy.py  (#444 candidate T22, G5-2)

REFUTATION of the determinantal-rigidity COUNT law for the generalized-Paley period family.

T22 conjectures that the normalized eigenvalue multiset X_n = {eta_b/sqrt(n) : b in F_p^*} of
C = Cay(F_p, mu_n) is, "after Gaussianization", a DETERMINANTAL point process with a
Christoffel-Darboux kernel, and that the exceedance COUNT N(t) = #{b!=0 : eta_b > t sqrt(n)}
has log-VARIANCE rigidity Var(N) <= c log(p/n) (sub-Poissonian repulsion).

This probe establishes the FATAL structural fact (Podesta-Videla, arXiv 2604.06513, 2026;
Liu-Zhou Thm 115): eta_b depends only on the cyclotomic coset b*mu_n, so

   {eta_b : b in F_p^*}  has exactly  k = (p-1)/n  DISTINCT values,
                         each with multiplicity EXACTLY n.

Consequence: N(t) is ALWAYS a multiple of n. The "point process" is n-fold atomic, i.e. the
MAXIMALLY NON-SIMPLE configuration. A determinantal point process with a CD projection kernel is
a.s. SIMPLE (Hough-Krishnapur-Peres-Virag), its kernel vanishing on the diagonal -- the exact
"-K(s,u)^2" repulsion T22 invokes. Repulsion is structurally impossible for an n-fold-degenerate
atom (rho_2 on the diagonal ~ n^2, opposite sign to a DPP's 0). So the determinantal hypothesis is
FALSE at the spectrum level (not "likely to fail"). => REFUTED.

Secondary: the only half of T22 that bounds the prize sup is the MEAN estimate
E[N(t)] <= m e^{-t^2/2}, which for the deterministic family is certified only via the energy
moments E_r through Markov -- i.e. MomentCountSupBound.forall_le_of_sum_pow_lt = fence F1. The
variance is inert for an upper bound on t_max (a smaller variance does NOT lower the largest t with
N(t) >= 1; only the mean/energy does). This probe also prints t_max and sqrt(2 log k) so the only
operative scale is visible.

Prize regime: n = 2^30, p = n^beta, beta = 4. Small primes below are exact stand-ins for the
coset/multiplicity structure, which is INDEPENDENT of size (it is the algebraic spectrum).
"""
import cmath, math
from collections import Counter


def primitive_root(p: int) -> int:
    phi = p - 1
    f, facs = phi, set()
    d = 2
    while d * d <= f:
        while f % d == 0:
            facs.add(d); f //= d
        d += 1
    if f > 1:
        facs.add(f)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in facs):
            return g
    raise RuntimeError("no primitive root")


def paley_periods(p: int, n: int):
    """Return the list of distinct Gaussian periods eta_i and a Counter of multiplicities
    over b in F_p^*, plus the normalized (real) period values sorted descending."""
    assert (p - 1) % n == 0, "n must divide p-1"
    g = primitive_root(p)
    k = (p - 1) // n
    gen = pow(g, k, p)
    mu = set()
    x = 1
    for _ in range(n):
        mu.add(x); x = (x * gen) % p
    assert len(mu) == n
    w = 2j * math.pi / p
    etas = {}
    for b in range(1, p):
        s = sum(cmath.exp(w * ((b * xx) % p)) for xx in mu)
        etas[b] = s
    rounded = [(round(v.real, 6), round(v.imag, 6)) for v in etas.values()]
    mult = Counter(rounded)
    distinct_vals = sorted(set(etas.values()), key=lambda z: -z.real)
    norm = [v.real / math.sqrt(n) for v in distinct_vals]
    return k, len(mult), set(mult.values()), norm


def main():
    print("=" * 78)
    print("T22 REFUTATION PROBE: Paley period multiset is n-fold degenerate (NOT a simple DPP)")
    print("=" * 78)
    cases = [(13, 3), (29, 7), (41, 8), (73, 8), (127, 7), (257, 16), (241, 8), (337, 16),
             (1297, 16), (3457, 27)]
    all_ok = True
    for p, n in cases:
        if (p - 1) % n:
            continue
        k, n_distinct, mults, norm = paley_periods(p, n)
        # The refutation: #distinct == k == (p-1)/n  AND every multiplicity == n
        ok_distinct = (n_distinct == k)
        ok_mult = (mults == {n})
        # N(t) is a multiple of n; it can never be 1 when n >= 2 -> not simple
        tmax = max(norm)
        scale = math.sqrt(2 * math.log(k)) if k > 1 else 0.0
        status = "OK" if (ok_distinct and ok_mult) else "MISMATCH"
        all_ok = all_ok and ok_distinct and ok_mult
        print(f"p={p:5d} n={n:3d} k=(p-1)/n={k:3d} | #distinct eta={n_distinct:3d} "
              f"mult set={sorted(mults)} | N(t) in n*Z (n={n}) => never 1 (NOT simple) "
              f"| t_max={tmax:.3f}  sqrt(2 log k)={scale:.3f}  [{status}]")
    print("-" * 78)
    if all_ok:
        print("VERDICT: every case has exactly k=(p-1)/n distinct periods, each multiplicity n.")
        print("  => exceedance count N(t) is ALWAYS a multiple of n; configuration is n-fold")
        print("     atomic; a Christoffel-Darboux DPP is a.s. SIMPLE => determinantal log-variance")
        print("     rigidity hypothesis is FALSE at the spectrum level. T22 REFUTED.")
        print("  => the only sup-bounding half is E[N(t)] (Markov on energy E_r) = fence F1;")
        print("     the variance bound is inert for the upper bound on t_max.")
    else:
        print("VERDICT: structural prediction FAILED on some case -- re-examine.")


if __name__ == "__main__":
    main()
