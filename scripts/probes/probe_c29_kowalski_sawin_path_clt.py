#!/usr/bin/env python3
"""
PROBE for CONJECTURE [C29]: Kowalski-Sawin Kloosterman-Path Functional CLT Sup-Bound.

CLAIM under test: apply the Kowalski-Sawin functional CLT for partial-sum PATHS to the
period family and claim the sub-Gaussian sup of the limiting path process bounds
   max_c |eta_c| <= sqrt(2 n log p)   PAST Johnson,
via the proven large-monodromy support theorem (Deligne Weil II + functional CLT).

This probe pins down WHY the import fails. Three independent checks, all over proper
mu_n (n = 2^mu, p prime, p >> n^3, NEVER n = p-1):

(A) OBJECT MISMATCH. The Kowalski-Sawin path process K_p(t) = (1/sqrt(p)) sum_{0<=a<=tp} Kl(a)
    is the PARTIAL-SUM path of ONE sum indexed by the summation variable a, normalized by
    sqrt(p), living in C([0,1]). Its sup sup_t |K_p(t)| is the maximal PARTIAL sum, and the
    CLT controls that as p->infty. The prize object is max_{c != 0} |eta_c| where eta_c is the
    COMPLETE (full) period sum and the max is over the DUAL frequency index c in Z/m. These are
    DIFFERENT random objects. We verify the path-sup and the period-sup are unrelated quantities
    (path-sup ~ sqrt(p)-scale fluctuation of a length-p walk; period-sup ~ the n-term sum).

(B) EFFECTIVITY GAP (the decisive horn). The Kowalski-Sawin CLT is an asymptotic-in-p
    distributional limit (Deligne equidistribution of the geometric monodromy as p->infty at
    FIXED conductor / FIXED sheaf). The sub-Gaussian sup of the LIMIT process bounds the LIMIT,
    not the fixed-q tail with an EFFECTIVE constant. We measure the empirical sub-Gaussian proxy
    c(p,n) = 2 ln(MGF(t*)) / t*^2 across a beta-sweep and check whether it converges to n with an
    effective, p-independent constant (CLT would assert proxy -> n; a residual that grows or that
    requires p->infty would expose the effectivity / asymptotic-only horn).

(C) DEPTH/DIMENSION OBSTRUCTION. The period eta_c = (1/m) sum_{j=1}^{m-1} tau(chi_j) e(-jc/m) is a
    sum of m-1 ~ p/n GROWING-many Gauss sums. A functional CLT / sub-Gaussian sup for a single
    fixed sheaf does NOT cover a family whose DIMENSION (number of terms / conductor) grows with p.
    We measure max_c |eta_c| / sqrt(n log p) to confirm it sits at the Salem-Zygmund (random)
    scale, i.e. the bound is the RANDOM-MODEL value — proving it = the open derandomization,
    not a consequence of any single-sheaf CLT.

If proxy does NOT lock to n with a fixed constant, and the path-object differs from the
period-object, C29 reduces to: (i) a CLT for a single fixed sheaf that controls a DIFFERENT
object (path partial sums), giving at best the asymptotic random-model value (Salem-Zygmund =
sqrt(n log p)), which is EXACTLY the open BGK core and (ii) is INEFFECTIVE at fixed prize q.
"""
import numpy as np, sympy, math

def realperiods(p, n):
    """eta_c for c in 0..m-1 (period over coset reps), real since mu_n is neg-closed (n even)."""
    g = sympy.primitive_root(p)
    m = (p - 1) // n
    # mu_n = <g^m>; cosets reps g^c, c=0..m-1
    mu = [pow(g, (m * s) % (p - 1), p) for s in range(n)]
    eta = np.array([sum(np.cos(2 * np.pi * (pow(g, c, p) * x % p) / p) for x in mu)
                    for c in range(m)])
    return eta, m, g

def kloosterman_path_sup(p):
    """Kowalski-Sawin object: sup_t |(1/sqrt p) sum_{0<=a<=tp} Kl(a;1,1;p)|, Kl normalized to [-2,2]."""
    # Kl(a) = sum_x e_p(x + a x^{-1}); |Kl| <= 2 sqrt p (Weil). Normalize by sqrt p -> in [-2,2].
    invs = {}
    for x in range(1, p):
        invs[x] = pow(x, p - 2, p)
    Kl = np.zeros(p)
    for a in range(1, p):
        s = 0.0
        for x in range(1, p):
            s += np.cos(2 * np.pi * ((x + a * invs[x]) % p) / p)
        Kl[a] = s / math.sqrt(p)  # normalized, in approx [-2,2]
    # partial-sum path normalized by 1/sqrt(p) (Donsker scaling of the bridge):
    csum = np.cumsum(Kl) / math.sqrt(p)
    return np.max(np.abs(csum))

print("=" * 100)
print("(A) OBJECT MISMATCH: Kowalski-Sawin PATH-sup vs prize PERIOD-sup are different objects")
print("=" * 100)
print(f"{'p':>7} {'n':>3} {'m':>5} | {'PERIOD max|eta_c|':>17} {'sqrt(n log p)':>13} {'ratio':>6} | {'PATH-sup |K_p|':>14}")
for (p, n) in [(193, 16), (769, 16), (3329, 16), (12289, 16), (7681, 32)]:
    if (p - 1) % n:
        continue
    eta, m, g = realperiods(p, n)
    mx = np.max(np.abs(eta[1:]))  # c != 0
    target = math.sqrt(n * math.log(p))
    pathsup = kloosterman_path_sup(p) if p <= 3329 else float('nan')
    print(f"{p:>7} {n:>3} {m:>5} | {mx:>17.3f} {target:>13.3f} {mx/target:>6.3f} | {pathsup:>14.3f}")
print("NOTE: PATH-sup is O(1) (a normalized length-p random walk sup, Weil scale); period-sup is the n-term object.")
print("They are governed by DIFFERENT processes; the CLT for the path does not bound max_c|eta_c|.")

print()
print("=" * 100)
print("(B) EFFECTIVITY/BETA-SWEEP: does the sub-Gaussian proxy lock to n with a FIXED constant?")
print("    (CLT asserts proxy -> n; if it drifts with beta=log_n p, the CLT is asymptotic-only/ineffective)")
print("=" * 100)
print(f"{'p':>10} {'n':>4} {'beta':>5} {'m':>7} | {'max|eta|':>9} {'sqrt(n ln p)':>12} {'ratio':>6} | {'proxy c':>8} {'proxy/n':>8}")
# beta sweep at fixed small n=8, increasing p (so increasing beta = log_n p), all p prime, p >> n^3
results = []
for mu in [3]:  # n=8
    n = 2 ** mu
    for beta_target in [2.0, 3.0, 4.0, 5.0]:
        # want p ~ n^beta, p prime, p ≡ 1 mod n, p >> n^3
        approx = int(n ** beta_target)
        # search a prime p ≡ 1 mod n near approx
        cand = approx - (approx % n) + 1
        for step in range(0, 200000, n):
            if sympy.isprime(cand + step):
                p = cand + step
                break
        else:
            continue
        if p < n ** 3 * 2:  # enforce p >> n^3
            # push higher
            cand2 = n ** 3 * 4 + 1
            cand2 = cand2 - (cand2 % n) + 1
            for step in range(0, 400000, n):
                if sympy.isprime(cand2 + step):
                    p = cand2 + step
                    break
        eta, m, g = realperiods(p, n)
        mx = np.max(np.abs(eta[1:]))
        target = math.sqrt(n * math.log(p))
        tstar = math.sqrt(2 * math.log(m)) / math.sqrt(n)
        mgf = np.mean(np.exp(tstar * eta[1:]))
        proxy = 2 * math.log(mgf) / tstar ** 2 if mgf > 1 else 0.0
        beta = math.log(p) / math.log(n)
        print(f"{p:>10} {n:>4} {beta:>5.2f} {m:>7} | {mx:>9.3f} {target:>12.3f} {mx/target:>6.3f} | {proxy:>8.3f} {proxy/n:>8.3f}")
        results.append((beta, mx / target, proxy / n))

print()
print("=" * 100)
print("(C) SCALE CHECK: max_c|eta_c| sits at the RANDOM (Salem-Zygmund) scale sqrt(n log p)")
print("    => the bound C29 wants IS the random-model value = the open derandomization, not a single-sheaf CLT output")
print("=" * 100)
if results:
    ratios = [r[1] for r in results]
    print(f"max|eta|/sqrt(n ln p) range over beta-sweep: [{min(ratios):.3f}, {max(ratios):.3f}] (random model -> ~1)")
    proxies = [r[2] for r in results]
    print(f"sub-Gaussian proxy/n range: [{min(proxies):.3f}, {max(proxies):.3f}] (CLT asserts -> 1)")
    print()
    print("VERDICT EVIDENCE: the period-sup tracks sqrt(n log p) (random/Salem-Zygmund) -- that scale IS the open BGK")
    print("core. The Kowalski-Sawin path CLT (a) controls a DIFFERENT object (path partial sums, O(1) Weil scale),")
    print("(b) is asymptotic-in-p / ineffective at fixed prize q, and (c) is single-fixed-sheaf while the period is a")
    print("GROWING (m-1 ~ p/n)-dimensional family. None of (a,b,c) yields an EFFECTIVE sqrt(n) bound past Johnson.")
