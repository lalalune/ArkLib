"""
PROBE (#444): independent exact recomputation of the energy ratio

    rho(r) := S_r / ((p-1) * E_r(C)),   S_r := sum_{t != 0} |eta_t|^{2r} = p*E_r(F_p) - n^{2r}

for the thin 2-power subgroup mu_n (n = 2^k) at beta ~ 4, to corroborate the empirical
anchor stated in Frontier/_OpenCoreRhoMonotone.lean ("rho(r) strictly decreasing, max at
r=1 where rho(1) = (p-n)/(p-1) < 1; rho falls 0.9998 -> 0.83 at n=16") and the PROVEN
Parseval base case rho_base_lt_one.

This is a SECOND, independent implementation:
  * mu_n <= F_p^* built with the campaign's exact find_prime/primitive_root/subgroup, so p
    (hence every integer) matches the campaign's choice -- not a parallel definition.
  * E_r(F_p) = #{(a,b) in mu_n^r x mu_n^r : sum a == sum b (mod p)} via mod-p convolution
    (exact Python ints). S_r = p*E_r(F_p) - n^{2r} is the orthogonality identity
    sum_t |eta_t|^{2r} = p*E_r(F_p), |eta_0|^{2r} = n^{2r}.
  * E_r(C) = char-0 additive energy of the n-th roots of unity, computed EXACTLY for n = 2^k
    via the cyclotomic basis: Phi_n(x) = x^{n/2}+1, so {1, z, ..., z^{n/2-1}} is a Q-basis;
    z^a reduces to a signed unit vector ( +e_{a} for a < n/2, -e_{a-n/2} for a >= n/2 ), and
    two multisets have equal complex sum IFF their reduced integer vectors are equal. So
    E_r(C) = sum_v (#r-tuples reducing to v)^2 -- convolution over reduced vectors, exact.
  * rho(r) kept as fractions.Fraction -> the monotone/<=1 verdicts are exact, never float.

NEVER fabricates: claims hold only for the (n, r) actually computed and reported.
"""
import sys, time
from collections import Counter
from fractions import Fraction

# ---- campaign helpers (copied verbatim from probe_rho_increment_bounded.py) ----
def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if m % q == 0: return m == q
    d = m-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a >= m: continue
        x = pow(a, d, m)
        if x == 1 or x == m-1: continue
        ok = False
        for _ in range(r-1):
            x = x*x % m
            if x == m-1: ok = True; break
        if not ok: return False
    return True

def find_prime(amax, beta):
    n = 2**amax
    target = int(n**beta)
    mod = 2**amax
    start = (target//mod)*mod + 1
    for k in range(0, 200000):
        for cand in (start + k*mod, start - k*mod):
            if cand > n and is_prime(cand):
                return cand
    return None

def primitive_root(p):
    fac = []; pm = p-1; d = 2
    while d*d <= pm:
        if pm % d == 0:
            fac.append(d)
            while pm % d == 0: pm //= d
        d += 1
    if pm > 1: fac.append(pm)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            return g
    return None

def subgroup(p, g, n):
    h = pow(g, (p-1)//n, p)
    S = []; cur = 1
    for _ in range(n):
        S.append(cur); cur = cur*h % p
    return S

# ---- exact energies ----
def dfac2(k):           # (2k-1)!!  (double factorial of the odd number)
    r = 1
    for i in range(1, 2*k, 2):
        r *= i
    return r

def Er_Fp(S, p, r):
    """E_r(F_p) = #{(a,b): sum a == sum b mod p}; = sum_v c_v^2 over residues v."""
    c = Counter({0: 1})
    for _ in range(r):
        nc = Counter()
        for v, m in c.items():
            for x in S:
                nc[(v + x) % p] += m
        c = nc
    return sum(m*m for m in c.values())

def Er_C_2power(n, r):
    """E_r(C) for the n-th roots of unity, n = 2^k, via cyclotomic antipodal reduction.
    Reduced vector lives in Z^{n/2}; z^a -> +e_a (a<n/2) or -e_{a-n/2} (a>=n/2)."""
    half = n // 2
    # single-element reduced vectors as (index, sign)
    units = []
    for a in range(n):
        if a < half: units.append((a, 1))
        else:        units.append((a - half, -1))
    c = Counter({tuple([0]*half): 1})
    for _ in range(r):
        nc = Counter()
        for v, m in c.items():
            for (idx, s) in units:
                w = list(v); w[idx] += s; nc[tuple(w)] += m
        c = nc
    return sum(m*m for m in c.values())

def Er_Fp_brute(S, p, r):
    """independent brute-force cross-check (small cases only)."""
    from itertools import product
    cnt = Counter()
    for tup in product(S, repeat=r):
        cnt[sum(tup) % p] += 1
    return sum(m*m for m in cnt.values())

def main():
    out = open("RESULTS-444-RHO-ANTITONE.md", "w")
    def emit(*a):
        line = " ".join(str(x) for x in a)
        print(line); sys.stdout.flush()
        out.write(line + "\n"); out.flush()

    emit("# Independent recompute of rho(r)=S_r/((p-1)E_r(C)) for mu_{2^k}, beta=4  (#444)")
    emit("# rho exact (Fraction); E_r(F_p) mod-p conv; E_r(C) cyclotomic antipodal reduction.\n")

    # per-n (r-cap, complex-side cap) chosen for sane runtime; reported honestly.
    plan = [(3, 12, 10), (4, 11, 10), (5, 6, 5)]   # (amax, rmax_Fp, rmax_C)
    BETA = 4.0
    overall_ok = True

    for amax, rmax_fp, rmax_c in plan:
        n = 2**amax
        p = find_prime(amax, BETA)
        g = primitive_root(p)
        S = subgroup(p, g, n)
        assert len(set(S)) == n, "subgroup not size n"
        beta_eff = (p.bit_length()-1) / amax  # approx log_n p
        emit(f"## n={n}  p={p}  (beta_eff~{beta_eff:.2f})  generator g={g}")

        # base-case cross-check: rho(1) should equal (p-n)/(p-1) exactly
        E1_fp = Er_Fp(S, p, 1)
        S1 = p*E1_fp - n**2
        E1_C = Er_C_2power(n, 1)
        rho1 = Fraction(S1, (p-1)*E1_C)
        rho1_parseval = Fraction(p - n, p - 1)
        base_ok = (rho1 == rho1_parseval) and (E1_fp == n) and (E1_C == n) and (S1 == p*n - n*n)
        emit(f"   base: E1(F_p)={E1_fp} (==n? {E1_fp==n}) E1(C)={E1_C} (==n? {E1_C==n}) "
             f"S1={S1} (==pn-n^2? {S1==p*n-n*n})")
        emit(f"   rho(1)={float(rho1):.6f}  Parseval (p-n)/(p-1)={float(rho1_parseval):.6f}  "
             f"EXACT MATCH={base_ok}")
        overall_ok &= base_ok

        # small-case brute-force cross-check of E_r(F_p)
        rcheck = 3 if n <= 8 else 2
        bf = Er_Fp_brute(S, p, rcheck); cv = Er_Fp(S, p, rcheck)
        emit(f"   brute-check E_{rcheck}(F_p): conv={cv} brute={bf} MATCH={cv==bf}")
        overall_ok &= (cv == bf)

        # compute rho(r) and E_r(C)/Wick (Lam-Leung leading -> (2r-1)!!)
        rhos = []
        rmax = max(rmax_fp, rmax_c)
        for r in range(1, rmax+1):
            t0 = time.time()
            Efp = Er_Fp(S, p, r)
            Sr = p*Efp - n**(2*r)
            if r <= rmax_c:
                EC = Er_C_2power(n, r)
                wick = dfac2(r) * n**r
                rho = Fraction(Sr, (p-1)*EC)
                rhos.append((r, rho))
                emit(f"   r={r}: S_r={Sr}  E_r(C)={EC}  E_r(C)/Wick={float(Fraction(EC,wick)):.4f}  "
                     f"rho={float(rho):.6f}  (<=1: {rho<=1})  [{time.time()-t0:.1f}s]")
            else:
                emit(f"   r={r}: S_r={Sr}  (E_r(C) beyond cap; rho skipped)  [{time.time()-t0:.1f}s]")

        # exact monotone + <=1 verdict over the computed rho's
        mono = all(rhos[i+1][1] <= rhos[i][1] for i in range(len(rhos)-1))
        le1  = all(r <= 1 for _, r in rhos)
        emit(f"   >> rho strictly-decreasing(exact)={all(rhos[i+1][1] < rhos[i][1] for i in range(len(rhos)-1))} "
             f"  antitone(<=)={mono}  all<=1={le1}  "
             f"rho range=[{float(rhos[-1][1]):.4f},{float(rhos[0][1]):.4f}]\n")
        overall_ok &= mono and le1

    emit(f"=== VERDICT: base-case+brute+monotone+<=1 all exact-confirmed = {overall_ok} ===")
    emit("Corroborates _OpenCoreRhoMonotone.lean in the COMPUTED regime only; the open core is")
    emit("rho(r+1)<=rho(r) for ALL r<=log p (the char-p excess = BGK/Paley wall), still open.")
    out.close()

if __name__ == "__main__":
    main()
