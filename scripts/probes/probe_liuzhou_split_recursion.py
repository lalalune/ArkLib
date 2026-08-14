r"""F10 / Liu-Zhou subgroup-restriction eigenvalue recursion probe (#444).

The Cayley/Paley adjacency operator A_G with connection set G = mu_n is LINEAR in G, and the
eigenvalue at frequency b is eta_b(G) = sum_{x in G} e_p(b x). Splitting mu_n along its index-2
sublattice mu_n = mu_{n/2} cup zeta*mu_{n/2} (zeta a primitive n-th root that is NOT in mu_{n/2})
gives the EXACT additive split

    eta_b(mu_n) = eta_b(mu_{n/2}) + eta_b(zeta*mu_{n/2}).

Liu-Zhou (arXiv:1809.09829) lambda <= lambda2(Cay(Gamma_k, T cap Gamma_k)) + lambda2(Cay(Gamma, T\Gamma_k))
is, for this abelian/character-diagonal setting, exactly the TRIANGLE INEQUALITY on this split:

    M(mu_n) = max_{b!=0} |eta_b(mu_n)|
            = max_{b!=0} |eta_b(A) + eta_b(B)|
            <= max_{b!=0}|eta_b(A)| + max_{b!=0}|eta_b(B)|     (subadditive recursion)
            = M(A) + M(B),    A = mu_{n/2}, B = zeta*mu_{n/2}.

Note M(B) = M(zeta*mu_{n/2}): a dilation by zeta is a relabelling b -> zeta^{-1} b of the frequency
index, so max_{b!=0}|eta_b(zeta A)| = max_{b!=0}|eta_b(A)| = M(mu_{n/2}). Hence the recursion reads

    M(mu_n) <= 2 * M(mu_{n/2}).               (the dyadic doubling)

THE HONESTY QUESTION (rule 3): is this recursion thinness-essential or thickness-blind, and is it
TIGHT (= the FALSE doubling the N13 census flags, where the two half-sums phase-ALIGN at the worst b)
or LOSSY (a genuine subadditivity SAVING the census says the magnitude recursion drops)?

We measure, on PROPER thin subgroups (p >> n^3, NEVER n=q-1):
  - LHS  = M(mu_n)                            (max over b!=0)
  - RHS  = M(mu_{n/2}) + M(zeta*mu_{n/2})     (= 2 M(mu_{n/2}))
  - the SUBADDITIVITY GAP  RHS - LHS  (>= 0 by triangle ineq; tight <=> 0)
  - the worst-b ALIGNMENT  |eta_b(A)+eta_b(B)| / (|eta_b(A)|+|eta_b(B)|) at the b achieving LHS
    (== 1.0 exactly  <=>  the two half-sums are phase-aligned at the worst frequency).
"""
import cmath, math, time


def primitive_root(p):
    phi = p - 1
    facs = set()
    x = phi
    d = 2
    while d * d <= x:
        if x % d == 0:
            facs.add(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        facs.add(x)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in facs):
            return g
    return None


def eta(b, S, p):
    """eta_b(S) = sum_{x in S} e_p(b x)."""
    tp = 2.0 * math.pi / p
    acc = 0j
    for x in S:
        acc += cmath.exp(1j * tp * ((b * x) % p))
    return acc


def analyze(p, n):
    g = primitive_root(p)
    m = (p - 1) // n
    # mu_n = { g^{m k} } for k=0..n-1
    mu_n = [pow(g, (m * k) % (p - 1), p) for k in range(n)]
    # index-2 split: mu_{n/2} = squares within mu_n = { g^{2 m j} } ; zeta = g^m (prim n-th root)
    half = n // 2
    A = [pow(g, (2 * m * j) % (p - 1), p) for j in range(half)]   # mu_{n/2}
    zeta = pow(g, m, p)
    B = [(zeta * a) % p for a in A]                               # zeta * mu_{n/2}
    # sanity: A and B partition mu_n
    assert sorted(set(A) | set(B)) == sorted(set(mu_n)) and len(set(A)) + len(set(B)) == n

    # M over b!=0 for the three sets, and worst-b for mu_n
    best_lhs = -1.0
    best_b = None
    for b in range(1, p):
        v = abs(eta(b, mu_n, p))
        if v > best_lhs:
            best_lhs, best_b = v, b
    M_A = max(abs(eta(b, A, p)) for b in range(1, p))
    # M(B) by dilation equals M(A) but measure it directly to be honest
    M_B = max(abs(eta(b, B, p)) for b in range(1, p))
    rhs = M_A + M_B

    # alignment at the worst b for mu_n
    eA = eta(best_b, A, p)
    eB = eta(best_b, B, p)
    align = abs(eA + eB) / (abs(eA) + abs(eB)) if (abs(eA) + abs(eB)) > 0 else 0.0
    gap = rhs - best_lhs
    return dict(p=p, n=n, beta=math.log(p) / math.log(n),
                LHS=best_lhs, RHS=rhs, M_A=M_A, M_B=M_B, gap=gap,
                align=align, worst_b=best_b,
                exact_split_err=abs(eta(best_b, mu_n, p) - (eA + eB)))


def main():
    # PROPER thin subgroups only; p >> n^3 where feasible; multiple primes incl. Fermat-type.
    cases = [(257, 16), (769, 16), (1153, 16), (12289, 16), (40961, 16), (65537, 16),
             (12289, 32), (40961, 32), (65537, 32),
             (786433, 64), (1179649, 64)]
    hdr = (f"{'p':>9} {'n':>4} {'beta':>5} {'M(n)':>9} {'2M(n/2)':>9} {'gap':>9} "
           f"{'gap%':>7} {'align':>7} {'split_err':>10}")
    print(hdr, flush=True)
    rows = []
    for (p, n) in cases:
        if (p - 1) % n:
            continue
        t = time.time()
        r = analyze(p, n)
        dt = time.time() - t
        gp = 100.0 * r['gap'] / r['RHS'] if r['RHS'] else 0.0
        rows.append(r)
        print(f"{p:>9} {n:>4} {r['beta']:>5.2f} {r['LHS']:>9.3f} {r['RHS']:>9.3f} "
              f"{r['gap']:>9.3f} {gp:>6.2f}% {r['align']:>7.4f} {r['exact_split_err']:>10.2e}"
              f"   ({dt:.1f}s)", flush=True)

    # VERDICTS
    print("\n--- VERDICTS ---", flush=True)
    viol = [r for r in rows if r['gap'] < -1e-9]
    print(f"subadditivity M(n) <= 2M(n/2) violated: {len(viol)}/{len(rows)} "
          f"(expect 0 -- triangle inequality is a THEOREM)", flush=True)
    tight = [r for r in rows if abs(r['gap']) < 1e-6]
    print(f"recursion TIGHT (gap==0, the FALSE doubling, phases align at worst b): "
          f"{len(tight)}/{len(rows)}", flush=True)
    lossy = [r for r in rows if r['gap'] > 1e-6]
    print(f"recursion LOSSY (genuine subadditivity saving): {len(lossy)}/{len(rows)}", flush=True)
    if rows:
        mn_align = min(r['align'] for r in rows)
        mx_align = max(r['align'] for r in rows)
        print(f"worst-b alignment range: [{mn_align:.4f}, {mx_align:.4f}] "
              f"(1.0 => half-sums phase-aligned at worst b => recursion gives nothing)", flush=True)
        mx_err = max(r['exact_split_err'] for r in rows)
        print(f"max exact-split error eta_b(mu_n) - (eta_b(A)+eta_b(B)): {mx_err:.2e} "
              f"(==0 => the additive split is EXACT, the formalizable identity)", flush=True)


if __name__ == "__main__":
    main()
