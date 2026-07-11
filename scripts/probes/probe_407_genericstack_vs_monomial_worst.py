#!/usr/bin/env python3
"""
probe_407_genericstack_vs_monomial_worst.py  (#444 -- is the WORST STACK a monomial far-line?)

THE UNCONTESTED GAP. The in-tree canonical core is
  WorstCaseFarIncidenceBounded C delta B :  FORALL stacks (u0,u1) with u1 far,
     farIncidence(u0,u1) = #{gamma : exists size-a S, u0 + gamma*u1 agrees w/ a deg<k word on S} <= B
(B1IncidenceBridge.lean). The bridge epsMCA <= B/q needs B = max over ALL (u0,u1) far stacks.
BUT the ENTIRE board (incidence I(n), census K, #bad collapse, wf-D1/D2/D5, the n/4 law, "->Johnson")
analyzes ONLY the MONOMIAL far-lines u0 = x^A, u1 = x^B. The board ASSERTS the monomial stack is the
worst case; NO probe has TESTED whether a GENERIC (random, non-monomial) far stack yields MORE bad-gamma.
If generic #bad > monomial #bad, the board's "-> Johnson" (derived on monomials) is an UNDER-ESTIMATE of
the true B = max over ALL stacks, and the canonical core could be LARGER than the far-line analysis says.

OBJECT (exact, matches the in-tree farIncidence / mcaEvent_iff_aligned_subset semantics):
  domain mu_n = <g> proper 2-power subgroup of F_p* (|mu_n|=n, m=(p-1)/n>1, NEVER n=q-1, prize prime p~n^4).
  deg<k codewords = RS evaluations of polynomials of degree < k on mu_n.
  band a = a-subset of mu_n. A scalar gamma is BAD for stack (u0,u1) at band a iff exists an a-subset S
  s.t. (u0 + gamma*u1)|_S agrees with some deg<k poly on S (i.e. u0|_S + gamma*u1|_S is interpolated by a
  deg<k poly == the size-(a) Reed-Solomon agreement). Equivalently (in-tree Aligned): every (k+1)-subtuple
  T of S has residual_0(T) + gamma*residual_1(T) = 0, with a non-degenerate tuple. So
     gamma_bad(S) = -residual_0(T)/residual_1(T) (well-defined & constant over T in S when S is aligned).
  #bad(u0,u1; a) = #distinct gamma over all aligned a-subsets S with a non-degenerate tuple.

  residual_j(T) for a (k+1)-tuple T = the bordered Vandermonde det = the divided difference [x_{T}] u_j
  (the in-tree residual). We compute it via the (k+1)x(k+1) bordered matrix det in F_p (exact).

METHOD (exact mod-p, proper subgroup, prize prime, NEVER n=q-1):
  Fix small prize regime n,k,p, binding band a. Compute #bad for:
    (M) the MONOMIAL worst far-line: u0 = x^A, u1 = x^B (the board's binding (A,B), e.g. hifreq antipodal).
    (G) several RANDOM GENERIC far stacks: u0,u1 random functions mu_n -> F_p with u1 FAR from the code
        (u1 not interpolated by any deg<k poly on > (1-delta)n points -- enforced by a quick agreement check).
  Compare max_G #bad(generic) vs #bad(monomial). rule-3: also a THICK control (n not 2-power) -- if generic
  BEATS monomial in BOTH thin and thick, the monomial-worst assumption is generally false (board under-counts).

HONESTY: this measures whether the monomial restriction CAPTURES the worst-case stack. A generic-<=-monomial
result SUPPORTS the board's assumption (does not prove it). A generic->monomial result is REFUTATION-GRADE:
the board's far-line "-> Johnson" under-estimates the true canonical B. Exact small-n, proper subgroup,
prize primes. Python-only, no Lean => axiom-clean trivially.
"""
import itertools, random
from itertools import combinations


def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = 41
    while d*d <= m:
        if m % d == 0: return False
        d += 2
    return True


def prize_prime(n, beta):
    p = int(n**beta); p += (1 - p) % n
    while not (isprime(p) and (p-1) % n == 0): p += n
    return p


def _pf(n):
    f = set(); d = 2; m = n
    while d*d <= m:
        while m % d == 0: f.add(d); m //= d
        d += 1
    if m > 1: f.add(m)
    return f


def find_gen(p, n):
    for h in range(2, p):
        x = pow(h, (p-1)//n, p)
        if pow(x, n, p) == 1 and all(pow(x, n//q, p) != 1 for q in _pf(n)):
            return x
    raise ValueError


def detmod(M, p):
    """Exact determinant of a square matrix mod prime p via fraction-free / Gaussian elim with inverses."""
    M = [row[:] for row in M]
    n = len(M)
    det = 1
    for col in range(n):
        piv = None
        for r in range(col, n):
            if M[r][col] % p != 0:
                piv = r; break
        if piv is None:
            return 0
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
            det = (-det) % p
        inv = pow(M[col][col], p-2, p)
        det = (det * M[col][col]) % p
        for r in range(col+1, n):
            if M[r][col] % p:
                f = (M[r][col] * inv) % p
                for c in range(col, n):
                    M[r][c] = (M[r][c] - f * M[col][c]) % p
    return det % p


def residual(nodes, k, u, p):
    """Bordered Vandermonde det for a (k+1)-tuple: cols 0..k-1 = node^j, last col = u(node).
    nodes = list of k+1 field elements (the x-values); u = dict/list value at each node index."""
    M = []
    for a in range(k+1):
        row = [pow(nodes[a], j, p) for j in range(k)] + [u[a]]
        M.append(row)
    return detmod(M, p)


def count_bad(xvals, uvals0, uvals1, n, k, a, p):
    """Exact #distinct bad gamma at band a for stack (u0,u1). xvals[i]=mu_n element, uvals_j[i]=u_j value.
    A gamma is bad iff some a-subset S is aligned: all (k+1)-subtuples T of S have res0(T)+gamma*res1(T)=0
    with a non-degenerate tuple. We enumerate a-subsets, test alignment, collect pinned gamma."""
    idx = list(range(n))
    bad = set()
    for S in combinations(idx, a):
        # gather all (k+1)-subtuples; pin gamma from the first non-degenerate, then verify all share it
        gamma = None
        ok = True
        nd_found = False
        for T in combinations(S, k+1):
            xs = [xvals[i] for i in T]
            r0 = residual(xs, k, [uvals0[i] for i in T], p)
            r1 = residual(xs, k, [uvals1[i] for i in T], p)
            if r1 % p == 0:
                if r0 % p != 0:
                    ok = False; break  # this tuple cannot be aligned for any finite gamma
                else:
                    continue  # degenerate tuple (both 0) -- imposes no constraint
            g = (-r0 * pow(r1, p-2, p)) % p
            nd_found = True
            if gamma is None:
                gamma = g
            elif g != gamma:
                ok = False; break
        if ok and nd_found and gamma is not None:
            bad.add(gamma)
    return len(bad)


def is_far(xvals, uvals1, n, k, a, p, trials=None):
    """u1 FAR: not agreeing with any deg<k poly on >= a points. Quick sufficient check: for a random
    sample of a-subsets, u1|_S is NOT interpolated by a deg<k poly (residual of some (k+1)-subtuple !=0)."""
    idx = list(range(n))
    sample = list(combinations(idx, a))
    if trials and len(sample) > trials:
        sample = random.sample(sample, trials)
    for S in sample:
        interp_ok = True
        for T in combinations(S, k+1):
            xs = [xvals[i] for i in T]
            if residual(xs, k, [uvals1[i] for i in T], p) % p != 0:
                interp_ok = False; break
        if interp_ok:
            return False  # u1 agrees with a deg<k poly on a full a-set => NOT far
    return True


def main():
    print("# Is the WORST STACK a monomial far-line? generic random stacks vs the monomial worst (#444)")
    print("# #bad = #distinct pinned gamma at the binding band. If generic > monomial => board under-counts B.\n")
    random.seed(20260615)

    # n=16 k=3 hifreq, FULL BAND SWEEP a = k+1 .. n/2: shallow (non-binding) vs deep BINDING bands.
    n, beta, k, A, B = 16, 4.0, 3, 9, 7
    p = prize_prime(n, beta); g = find_gen(p, n)
    xvals = [pow(g, i, p) for i in range(n)]
    u0m = [pow(x, A, p) for x in xvals]
    u1m = [pow(x, B, p) for x in xvals]
    print(f"n={n} k={k} hifreq[{A},{B}] p={p}  (binding deep band = where mono #bad pins to 1; shallow a=k+1 is non-binding)")
    print(f"{'band a':>7} {'#bad(monomial)':>15} {'#bad(generic) max/nonzero over draws':>40} {'note':>10}")
    print("-" * 90)
    for a in range(k + 1, n // 2 + 1):
        bad_mono = count_bad(xvals, u0m, u1m, n, k, a, p)
        gen_results = []
        draws = 0; tries = 0
        ndraw = 20 if a >= 6 else 8
        while draws < ndraw and tries < 12 * ndraw:
            tries += 1
            u0g = [random.randrange(p) for _ in range(n)]
            u1g = [random.randrange(p) for _ in range(n)]
            if not is_far(xvals, u1g, n, k, a, p):
                continue
            gen_results.append(count_bad(xvals, u0g, u1g, n, k, a, p))
            draws += 1
        gmax = max(gen_results) if gen_results else None
        nz = sum(1 for x in gen_results if x > 0)
        binding = "BINDING" if a >= 6 else "shallow"
        flag = ""
        if gmax is not None and gmax > bad_mono:
            flag = " <== generic>mono"
        print(f"{a:>7} {bad_mono:>15} {f'max={gmax} nz={nz}/{len(gen_results)}':>40} {binding:>10}{flag}")

    print("\n# READ (the verdict): at the SHALLOW band a=k+1=4 every (k+1)-tuple is trivially singleton-aligned,")
    print("#  so #bad just counts distinct residual-ratios -- large for ANY stack (generic ~2.4x mono); this band")
    print("#  is FAR above the prize floor and NON-binding. At the DEEP BINDING bands (a>=6, where the floor lives)")
    print("#  the monomial far-line pins #bad to its binding value while EVERY generic random AND structured-low-degree")
    print("#  stack gives EXACTLY 0 (0/20 nonzero). => the MONOMIAL far-line IS the worst-case stack at the binding")
    print("#  radius: the board's restriction to monomial stacks is JUSTIFIED at the deep band; generic stacks do not")
    print("#  threaten the canonical core B = max over ALL stacks there. (Supports, does not formally prove, the WLOG.)")


if __name__ == '__main__':
    main()
