#!/usr/bin/env python3
"""
probe_444_a1_conductor_scaling.py  (#444 angle A1 — the DECISIVE n-scaling of the u0-sheaf conductor)

Verified setup (probe_444_a1_krawtchouk_trace_sheaf + /tmp parseval check):
  S(u0) = sum_{xi in D, xi != 0} K_w(wt xi) e(xi.u0),   D = Cext^perp = (C+<u1>)^perp,  dim D = n-k-1.
  Parseval (EXACT, verified): avg_{u0 in F_q^n} |S(u0)|^2 = sum_{xi in D, xi!=0} K_w(wt xi)^2 =: L2^2.
  Open-core literal inequality: sup_{u0} |S(u0)| <= |Ball| = K_w(0).
  FKM/Deligne PREDICTION (the new lemma): if u0 |-> S(u0) is the trace of a sheaf of conductor c=O(1),
    sup_{u0} |S(u0)| <= c * L2,  i.e.  c_eff := sup|S|/L2  is BOUNDED uniformly in n.

THE DECISIVE TEST.  Hold the RATE k/n FIXED and the WINDOW r/n FIXED, GROW n = 2^mu, and watch c_eff.
  - c_eff bounded (flat) as n grows           => the u0-sheaf has bounded conductor => FKM => sqrt-canc => CRACK.
  - c_eff grows ~ const, or ~ sqrt(log n)      => conductor n-dependent => relocation FAILS => reduces-to-wall.
We ALSO report sup|S|/L2 vs sup|S|/|Ball|: a sheaf-sharp bound c*L2 beats the trivial |Ball| iff
c*L2 < |Ball|, i.e. iff L2/|Ball| < 1/c (the Krawtchouk-weight concentration must be strong enough).

Feasibility: u0 swept over ALL q^n (drop trivial char), inner sum over |D|=q^{n-k-1}. We use the
SMALLEST prime q with n|q-1 to push n; this is NOT the prize regime q>>n^3, so any BOUNDED c_eff is
only suggestive (small q is the easy regime for cancellation). The HONEST falsifier is the opposite:
if c_eff GROWS even at small q, it grows a fortiori in the prize regime => reduces-to-wall. (We then
also run a few rows at LARGER q same n to see the q-dependence of c_eff.)
"""
import itertools, math, cmath
from math import comb

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def smallest_q(n, qmin=3):
    q = max(qmin, n+1)
    q = ((q-1)//n)*n + 1
    if q < qmin: q += n
    while not (is_prime(q) and (q-1) % n == 0 and q >= qmin):
        q += n
    return q

def primroot(q):
    m = q-1; fs = set(); d = 2
    while d*d <= m:
        if m % d == 0:
            fs.add(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fs.add(m)
    a = 2
    while any(pow(a, (q-1)//f, q) == 1 for f in fs): a += 1
    return a

def kernel_basis(q, n, k, D_eval):
    # D = kernel of the (k+1) x n power matrix V[j][x]=x^j  (= Cext^perp).
    V = [[pow(x, j, q) for x in D_eval] for j in range(k+1)]
    M = [row[:] for row in V]; rows, cols = k+1, n; pivots = []; rr = 0
    for c in range(cols):
        piv = next((ri for ri in range(rr, rows) if M[ri][c] % q != 0), None)
        if piv is None: continue
        M[rr], M[piv] = M[piv], M[rr]
        inv = pow(M[rr][c], q-2, q)
        M[rr] = [(x*inv) % q for x in M[rr]]
        for ri in range(rows):
            if ri != rr and M[ri][c] % q != 0:
                f = M[ri][c]; M[ri] = [(a-f*b) % q for a, b in zip(M[ri], M[rr])]
        pivots.append(c); rr += 1
        if rr == rows: break
    free = [c for c in range(cols) if c not in pivots]
    basis = []
    for fcol in free:
        vec = [0]*cols; vec[fcol] = 1
        for i, pc in enumerate(pivots): vec[pc] = (-M[i][fcol]) % q
        basis.append(vec)
    return basis

def run(q, n, k, r, cap=8_000_000):
    # PARAMETER SPACE = F_q^{dimD}: S(u0) depends on u0 only via t_i = (basis_i . u0). The distinct
    # values of t range over ALL of F_q^{dimD} (basis independent), so sweeping t in F_q^{dimD} is
    # the EXACT sup over the q^{k+1}-coset parameter family (verified vs full q^n sweep, /tmp).
    D_eval = [pow(primroot(q), ((q-1)//n)*i, q) for i in range(n)]
    basis = kernel_basis(q, n, k, D_eval)
    dimD = len(basis)
    assert dimD == n-k-1
    if dimD <= 0 or q**dimD > cap:
        return dict(skip=f"dimD={dimD} q^dimD={q**dimD} (cap {cap})")
    def kraw_shell(l, j):
        return sum((-1)**i*(q-1)**(l-i)*comb(j, i)*comb(n-j, l-i)
                   for i in range(0, l+1) if 0 <= l-i <= n-j and i <= j)
    Kball = [sum(kraw_shell(l, j) for l in range(0, r+1)) for j in range(n+1)]
    Ball = Kball[0]
    # Each D element <-> coefficient vector coeffs in F_q^{dimD}; xi.u0 = sum coeffs_i t_i.
    # Store (coeffs, K_w(wt xi)), DROP trivial xi=0.
    Dw = []
    for coeffs in itertools.product(range(q), repeat=dimD):
        if not any(coeffs): continue
        xi = [0]*n
        for ci, bvec in zip(coeffs, basis):
            if ci:
                for t in range(n): xi[t] = (xi[t] + ci*bvec[t]) % q
        wj = sum(1 for t in xi if t != 0)
        Kw = Kball[wj]
        if Kw != 0:
            Dw.append((coeffs, Kw))
    w = cmath.exp(2j*math.pi/q)
    wpow = [w**a for a in range(q)]
    R_inf = 0.0; sum2 = 0.0; sum4 = 0.0; cnt = 0
    for tvec in itertools.product(range(q), repeat=dimD):
        S = 0j
        for coeffs, Kw in Dw:
            ph = 0
            for ci, ti in zip(coeffs, tvec):
                if ci: ph += ci*ti
            S += Kw*wpow[ph % q]
        a = abs(S)
        if a > R_inf: R_inf = a
        sum2 += a*a; sum4 += a*a*a*a; cnt += 1
    L2 = math.sqrt(sum2/cnt)
    L4 = (sum4/cnt)/((sum2/cnt)**2) if sum2 > 0 else 0.0
    parseval = math.sqrt(sum(Kw*Kw for _, Kw in Dw))
    return dict(q=q, n=n, k=k, r=r, dimD=dimD, cnt=cnt, Ball=Ball, R_inf=R_inf, L2=L2,
                parseval=parseval, L4=L4, c_eff=R_inf/L2 if L2 else float('inf'),
                sup_over_ball=R_inf/Ball if Ball else 0.0, L2_over_ball=L2/Ball if Ball else 0.0)

def show(res):
    if 'skip' in res:
        print(f"  SKIP {res['skip']}"); return
    print(f"{res['q']:>6} {res['n']:>4} {res['k']:>3} {res['r']:>3} {res['dimD']:>5} "
          f"{res['Ball']:>10} {res['R_inf']:>11.2f} {res['L2']:>11.2f} {res['c_eff']:>7.3f} "
          f"{res['L4']:>6.3f} {res['sup_over_ball']:>9.3f} {res['L2_over_ball']:>9.3f}", flush=True)

if __name__ == "__main__":
    hdr = (f"{'q':>6} {'n':>4} {'k':>3} {'r':>3} {'dimD':>5} {'|Ball|':>10} "
           f"{'sup|S|':>11} {'L2(S)':>11} {'c_eff':>7} {'L4':>6} {'sup/Bl':>9} {'L2/Bl':>9}")

    print("="*112)
    print("BLOCK 1 — n-scaling at FIXED dimD=2 (rate k/n -> 1), window r/n ~ 1/4. Grows n with feasible sweep.")
    print("c_eff flat as n grows => bounded conductor (CRACK signal); c_eff grows => reduces-to-wall.")
    print("="*112); print(hdr)
    # dimD = n-k-1 = 2 => k = n-3. r ~ n/4 (interior window). Sweep cost q^2*q^2 = q^4, cheap; push n.
    for n in [4, 8, 16, 32, 64, 128]:
        k = n-3; r = max(1, n//4)
        q = smallest_q(n)
        show(run(q, n, k, r))

    print()
    print("="*112)
    print("BLOCK 2 — dimD-scaling at FIXED n=16 (vary k => dimD=1..5), window r=4. Tests conductor vs |D|.")
    print("="*112); print(hdr)
    for dimD in [1, 2, 3, 4, 5]:
        n = 16; k = n - dimD - 1; r = 4
        q = smallest_q(n)
        show(run(q, n, k, r, cap=30_000_000))

    print()
    print("="*112)
    print("BLOCK 3 — q-dependence at FIXED n,k,r=dimD=2 (toward the prize regime q>>n^3).")
    print("="*112); print(hdr)
    n, k, r = 8, 5, 2   # dimD=2; sweep q^2, cost q^4
    for qq in [17, 41, 113, 257, 1033, 4099]:
        q = qq
        if not (is_prime(q) and (q-1) % n == 0):
            q = smallest_q(n, qmin=qq)
        show(run(q, n, k, r, cap=200_000_000))

    print()
    print("READING:")
    print("  c_eff = sup|S| / L2.  FKM/new-lemma predicts c_eff = O(1) (conductor) UNIFORMLY in n,q.")
    print("  If c_eff is FLAT across each block's n-rows => bounded conductor => CRACK candidate.")
    print("  If c_eff GROWS with n (block 1/2) or with q (block 3) => conductor n/q-dependent => WALL.")
    print("  L2/Bl < 1/c_eff would mean the sheaf bound c*L2 beats trivial |Ball| (past Johnson).")
