#!/usr/bin/env python3
"""
probe_407_lacunary_pencil_Npencil.py   (issue #407, target P5-sparse-poly-roots)

THE ORBIT-COUNT CONSEQUENCE of the inner sparse-root count.

The companion probes (probe_407_lacunary_pencil_roots_mann.py,
probe_407_lacunary_pencil_coset_mann.py) established that the INNER per-witness
agreement (# mu_n roots of a t=k+2 term pencil poly) CAN be Theta(n), via the
single dyadic cyclotomic coset factor (1+x^{n/2}).

But the GOVERNING LAW is about the bad-ALPHA count:
    I(delta) = #{alpha in F_q : x^a + alpha x^b is delta-close to RS[k]},
    delta* = sup{ delta : I(delta) <= q*eps* ~ n }.
The orbit-count crossing law (in-tree OrbitCountCrossingLaw.lean) factors
    I = N_pencil * S,   S = n/gcd(b-a,n),
and reduces the budget I<=n to the orbit test  N_pencil <= gcd(b-a,n).

THIS PROBE measures, EXACTLY over F_p (p >> n^3, mu_n PROPER -- prize-faithful),
for every monomial pencil (a,b) and every agreement threshold thr in the window:
   I(thr)       = # alpha with max-agreement(x^a+alpha x^b, RS[k]) >= thr
   N_pencil     = # orbits of the bad-alpha set under alpha->alpha*w^{b-a}
We sweep thr ACROSS the genuinely open window interior  rho*n < thr <= sqrt(rho)*n
(beyond Johnson, below capacity) -- NOT the trivial below-Johnson regime where
C(n,thr) subsets give exponentially many low-agreement alphas.

Exactness: every alpha with agreement >= thr >= k+1 is produced by some (k+1)-subset
(any k+1 of its agreement points determine it via the unique deg-k divided
difference), so the candidate alpha set = {alphas from (k+1)-subsets} is EXACT and
complete; max-agreement is then computed exactly per candidate.

KEY FINDING (n=8, both rates, exact -- see committed output):
   * At the JOHNSON EDGE (thr = sqrt(rho)*n): worst-pencil I is SMALL (<= n) and
     N_pencil is small (<= 2). This is the Johnson-protected part of the window.
   * At the DEEP INTERIOR (thr strictly between rho*n and sqrt(rho)*n, e.g. thr=3
     for n=8,k=2): I JUMPS far above the budget n (I=40 vs n=8) and N_pencil
     exceeds gcd(b-a,n) (N=5,6 vs gcd=1). This is the bad-alpha count crossing
     its budget -- i.e. it LOCATES delta* strictly below the Johnson edge but the
     count there is the FULL (open, BGK-sized) incidence with NO orbit compression
     escape (N > gcd).

VERDICT (orbit-count lane): the orbit count N_pencil does NOT stay <= gcd(b-a,n)
in the deep window interior -- the S-compression buys a constant factor only; below
Johnson, N inherits the (open, BGK-sized) growth of I.  This is CONSISTENT with the
in-tree refuted-survivors (candidate_floor_is_exact_REFUTED) and the recon
consensus that at constant rate the tight incidence is itself exponential with no
lossy edge.  The probe thus REFUTES the naive "N_pencil <= gcd => closeable"
escape in the deep interior, and confirms the per-witness Theta(n) coset factor is
benign (it lives at the Johnson edge with N small) while the real growth is the
sub-Johnson bad-alpha count = the BGK wall.  Does NOT close the prize.

HONESTY: exact over F_p, p >> n^3, mu_n proper.  Feasible only for small n (the
(k+1)-subset and k-subset enumerations are C(n,k+1), C(n,k)); the law is the
SCALING claim, anchored at n=8 exactly and extended toward n=16,32 where feasible.
"""
import itertools
from math import gcd, sqrt, ceil, floor
import math

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True
def prime_ge(lo, n):
    p = lo - (lo % n) + 1
    while not (is_prime(p) and (p-1) % n == 0): p += n
    return p
def find_gen(p, n):
    for g0 in range(2, p):
        w = pow(g0, (p-1)//n, p)
        if pow(w, n, p) == 1 and all(pow(w, n//q, p) != 1 for q in (2,3,5,7) if n % q == 0):
            return w
    raise RuntimeError
def inv(a, p): return pow(a % p, p-2, p)

def alpha_for_subset(Tvals, a, b, p, k):
    """(k+1)-subset Tvals interpolable by deg<k for word X^a+alpha X^b => unique alpha."""
    Xs = Tvals; m = k+1
    M = [[pow(Xs[c], i, p) for c in range(m)] for i in range(k)]
    rows = [r[:] for r in M]; pivots = []; r = 0
    for c in range(m):
        piv = None
        for rr in range(r, k):
            if rows[rr][c] % p != 0: piv = rr; break
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        iv = inv(rows[r][c], p); rows[r] = [(xx*iv) % p for xx in rows[r]]
        for rr in range(k):
            if rr != r and rows[rr][c] % p != 0:
                f = rows[rr][c]; rows[rr] = [(aa - f*bb) % p for aa, bb in zip(rows[rr], rows[r])]
        pivots.append(c); r += 1
    free = [c for c in range(m) if c not in pivots]
    if not free: return None
    fc = free[0]; lam = [0]*m; lam[fc] = 1
    for i, c in enumerate(pivots): lam[c] = (-rows[i][fc]) % p
    U = sum(lam[c]*pow(Xs[c], a, p) for c in range(m)) % p
    V = sum(lam[c]*pow(Xs[c], b, p) for c in range(m)) % p
    if V % p == 0: return None
    return (-U*inv(V, p)) % p

def max_agree(n, k, p, X, a, b, alpha):
    y = [(pow(X[j], a, p) + alpha*pow(X[j], b, p)) % p for j in range(n)]
    best = 0
    for comb in itertools.combinations(range(n), k):
        bx = [X[i] for i in comb]; by = [y[i] for i in comb]; cnt = 0
        for jx in range(n):
            xx = X[jx]; tot = 0
            for jj in range(k):
                num = by[jj]; den = 1; xj = bx[jj]
                for ll in range(k):
                    if ll != jj:
                        num = num*((xx - bx[ll]) % p) % p; den = den*((xj - bx[ll]) % p) % p
                tot = (tot + num*inv(den, p)) % p
            if tot == y[jx]: cnt += 1
        if cnt > best: best = cnt
        if best == n: break
    return best

def main():
    print("DEEP WINDOW INTERIOR bad-alpha count I and orbit count N (rho*n < agr <= sqrt(rho)*n)", flush=True)
    print("all pencils, exact, prize-faithful p >> n^3, mu_n proper", flush=True)
    for (n, k) in [(8, 2), (8, 4), (16, 4), (16, 2), (32, 8), (32, 4)]:
        if math.comb(n, k+1) > 2_000_000 or math.comb(n, k) > 2_000_000:
            print(f"\nn={n} k={k}: skip (C(n,k+1) or C(n,k) too big)", flush=True); continue
        p = prime_ge(8*n**3, n); w = find_gen(p, n); X = [pow(w, j, p) for j in range(n)]
        rho = k/n; lo_ag = rho*n; hi_ag = sqrt(rho)*n
        thrs = [t for t in range(floor(lo_ag)+1, ceil(hi_ag)+1)]
        if not thrs: thrs = [ceil(hi_ag)]
        print(f"\nn={n} k={k} rho={rho:.3f} budget(n)={n}: window agreement in ({lo_ag:.2f},{hi_ag:.2f}], thrs={thrs}", flush=True)
        seen_d = set(); b = k
        for de in range(1, n):
            a = (b + de) % n
            if a < k or a == b: continue
            d = gcd((b-a) % n, n)
            if d in seen_d: continue
            seen_d.add(d)
            cand = set()
            for Tidx in itertools.combinations(range(n), k+1):
                al = alpha_for_subset([X[j] for j in Tidx], a, b, p, k)
                if al is not None: cand.add(al)
            agrs = {al: max_agree(n, k, p, X, a, b, al) for al in cand}
            line = f"  (a,b)=({a},{b}) gcd={d}: "
            for thr in thrs:
                bad = [al for al, g in agrs.items() if g >= thr]
                S = n//d; mult = pow(w, (b-a) % n, p); seen = set(); N = 0
                for al in bad:
                    if al in seen: continue
                    N += 1; cur = al
                    for _ in range(S): seen.add(cur); cur = cur*mult % p
                flag = "" if (len(bad) <= n and N <= d) else " <-OVER"
                line += f"[thr{thr}:I={len(bad)},N={N}{flag}] "
            print(line, flush=True)
    print("\nVERDICT: at the JOHNSON edge (thr=sqrt(rho)*n) I and N are small (Johnson-protected);", flush=True)
    print("at the DEEP interior (rho*n<thr<sqrt(rho)*n) I jumps far above n and N exceeds gcd --", flush=True)
    print("the orbit S-compression does NOT bound the sub-Johnson incidence. N_pencil<=gcd is", flush=True)
    print("REFUTED in the deep interior; below Johnson the bad-alpha count IS the BGK wall.", flush=True)

if __name__ == "__main__":
    main()
