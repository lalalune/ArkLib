#!/usr/bin/env python3
"""
Attack on Conjecture 7.1 (sparse-worst-case dominance), ePrint 2026/861 (Action-Orbit FRI):
  "FRI soundness above the Johnson radius is dominated by its 3-position sparse witnesses."
RECONSTRUCTED model (PDF Cloudflare-gated); tests the mechanism: does worst-case single-fold FRI
soundness (# bad challenges lambda) saturate at error-support weight 3?

Fast core: one FRI fold sends f to the affine line {g0+lambda*g1} on D'=D^2. A folded word u is a
codeword of RS_{N/2} iff H*u=0 (H=parity check). #{lambda: H*(g0+lambda*g1)=0} counted in O(1) from
A=H*g0, B=H*g1 (linear in lambda). Closeness radius 1 position: syndrome 0 OR a single column of H.

FINDINGS (q=17/97, N=8/16, rho=1/2,1/4):
  * STRUCTURAL SIGNAL (robust, both N): the maximally-bad low-weight FRI witnesses are supported on
    ANTIPODAL ORBITS {x,-x}: best w=2 witness = supp (0,8) with D[8]=-D[0]; best w=4 = (0,1,8,9) =
    two antipodal pairs {0,8},{1,9}. Exactly the action-orbit / antipodal-coset (ACL) structure that
    ePrint 2026/861 builds its above-Johnson proof on -- encouraging for the ACL<->action-orbit link.
  * CONFOUND (honest caveat): this probe measures Hamming weight of the error-from-zero, NOT
    distance-to-code. RS_N is MDS (min distance N-k+1=5 at N=8), so a weight-5 vector can BE a nonzero
    codeword (distance 0; folds to code for all lambda) and a weight-2 vector is distance 2<Johnson
    (below-Johnson). So the "max=q" breaks at w=5 (d'=0) / w=2 (d'=1pos) are weight/distance artifacts,
    NOT above-Johnson soundness violations. A faithful test must control distance-to-RS_N and use the
    paper's EXACT defn of "3-position sparse witness"/"action-non-stabilised admissibility class" --
    needs the gated 2026/861 PDF. Conclusion: cannot confirm/refute Conj 7.1 from this reconstructed
    model; it establishes only the antipodal-orbit dominance signal.
"""
import itertools, random, math, functools
print = functools.partial(print, flush=True)

def run(q, N, k):
    def egcd(a, b):
        if b == 0: return (a, 1, 0)
        g, x, y = egcd(b, a % b); return (g, y, x - (a // b) * y)
    inv = [0]*q
    for a in range(1, q): inv[a] = egcd(a, q)[1] % q
    def find_root(order):
        for g in range(2, q):
            if pow(g, order, q) == 1 and pow(g, order // 2, q) != 1: return g
        return None
    omega = find_root(N)
    if omega is None or pow(omega, N // 2, q) != q - 1: return None
    D = [pow(omega, i, q) for i in range(N)]
    Dp = sorted(set(pow(x, 2, q) for x in D)); Np = len(Dp); kp = k // 2
    G = [[pow(x, j, q) for x in Dp] for j in range(kp)]
    M = [row[:] for row in G]; rows = kp; cols = Np; pivots = []; r = 0
    for c in range(cols):
        pr = None
        for i in range(r, rows):
            if M[i][c] % q != 0: pr = i; break
        if pr is None: continue
        M[r], M[pr] = M[pr], M[r]
        ipv = inv[M[r][c] % q]; M[r] = [(v * ipv) % q for v in M[r]]
        for i in range(rows):
            if i != r and M[i][c] % q != 0:
                fc0 = M[i][c] % q; M[i] = [(M[i][j] - fc0 * M[r][j]) % q for j in range(cols)]
        pivots.append(c); r += 1
        if r == rows: break
    free = [c for c in range(cols) if c not in pivots]
    Hrows = []
    for fc in free:
        h = [0]*cols; h[fc] = 1
        for ri, pc in enumerate(pivots): h[pc] = (-M[ri][fc]) % q
        Hrows.append(h)
    Hcols = [[Hrows[i][j] for i in range(len(Hrows))] for j in range(Np)]
    nH = len(Hrows)
    posDp = {v: i for i, v in enumerate(Dp)}
    seen = set(); foldinfo = []
    for x in D:
        y = pow(x, 2, q); nx = (q - x) % q
        if y not in seen:
            seen.add(y); foldinfo.append((posDp[y], x, nx))
    inv2 = inv[2]
    def Hmul(vec):
        return tuple(sum(Hrows[i][j]*vec[j] for j in range(Np)) % q for i in range(nH))
    targets = [tuple([0]*nH)] + [tuple(Hcols[j]) for j in range(Np)]
    def badcounts(fvec):
        fd = {D[i]: fvec[i] for i in range(N)}
        g0 = [0]*Np; g1 = [0]*Np
        for (yi, x, nx) in foldinfo:
            g0[yi] = ((fd[x] + fd[nx]) * inv2) % q
            g1[yi] = ((fd[x] - fd[nx]) * inv[(2*x) % q]) % q
        A = Hmul(g0); B = Hmul(g1)
        def solve(t):
            lam = None
            for i in range(nH):
                bi = B[i] % q; rhs = (t[i] - A[i]) % q
                if bi == 0:
                    if rhs != 0: return set()
                else:
                    li = (rhs * inv[bi]) % q
                    if lam is None: lam = li
                    elif lam != li: return set()
            return None if lam is None else {lam}
        s0 = solve(targets[0]); b0 = q if s0 is None else len(s0)
        lam_set = set()
        for t in targets:
            st = solve(t)
            if st is None: lam_set = set(range(q)); break
            lam_set |= st
        return b0, len(lam_set)
    rho = k / N; johnson = 1 - math.sqrt(rho)
    print(f"\n===== q={q} N={N} k={k} rho={rho:.3f} | Np={Np} kp={kp} nH={nH} | Johnson={johnson:.3f} ({johnson*N:.2f} pos) =====")
    res0 = {}; res1 = {}; random.seed(11); SAMPLE = 6000
    for w in range(1, N+1):
        best0 = -1; best1 = -1; sp0 = None; sp1 = None
        for supp in itertools.combinations(range(N), w):
            exhaust = (q-1)**w <= 200000
            itr = (itertools.product(range(1, q), repeat=w) if exhaust
                   else ([random.randrange(1, q) for _ in range(w)] for _ in range(SAMPLE)))
            for vals in itr:
                fvec = [0]*N
                for idx, v in zip(supp, vals): fvec[idx] = v
                b0, b1 = badcounts(fvec)
                if b0 > best0: best0 = b0; sp0 = supp
                if b1 > best1: best1 = b1; sp1 = supp
        res0[w] = best0; res1[w] = best1
        print(f"   w={w}: maxbad d'=0 -> {best0:3d}/{q} (supp {sp0}) | d'=1pos -> {best1:3d}/{q} (supp {sp1})")
    for lbl, res in [("d'=0", res0), ("d'=1pos", res1)]:
        mx = max(res.values()); first = min(w for w in res if res[w] == mx)
        print(f"   [{lbl}] global max={mx}, first at w={first} => "
              f"{'SATURATES by w<=3' if first <= 3 else f'needs w={first} (TENSION)'}  per-w={res}")
    return True

for (q, N, k) in [(17, 8, 4), (17, 8, 2), (97, 16, 8), (97, 16, 4), (193, 16, 8)]:
    run(q, N, k)
