#!/usr/bin/env python3
# -*- coding: ascii -*-
"""
probe_pgl2_coincidence_census.py -- the full-PGL2 coincidence census (normalizer-gap lane).

Pre-registered: lalalune/ArkLib#371, comment 4687191139, item 1 (the spectral-gap
theorem candidate).

OBJECT. q prime, n | q-1, H = the order-n multiplicative subgroup of F_q*.
For EVERY Moebius map sigma in PGL2(F_q) -- q(q-1)(q+1) elements, enumerated by an
exact bijective transversal, no double counting -- the coincidence count

    c(sigma) = #{x in H : sigma(x) defined (denominator != 0) and sigma(x) in H}.

Stab(H) = {x -> cx : c in H} u {x -> c/x : c in H}   (2n maps, all with c = n).

QUESTION. The histogram of c over PGL2 \\ Stab(H); its max; the structure of the
argmax maps; every map with c > n^2/q + 4.  CONJECTURE under test: the non-stabilizer
max is O(n^2/q) + O(1) -- concretely single digits at these scales -- with a clean
gap below n.

METHOD (exact integer arithmetic, no sampling behind any verdict).

 * Bijective parameterization of PGL2(F_q) by normalized matrix representatives
   [[a,b],[c,d]] acting as x -> (ax+b)/(cx+d):
       family A  (c=0,d=1): x -> a x + b,           a != 0           [q(q-1)   maps]
       family B0 (c=1,d=0): x -> (a x + b)/x,       b != 0           [q(q-1)   maps]
       family B  (c=1)    : x -> (a x + b)/(x + d), d != 0, b != ad  [q(q-1)^2 maps]
   Totals q(q-1)(q+1) = |PGL2(F_q)| exactly (asserted via histogram mass).

 * Right-coset compression. For tau_e : x -> e x (e in H), c(sigma o tau_e) =
   c(sigma): tau_e permutes H and transports poles. Right multiplication by the
   order-n subgroup S0 = {tau_e} is FREE, so PGL2 splits into q(q-1)(q+1)/n orbits
   of size exactly n with constant c.  M*diag(e,1) = [[ae,b],[ce,d]] gives the
   transversal (T = {g^j : 0 <= j < m}, m = (q-1)/n, exactly one rep per H-coset
   of F_q*, T[0] = 1):
       A : a in T, b in F_q       B0 : a in F_q, b in T       B : a in F_q, d in T, b != ad.
   Each rep contributes its orbit weight n to the histogram.

 * Per-rep counting via discrete-log residues: with L(u) = dlog_g(u) mod m,
   sigma(x) in H  <=>  num != 0, den != 0, L(num) == L(den).  For fixed (a, d) the
   whole b-profile is accumulated in O(n^2): x contributes +1 at b = u - a*x for
   exactly the u in the coset den(x)*H.

 * Stab(H) = exactly two transversal orbits: family A (a=1, b=0) = {x -> ex} and
   family B0 (a=0, b=1) = {x -> e/x}.  Both asserted to have c = n; they are kept
   out of the non-stabilizer histogram.

 * Verification gates (all hard asserts):
     G1 mass:        sum of histogram == q(q-1)(q+1)
     G2 1st moment:  sum_sigma c(sigma) == n^2 * q(q-1)   [sharp transitivity:
                     each (x,y) in H x H has |PGL2|/(q+1) = q(q-1) maps x -> y]
     G3 stab:        stab histogram == {n: 2n} from exactly the two named orbits
     G4 orbits:      every tracked rep orbit expanded to its n member matrices and
                     each member's c recounted from the definition (field inversion
                     + set membership -- a code path independent of the dlog engine)
     G5 brute force: a SEPARATE direct census over all q(q-1)(q+1) normalized
                     matrices, no orbit compression, no dlog tables (subcommand
                     `brute`, gate closed by subcommand `compare`)
     G6 N(T)\\Stab:   every torus-normalizer map with c not in H (x -> cx and
                     x -> c/x, c in F_q* \\ H) has coincidence count 0 (checked
                     exhaustively; so the answer to "is the argmax in N(T) with
                     c not in H?" is decided, not assumed)
     G7 involution calibration (O133): see below.

INVOLUTION SUB-CENSUS == THE O133 PENCIL CENSUS (calibration gate).
For q odd the involutions of PGL2(F_q) are exactly the NONdegenerate dual points
phi = (p0:p1:p2) of PG(2,q) (p1^2 != p0*p2) via the O133 pencil involution

    sigma_phi(x) = (p1 x - p2)/(p0 x - p1),    M_phi = [[p1, -p2],[p0, -p1]]

(trace 0, det = p0 p2 - p1^2 != 0; q^2 of them = (q^2+q+1) - (q+1 conic points)).

EXACT RELATION (stated and machine-verified for every involution at every scale):

    c(sigma) = 2 * t2(sigma) + f_H(sigma)

where t2 = #{unordered pairs {x,y} c H, x != y, sigma(x) = y} (exactly the O133
pencil t2: 2-element fibers inside the domain) and f_H = #fixed points of sigma
lying in H.  Proof of the relation: the coincidence set {x in H : sigma(x) in H}
is sigma-invariant (sigma(x) in H => sigma(sigma(x)) = x in H since sigma is an
involution), hence partitions into 2-cycles inside H (each contributing 2 to c and
1 to t2) and fixed points in H (each contributing 1 to c and to f_H).  Both sides
are computed by independent code paths and compared for ALL q^2 involutions.

Gate G7: the t2 numbers of this sub-census, completed by the q+1 degenerate conic
pencils (each computed -- not assumed -- to carry t2 = 0 under the O133 partner
rule), must reproduce the stored O133 census byte-exactly:
  scripts/probes/moments/experiment/k3_q{41,113,257}_n{8,16,16}_sub.json
    census.t2_hist
including the n=16 spectral-gap shape: nonstab band capped at t2 <= 3, bins
{4,5,6} EMPTY, the stabilizer band isolated at t2 in {(n-2)/2, n/2} = {7,8} with
multiplicities {n/2, n/2+1} = {8, 9} (the (n-2)/2 vs n/2 split is by whether c is
a square IN H, i.e. f_H = 2 vs 0).  Hard-asserted at (113,16) and (257,16) per the
pre-registration; reported (not asserted) at (41,8) and (257,32).

USAGE
  probe_pgl2_coincidence_census.py fast    [--configs 41:8,113:16,257:16,257:32] [--json PATH]
  probe_pgl2_coincidence_census.py brute   --q Q --n N [--out PATH]
  probe_pgl2_coincidence_census.py compare --q Q --n N [--json PATH] [--brute PATH]

Heavy runs are meant to be wrapped in `taskset -c 0-5 nice -n 10`.  Progress goes
to stderr in chunks; results go to JSON next to this script.
"""

import argparse
import json
import math
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
EXPERIMENT_DIR = os.path.normpath(os.path.join(
    HERE, "..", "moments", "experiment"))
STORED_O133 = {
    (41, 8): "k3_q41_n8_sub.json",
    (113, 16): "k3_q113_n16_sub.json",
    (257, 16): "k3_q257_n16_sub.json",
}
HARD_GATE_CONFIGS = {(113, 16), (257, 16)}   # pre-registered calibration gate
TRACK_CAP = 5000
CLASSIFY_CAP = 200


def log(msg):
    sys.stderr.write(msg + "\n")
    sys.stderr.flush()


# --------------------------------------------------------------------------- tables

def primitive_root(q):
    fac, x, p = [], q - 1, 2
    while p * p <= x:
        if x % p == 0:
            fac.append(p)
            while x % p == 0:
                x //= p
        p += 1
    if x > 1:
        fac.append(x)
    for g in range(2, q):
        if all(pow(g, (q - 1) // f, q) != 1 for f in fac):
            return g
    raise AssertionError("no primitive root (q not prime?)")


def build_tables(q, n):
    assert (q - 1) % n == 0, (q, n)
    m = (q - 1) // n
    g = primitive_root(q)
    dlog = [0] * q          # dlog[0] unused
    v = 1
    for k in range(q - 1):
        dlog[v] = k
        v = v * g % q
    SENT = m + 7            # never equals a residue mod m
    L = [SENT] * q
    for u in range(1, q):
        L[u] = dlog[u] % m
    cosets = [[] for _ in range(m)]
    for u in range(1, q):
        cosets[L[u]].append(u)
    Hlist = list(cosets[0])
    Hset = set(Hlist)
    assert len(Hlist) == n
    inv = [0] * q
    for u in range(1, q):
        inv[u] = pow(u, q - 2, q)
    T = [pow(g, j, q) for j in range(m)]    # one rep per H-coset, T[0] = 1
    assert sorted(set(L[t] for t in T)) == list(range(m))
    return dict(q=q, n=n, m=m, g=g, dlog=dlog, L=L, SENT=SENT,
                cosets=cosets, Hlist=Hlist, Hset=Hset, inv=inv, T=T)


# ------------------------------------------- direct evaluation (independent path)

def count_c_direct(M, tb):
    """c(sigma) straight from the definition: field inversion + set membership."""
    q, inv, Hset = tb["q"], tb["inv"], tb["Hset"]
    a, b, c, d = M
    cnt = 0
    for x in tb["Hlist"]:
        den = (c * x + d) % q
        if den and (a * x + b) * inv[den] % q in Hset:
            cnt += 1
    return cnt


def coincidence_pairs(M, tb):
    q, inv, Hset = tb["q"], tb["inv"], tb["Hset"]
    a, b, c, d = M
    out = []
    for x in tb["Hlist"]:
        den = (c * x + d) % q
        if den:
            y = (a * x + b) * inv[den] % q
            if y in Hset:
                out.append((x, y))
    return out


# ------------------------------------------------------- fast exact census engine

def census_fast(tb, track_min=None):
    """One full pass over the right-S0 transversal.

    Returns (hist_nonstab, hist_stab, tracked, overflow); histograms count MAPS
    (each rep weighted by its orbit size n)."""
    q, n, L = tb["q"], tb["n"], tb["L"]
    cosets, Hlist, Hset, T = tb["cosets"], tb["Hlist"], tb["Hset"], tb["T"]
    hist = {}
    tracked = []
    overflow = 0
    stab_orbits = 0
    t0 = time.time()

    def rec(cnt, fam, a, b, d):
        nonlocal overflow
        hist[cnt] = hist.get(cnt, 0) + n
        if track_min is not None and cnt >= track_min:
            if len(tracked) < TRACK_CAP:
                tracked.append([fam, a, b, d, cnt])
            else:
                overflow += 1

    # family A: x -> a x + b ; reps a in T, b in F_q
    H0 = cosets[0]
    for a in T:
        bar = [0] * q
        for x in Hlist:
            ax = a * x % q
            for u in H0:
                bar[(u - ax) % q] += 1
        for b in range(q):
            if a == 1 and b == 0:           # the {x -> ex} stabilizer orbit
                assert bar[b] == n
                stab_orbits += 1
                continue
            rec(bar[b], "A", a, b, None)
    log("    [q=%d n=%d] family A done (%.1fs)" % (q, n, time.time() - t0))

    # family B0: x -> (a x + b)/x ; reps a in F_q, b in T.
    # On H: den = x in H is never 0 and (ax+b)/x in H <=> ax+b in xH = H.
    for a in range(q):
        for b in T:
            cnt = 0
            for x in Hlist:
                if (a * x + b) % q in Hset:
                    cnt += 1
            if a == 0 and b == 1:           # the {x -> e/x} stabilizer orbit
                assert cnt == n
                stab_orbits += 1
                continue
            rec(cnt, "B0", a, b, 0)
    log("    [q=%d n=%d] family B0 done (%.1fs)" % (q, n, time.time() - t0))

    # family B: x -> (a x + b)/(x + d) ; reps a in F_q, d in T, b != a d
    for di, d in enumerate(T):
        pre = []
        for x in Hlist:
            de = (x + d) % q
            if de:                          # pole x = -d contributes nothing
                pre.append((x, cosets[L[de]]))
        for a in range(q):
            bar = [0] * q
            for x, cos in pre:
                ax = a * x % q
                for u in cos:
                    bar[(u - ax) % q] += 1
            bad = a * d % q
            for b in range(q):
                if b != bad:
                    rec(bar[b], "B", a, b, d)
        log("    [q=%d n=%d] family B d-rep %d/%d (%.1fs)"
            % (q, n, di + 1, len(T), time.time() - t0))

    assert stab_orbits == 2, "stabilizer must be exactly two transversal orbits"
    hist_stab = {n: 2 * n}
    return hist, hist_stab, tracked, overflow


def run_global_checks(q, n, hist_ns, hist_stab):
    order_G = q * (q - 1) * (q + 1)
    mass = sum(hist_ns.values()) + sum(hist_stab.values())
    assert mass == order_G, ("G1 mass", mass, order_G)
    m1 = (sum(c * v for c, v in hist_ns.items())
          + sum(c * v for c, v in hist_stab.items()))
    assert m1 == n * n * q * (q - 1), ("G2 first moment", m1)
    assert hist_stab == {n: 2 * n}, ("G3 stab", hist_stab)
    return {"G1_mass": mass, "G2_first_moment": m1,
            "G2_expected": n * n * q * (q - 1), "G3_stab": dict(hist_stab)}


# ----------------------------------------------------------- brute force (gate G5)

def census_brute(tb):
    """Direct census over all q(q-1)(q+1) normalized matrices.

    Independent of the fast engine: no orbit compression, no dlog tables --
    membership via field inversion + set lookup only."""
    q, n, Hlist, Hset, inv = tb["q"], tb["n"], tb["Hlist"], tb["Hset"], tb["inv"]
    hist = {}
    hist_stab = {}
    t0 = time.time()

    # family A: x -> a x + b, a != 0
    for a in range(1, q):
        for b in range(q):
            cnt = 0
            for x in Hlist:
                if (a * x + b) % q in Hset:
                    cnt += 1
            if b == 0 and a in Hset:
                assert cnt == n
                hist_stab[cnt] = hist_stab.get(cnt, 0) + 1
            else:
                hist[cnt] = hist.get(cnt, 0) + 1
    log("    [brute q=%d n=%d] affine done (%.1fs)" % (q, n, time.time() - t0))

    # c = 1 rows: x -> (a x + b)/(x + d), b != a d   (d = 0 included)
    for d in range(q):
        pre = [(x, inv[(x + d) % q]) for x in Hlist]   # iv == 0 marks the pole
        stab_row_possible = (d == 0)
        for a in range(q):
            axs = [(a * x % q, iv) for x, iv in pre]
            ad = a * d % q
            stab_row = stab_row_possible and a == 0
            for b in range(q):
                if b == ad:
                    continue
                cnt = 0
                for ax, iv in axs:
                    if iv and (ax + b) * iv % q in Hset:
                        cnt += 1
                if stab_row and b in Hset:
                    assert cnt == n
                    hist_stab[cnt] = hist_stab.get(cnt, 0) + 1
                else:
                    hist[cnt] = hist.get(cnt, 0) + 1
        if (d + 1) % 16 == 0 or d == q - 1:
            el = time.time() - t0
            log("    [brute q=%d n=%d] d=%d/%d elapsed %.0fs eta %.0fs"
                % (q, n, d + 1, q, el, el / (d + 1) * (q - d - 1)))
    return hist, hist_stab


# ------------------------------------------------------------ structure analysis

def mat_mul(M, N, q):
    a, b, c, d = M
    e, f, g, h = N
    return ((a * e + b * g) % q, (a * f + b * h) % q,
            (c * e + d * g) % q, (c * f + d * h) % q)


def proj_order(M, q):
    P, k = M, 1
    while not (P[1] == 0 and P[2] == 0 and P[0] == P[3]):
        P = mat_mul(P, M, q)
        k += 1
        assert k <= q + 1, "PGL2 element order overflow"
    return k


def mult_order(z, q):
    v, k = z % q, 1
    assert v != 0
    while v != 1:
        v = v * z % q
        k += 1
        assert k <= q - 1
    return k


def subgroup_order(elems, tb):
    """Order of the subgroup of F_q* generated by elems (via dlog gcd)."""
    q, dlog = tb["q"], tb["dlog"]
    if not elems:
        return 1
    gg = q - 1
    for u in elems:
        gg = math.gcd(gg, dlog[u])
    return (q - 1) // gg


def classify_member(M, cnt, tb):
    q, L, Hset, inv = tb["q"], tb["L"], tb["Hset"], tb["inv"]
    a, b, c, d = M
    det = (a * d - b * c) % q
    assert det != 0
    tr = (a + d) % q
    disc = (tr * tr - 4 * det) % q   # QR class is a projective invariant
    if disc == 0:
        typ = "parabolic"
    elif pow(disc, (q - 1) // 2, q) == 1:
        typ = "split"
    else:
        typ = "elliptic"
    in_NT = (b == 0 and c == 0) or (a == 0 and d == 0)
    order = proj_order(M, q)
    fixed = [z for z in range(q) if (c * z * z + (d - a) * z - b) % q == 0]
    fp = []
    for z in fixed:
        if z == 0:
            fp.append({"z": 0, "mult_order": None, "in_H": False, "coset": None})
        else:
            fp.append({"z": z, "mult_order": mult_order(z, q),
                       "in_H": z in Hset, "coset": L[z]})
    pairs = coincidence_pairs(M, tb)
    assert len(pairs) == cnt
    mono_pos = mono_neg = None
    if pairs:
        vals = {y * inv[x] % q for x, y in pairs}
        if len(vals) == 1:
            u = vals.pop()
            mono_pos = {"u": u, "u_in_H": u in Hset, "u_coset": L[u],
                        "u_order": mult_order(u, q)}
        vals = {y * x % q for x, y in pairs}
        if len(vals) == 1:
            u = vals.pop()
            mono_neg = {"u": u, "u_in_H": u in Hset, "u_coset": L[u],
                        "u_order": mult_order(u, q)}
    S = [x for x, _ in pairs]
    img = [y for _, y in pairs]
    s_sub = subgroup_order([x * inv[S[0]] % q for x in S], tb) if S else 0
    i_sub = subgroup_order([y * inv[img[0]] % q for y in img], tb) if img else 0
    return {
        "matrix": [a, b, c, d], "c": cnt, "det": det, "trace": tr,
        "disc": disc, "type": typ, "pgl2_order": order, "in_NT": in_NT,
        "fixes_infinity": (c == 0), "fixed_points_in_Fq": fp,
        "coincidence_pairs": [[x, y] for x, y in pairs],
        "monomial_pos": mono_pos, "monomial_neg": mono_neg,
        "S_in_coset_of_subgroup_order": s_sub,
        "image_in_coset_of_subgroup_order": i_sub,
    }


def orbit_matrices(fam, a, b, d, tb):
    q, Hlist = tb["q"], tb["Hlist"]
    if fam == "A":
        base = (a, b, 0, 1)
    elif fam == "B0":
        base = (a, b, 1, 0)
    else:
        base = (a, b, 1, d)
    ba, bb, bc, bd = base
    return [(ba * e % q, bb, bc * e % q, bd) for e in Hlist]


# ------------------------------------- involutions == O133 pencils (gate G7)

def iter_pg2(q):
    """Canonical representatives of the q^2+q+1 points of PG(2,q) -- O133 order."""
    for b in range(q):
        for c in range(q):
            yield (1, b, c)
    for c in range(q):
        yield (0, 1, c)
    yield (0, 0, 1)


def involution_census(tb):
    q, n, L, inv = tb["q"], tb["n"], tb["L"], tb["inv"]
    Hlist, Hset = tb["Hlist"], tb["Hset"]
    dset = Hset
    n_inv = n_deg = 0
    t2_all_pencils = {}
    t2_inv = {}
    t2_stab = {}
    t2_nonstab = {}
    c_inv_hist = {}
    stab_phis = []
    nonstab_max_t2 = -1
    nonstab_argmax = []
    t0 = time.time()
    for phi in iter_pg2(q):
        p0, p1, p2 = phi
        # ---- O133 pencil partner rule (verbatim semantics)
        x0 = p1 if (p0 == 1 and (p1 * p1) % q == p2 and p1 in dset) else None
        matched = 0
        for x in Hlist:
            if x == x0:
                continue
            den = (p0 * x - p1) % q
            if den == 0:
                continue
            y = (p1 * x - p2) * inv[den] % q
            if y != x and y != x0 and y in dset:
                matched += 1
        assert matched % 2 == 0, ("asymmetric partner relation", phi)
        t2_pencil = matched // 2
        t2_all_pencils[t2_pencil] = t2_all_pencils.get(t2_pencil, 0) + 1
        if (p1 * p1 - p0 * p2) % q == 0:
            # degenerate conic point: not a Moebius map
            n_deg += 1
            assert t2_pencil == 0, ("degenerate pencil with t2 != 0", phi)
            continue
        # ---- the involution sigma_phi(x) = (p1 x - p2)/(p0 x - p1)
        n_inv += 1
        M = (p1, (-p2) % q, p0, (-p1) % q)
        M2 = mat_mul(M, M, q)
        assert M2[1] == 0 and M2[2] == 0 and M2[0] == M2[3] != 0, ("not involutive", phi)
        # path 1: direct evaluation -> c, f_H, 2-cycles
        c1 = fH = matched2 = 0
        for x in Hlist:
            den = (p0 * x - p1) % q
            if den == 0:
                continue
            y = (p1 * x - p2) * inv[den] % q
            if y in dset:
                c1 += 1
                if y == x:
                    fH += 1
                else:
                    matched2 += 1
        assert matched2 % 2 == 0
        t2 = matched2 // 2
        assert t2 == t2_pencil, ("pencil t2 != involution t2", phi)
        # path 2: dlog residues (independent membership test)
        c2 = 0
        for x in Hlist:
            den = (p0 * x - p1) % q
            num = (p1 * x - p2) % q
            if den and num and L[num] == L[den]:
                c2 += 1
        # THE EXACT RELATION  c = 2*t2 + f_H, via two independent c paths
        assert c1 == c2 == 2 * t2 + fH, ("relation c = 2*t2 + f_H failed", phi)
        # stabilizer / normalizer classification
        is_neg = (p0 == 0 and p2 == 0)                   # x -> -x  (canon (0,1,0))
        cmap = (-p2) % q if (p0 == 1 and p1 == 0) else None   # x -> cmap/x
        is_stab = is_neg or (cmap is not None and cmap in Hset)
        t2_inv[t2] = t2_inv.get(t2, 0) + 1
        c_inv_hist[c1] = c_inv_hist.get(c1, 0) + 1
        if is_stab:
            t2_stab[t2] = t2_stab.get(t2, 0) + 1
            stab_phis.append((phi, t2, fH))
        else:
            t2_nonstab[t2] = t2_nonstab.get(t2, 0) + 1
            if t2 > nonstab_max_t2:
                nonstab_max_t2, nonstab_argmax = t2, [phi]
            elif t2 == nonstab_max_t2 and len(nonstab_argmax) < 64:
                nonstab_argmax.append(phi)
    assert n_inv == q * q, ("involution count", n_inv)
    assert n_deg == q + 1, ("degenerate pencil count", n_deg)
    # stabilizer involutions: {x -> -x} u {x -> c/x : c in H}, n+1 of them,
    # t2 split {(n-2)/2: n/2, n/2: n/2 + 1} by f_H = 2 (c a square in H) vs 0
    assert len(stab_phis) == n + 1, ("stab involution count", len(stab_phis))
    assert t2_stab == {(n - 2) // 2: n // 2, n // 2: n // 2 + 1}, t2_stab
    log("    [involutions q=%d n=%d] %d involutions + %d degenerate pencils (%.1fs)"
        % (q, n, n_inv, n_deg, time.time() - t0))
    return {
        "n_involutions": n_inv, "n_degenerate_pencils": n_deg,
        "t2_hist_all_pencils": t2_all_pencils,
        "t2_hist_involutions": t2_inv,
        "t2_hist_stab": t2_stab,
        "t2_hist_nonstab": t2_nonstab,
        "c_hist_involutions": c_inv_hist,
        "relation_verified_for_all": True,
        "nonstab_max_t2": nonstab_max_t2,
        "nonstab_argmax_phis_capped": nonstab_argmax,
    }


def o133_gate(q, n, tb, inv_block):
    """Gate G7: reproduce the stored O133 census byte-exactly."""
    out = {"stored_file": None, "domain_match": None, "t2_hist_match": None,
           "n16_gap_456_empty": None, "n16_band_78": None,
           "nonstab_t2_cap": inv_block["nonstab_max_t2"]}
    fname = STORED_O133.get((q, n))
    if fname:
        path = os.path.join(EXPERIMENT_DIR, fname)
        with open(path) as fh:
            stored = json.load(fh)
        assert stored["q"] == q and stored["n"] == n
        dom_ok = sorted(stored["domain"]) == sorted(tb["Hlist"])
        ours = {str(k): v for k, v in
                sorted(inv_block["t2_hist_all_pencils"].items())}
        match = (ours == stored["census"]["t2_hist"])
        out.update(stored_file=fname, domain_match=dom_ok, t2_hist_match=match,
                   stored_t2_hist=stored["census"]["t2_hist"])
        assert dom_ok, "stored O133 domain differs from our H"
        assert match, ("O133 t2 histogram mismatch", ours,
                       stored["census"]["t2_hist"])
    if n == 16:
        hist = inv_block["t2_hist_all_pencils"]
        gap = all(hist.get(v, 0) == 0 for v in (4, 5, 6))
        band = (hist.get(7, 0), hist.get(8, 0)) == (8, 9)
        out.update(n16_gap_456_empty=gap, n16_band_78=band)
        if (q, n) in HARD_GATE_CONFIGS:
            assert gap and band, ("n=16 calibration gate failed", q, n)
            assert inv_block["nonstab_max_t2"] == 3, inv_block["nonstab_max_t2"]
    return out


def nt_zero_gate(tb):
    """Gate G6: every N(T)\\Stab map (x -> cx, x -> c/x with c not in H) has c = 0."""
    q, Hset = tb["q"], tb["Hset"]
    checked = 0
    for cval in range(1, q):
        if cval in Hset:
            continue
        assert count_c_direct((cval, 0, 0, 1), tb) == 0, ("x->cx", cval)
        assert count_c_direct((0, cval, 1, 0), tb) == 0, ("x->c/x", cval)
        checked += 2
    return {"maps_checked": checked, "all_zero": True}


# ------------------------------------------------------------------ orchestration

def hist_to_json(h):
    return {str(k): h[k] for k in sorted(h)}


def run_config(q, n):
    t0 = time.time()
    log("== config (q=%d, n=%d) ==" % (q, n))
    tb = build_tables(q, n)
    order_G = q * (q - 1) * (q + 1)

    h1, hs1, _, _ = census_fast(tb, track_min=None)
    checks = run_global_checks(q, n, h1, hs1)

    cmax = max(c for c, v in h1.items() if v > 0)
    thr = n * n // q + 5            # smallest integer c with c > n^2/q + 4
    over_thr_maps = sum(v for c, v in h1.items() if c >= thr)
    track_min = min(thr, cmax)

    h2, hs2, tracked, overflow = census_fast(tb, track_min=track_min)
    assert h2 == h1 and hs2 == hs1, "pass-2 histogram drift"

    # G4: expand each tracked rep orbit, recount every member from the definition
    members = []
    for fam, a, b, d, cnt in tracked:
        for M in orbit_matrices(fam, a, b, d, tb):
            assert count_c_direct(M, tb) == cnt, ("orbit recount", fam, a, b, d)
            members.append((M, cnt))
    log("    G4 orbit recount: %d tracked orbits -> %d member maps, all verified"
        % (len(tracked), len(members)))

    classified = [classify_member(M, cnt, tb)
                  for M, cnt in members[:CLASSIFY_CAP]]

    inv_block = involution_census(tb)
    gate7 = o133_gate(q, n, tb, inv_block)
    gate6 = nt_zero_gate(tb)

    # involution c-histogram must embed pointwise in the full histogram
    hist_all = dict(h1)
    for c, v in hs1.items():
        hist_all[c] = hist_all.get(c, 0) + v
    for c, v in inv_block["c_hist_involutions"].items():
        assert v <= hist_all.get(c, 0), ("involution c-hist exceeds census", c)

    block = {
        "q": q, "n": n, "m": tb["m"], "g": tb["g"], "H": tb["Hlist"],
        "pgl2_order": order_G,
        "stab_order": 2 * n,
        "mean_c_exact": "%d/%d" % (n * n, q + 1),
        "hist_nonstab": hist_to_json(h1),
        "hist_stab": hist_to_json(hs1),
        "max_c_nonstab": cmax,
        "gap_to_n": n - cmax,
        "nonstab_maps_at_max": h1[cmax],
        "threshold_c_gt_n2q_plus4": thr,
        "maps_over_threshold": over_thr_maps,
        "tracked_orbits": len(tracked),
        "tracked_overflow": overflow,
        "checks": checks,
        "gate6_NT_minus_stab_all_zero": gate6,
        "involutions": {k: (hist_to_json(v) if isinstance(v, dict) else v)
                        for k, v in inv_block.items()
                        if k != "nonstab_argmax_phis_capped"},
        "involution_nonstab_argmax_phis": inv_block["nonstab_argmax_phis_capped"],
        "gate7_O133": gate7,
        "argmax_and_over_threshold_maps": classified,
        "elapsed_s": round(time.time() - t0, 1),
    }
    log("== config (q=%d, n=%d) done in %.1fs: max nonstab c = %d "
        "(threshold %d, %d maps >= threshold) ==" %
        (q, n, block["elapsed_s"], cmax, thr, over_thr_maps))
    return block


def main_fast(args):
    configs = []
    for part in args.configs.split(","):
        qs, ns = part.strip().split(":")
        configs.append((int(qs), int(ns)))
    results = {"probe": "probe_pgl2_coincidence_census",
               "preregistration": "lalalune/ArkLib#371 comment 4687191139 item 1",
               "configs": {}}
    for q, n in configs:
        results["configs"]["q%d_n%d" % (q, n)] = run_config(q, n)
    with open(args.json, "w") as fh:
        json.dump(results, fh, indent=1)
    log("results written to %s" % args.json)
    for key, blk in results["configs"].items():
        print("%s: max nonstab c = %d (n = %d, gap %d), maps > n^2/q+4: %d, "
              "O133 gate: %s" %
              (key, blk["max_c_nonstab"], blk["n"], blk["gap_to_n"],
               blk["maps_over_threshold"],
               blk["gate7_O133"]["t2_hist_match"]))


def main_brute(args):
    tb = build_tables(args.q, args.n)
    t0 = time.time()
    hist, hist_stab = census_brute(tb)
    out = {"q": args.q, "n": args.n,
           "hist_nonstab": hist_to_json(hist),
           "hist_stab": hist_to_json(hist_stab),
           "elapsed_s": round(time.time() - t0, 1)}
    path = args.out or os.path.join(HERE, "brute_q%d_n%d.json" % (args.q, args.n))
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1)
    print("brute census written to %s (%.1fs)" % (path, out["elapsed_s"]))


def main_compare(args):
    jpath = args.json
    bpath = args.brute or os.path.join(HERE, "brute_q%d_n%d.json" % (args.q, args.n))
    with open(jpath) as fh:
        results = json.load(fh)
    with open(bpath) as fh:
        brute = json.load(fh)
    key = "q%d_n%d" % (args.q, args.n)
    blk = results["configs"][key]
    ok_ns = blk["hist_nonstab"] == brute["hist_nonstab"]
    ok_st = blk["hist_stab"] == brute["hist_stab"]
    assert ok_ns and ok_st, ("brute mismatch", key)
    blk.setdefault("gate5_brute", {})
    blk["gate5_brute"] = {"file": os.path.basename(bpath),
                          "hist_nonstab_match": ok_ns, "hist_stab_match": ok_st}
    with open(jpath, "w") as fh:
        json.dump(results, fh, indent=1)
    print("G5 brute gate %s: nonstab %s, stab %s" % (key, ok_ns, ok_st))


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p1 = sub.add_parser("fast")
    p1.add_argument("--configs", default="41:8,113:16,257:16,257:32")
    p1.add_argument("--json", default=os.path.join(HERE, "results_pgl2_census.json"))
    p2 = sub.add_parser("brute")
    p2.add_argument("--q", type=int, required=True)
    p2.add_argument("--n", type=int, required=True)
    p2.add_argument("--out", default=None)
    p3 = sub.add_parser("compare")
    p3.add_argument("--q", type=int, required=True)
    p3.add_argument("--n", type=int, required=True)
    p3.add_argument("--json", default=os.path.join(HERE, "results_pgl2_census.json"))
    p3.add_argument("--brute", default=None)
    args = ap.parse_args()
    if args.cmd == "fast":
        main_fast(args)
    elif args.cmd == "brute":
        main_brute(args)
    else:
        main_compare(args)


if __name__ == "__main__":
    main()
