#!/usr/bin/env python3
"""wf407_T357-10-derand_colocation.py — THE NEVER-RUN CO-LOCATION PROBE.

Thread T357-10-derand (= 357-T10 / 232-T06): derandomize random-RS capacity to
explicit smooth. The fold-transport feasibility frontier
(probe_fold_transport_feasibility.py) reduced the WHOLE viability question to ONE
toy-probeable successor never run:

  Fold arity s=2 on the smooth 2-power tower. The squaring fold μ_n -> μ_{n/2}
  sends x and -x = g^{n/2}*x to the same downstairs point x^2; a downstairs BLOCK
  is the antipodal pair {x,-x}. The effective unfolding loss is
     L = 1 + (fraction of MCA-bad error coords in FRESH blocks, NOT antipodal-closed).
  The fold route to capacity beats Johnson iff that spread-fraction < sqrt(rho),
  i.e. the CO-LOCATION fraction
     cl(E) = #{x in E : -x in E} / |E|     (E = error support)
  is >= 1 - sqrt(rho) for EVERY MCA-bad error pattern.

WHAT WE MEASURE (exact, full enumeration of error sets at toy scale):
  For RS[F_p, μ_n, k] (n=2^mu smooth subgroup) and a stack u=(u0,u1):
   gamma is MCA-bad at radius delta iff (u0+gamma*u1) agrees with SOME deg-<k poly
   on >= n-floor(delta*n) coords, i.e. there is an error set E (|E| <= floor(delta n))
   whose complement interpolates to deg<k. We enumerate error sets E of size
   <= floor(delta n) (cheap: C(n, <=delta n)), find those whose complement
   interpolates, and for EACH such (gamma, E) record cl(E). The route demands
   cl(E) >= 1-sqrt(rho) for ALL of them; we report the MINIMUM cl(E) (closest to a
   spread refutation) and count how many bad patterns spread below threshold.

  The maximal agreement set = MINIMAL error set is the route's BEST case (least
  spread). We report cl over the minimal error sets too (the per-gamma best).

VERDICT: route ALIVE  <=> every realized MCA-bad min-error-support has cl >= 1-sqrt(rho).
         route REFUTED <=> some realized MCA-bad min-error-support has cl < 1-sqrt(rho).
"""
import sys, itertools
from math import sqrt

def _flush():
    sys.stdout.flush()

def prime_factors(n):
    f, d = set(), 2
    while d*d <= n:
        while n % d == 0:
            f.add(d); n //= d
        d += 1
    if n > 1: f.add(n)
    return f

def find_gen_order(p, n):
    assert (p-1) % n == 0
    cof = (p-1)//n
    for cand in range(2, p):
        g = pow(cand, cof, p)
        if g == 1: continue
        if all(pow(g, n//q, p) != 1 for q in prime_factors(n)):
            return g
    raise RuntimeError("no gen")

def subgroup(p, n):
    g = find_gen_order(p, n)
    H = [pow(g, i, p) for i in range(n)]
    assert len(set(H)) == n
    return H

def interpolates_deglt(pts, k, p):
    """True iff some poly deg<k passes through all (x,y) in pts (x distinct)."""
    pts = list(pts)
    if len(pts) <= k:
        return True
    base = pts[:k]
    xs = [x for x,_ in base]; ys = [y for _,y in base]
    def lag(xq):
        tot = 0
        for i in range(k):
            num = ys[i] % p; den = 1
            for j in range(k):
                if j == i: continue
                num = (num*((xq-xs[j])%p))%p
                den = (den*((xs[i]-xs[j])%p))%p
            tot = (tot + num*pow(den, p-2, p))%p
        return tot
    for xq, yq in pts[k:]:
        if lag(xq) != yq % p:
            return False
    return True

def coloc(H, Eidx, p):
    """cl over error-index-set Eidx."""
    n = len(H); pos = {H[i]: i for i in range(n)}
    if not Eidx: return (0,0,1.0)
    E = set(Eidx); c = 0
    for i in E:
        if pos[(-H[i]) % p] in E: c += 1
    return (len(E), c, c/len(E))

def min_error_sets(H, vals, k, p, max_err):
    """All MINIMAL error index-sets E (|E|<=max_err) whose complement
    interpolates to deg<k. Returns list of E (as frozensets) of the SMALLEST
    size that works; if none up to max_err, []. Also returns that smallest size."""
    n = len(H); pts_all = list(zip(H, vals))
    for size in range(0, max_err+1):
        good = []
        for Ecombo in itertools.combinations(range(n), size):
            Eset = set(Ecombo)
            comp = [pts_all[i] for i in range(n) if i not in Eset]
            if interpolates_deglt(comp, k, p):
                good.append(frozenset(Ecombo))
        if good:
            return good, size
    return [], None

def run_instance(p, n, k, lbl, rho, families):
    H = subgroup(p, n)
    sq = sqrt(rho); johnson = 1-sq; cap = 1-rho; thr = 1-sq
    print(f"\n=== F_{p}, mu_{n}, k={k}, rho={lbl} | Johnson {johnson:.4f} cap {cap:.4f}"
          f" | fold demands cl(E) >= 1-sqrt(rho) = {thr:.4f} ===")
    _flush()
    out = []
    # window radii: error fraction strictly inside (Johnson, capacity)
    radii = sorted(set(
        d for d in range(1, n)
        if johnson + 1e-9 < d/n < cap - 1e-9
    ))
    if not radii:
        # fall back to the band edges if no integer radius strictly inside
        radii = [max(1, int(((johnson+cap)/2)*n))]
    for fam, stacks in families.items():
        min_cl = 1.0; nbad = 0; nspread = 0; ex = []
        for (u0, u1) in stacks:
            for delta in radii:
                if n - delta < k: continue
                for gamma in range(p):
                    vals = [(u0[x] + gamma*u1[x]) % p for x in H]
                    Es, sz = min_error_sets(H, vals, k, p, delta)
                    if sz is None or sz == 0:
                        continue  # no bad pattern (or exact codeword)
                    nbad += 1
                    # per-gamma best case = the MAX cl over the minimal error sets
                    # (route's most favorable realization)
                    best = max(coloc(H, E, p)[2] for E in Es)
                    if best < min_cl: min_cl = best
                    if best < thr - 1e-9:
                        nspread += 1
                        if len(ex) < 5:
                            E0 = max(Es, key=lambda E: coloc(H,E,p)[2])
                            sE,c,f = coloc(H, E0, p)
                            ex.append((gamma, delta, sE, c, f))
        verdict = ("ALIVE" if (nbad>0 and nspread==0)
                   else ("REFUTED" if nspread>0 else "no-bad"))
        print(f"  [{fam:>11}] bad patterns={nbad:6d}  min cl(E)={min_cl:.4f}  "
              f"#spread<thr={nspread:6d}  -> {verdict}")
        for (g,d,sE,c,f) in ex:
            print(f"        spread: gamma={g} delta={d} |E|={sE} coloc={c} cl={f:.4f} < {thr:.4f}")
        _flush()
        out.append((p,n,k,lbl,fam,verdict,min_cl,nspread,nbad))
    return out

def build_families(H, p, n, k):
    fams = {}
    mono = []
    for (a,b) in [(k,k-1),(k+1,k),(n-1,n-2),(k,1)]:
        if a>=n or b<0 or b>=n: continue
        u0 = {x: pow(x,a,p) for x in H}; u1 = {x: pow(x,b,p) for x in H}
        mono.append((u0,u1))
    fams["KKH26-mono"] = mono
    rnd = []; seed = 1234567
    def nxt():
        nonlocal seed; seed = (seed*1103515245+12345)&0x7fffffff; return seed
    for _ in range(3):
        u0 = {x: nxt()%p for x in H}; u1 = {x: nxt()%p for x in H}; rnd.append((u0,u1))
    fams["random"] = rnd
    return fams

def main():
    print("CO-LOCATION PROBE (T357-10-derand): does the MCA-bad error support of a")
    print("smooth 2-power RS stack co-locate under the squaring fold to 1-sqrt(rho)?")
    print("cl(E) >= 1-sqrt(rho) for EVERY bad pattern <=> fold route ALIVE.")
    print("One spread bad pattern (cl < 1-sqrt(rho)) => REFUTED.\n"); _flush()
    instances = [
        (17, 4, 1, "1/4", 0.25),
        (17, 8, 1, "1/8", 0.125),
        (17, 8, 2, "1/4", 0.25),
        (41, 8, 2, "1/4", 0.25),
        (41, 8, 4, "1/2", 0.5),
        (97, 8, 2, "1/4", 0.25),
    ]
    allv = []
    for (p,n,k,lbl,rho) in instances:
        H = subgroup(p,n); fams = build_families(H,p,n,k)
        allv.extend(run_instance(p,n,k,lbl,rho,fams))
    print("\n" + "="*72); print("GLOBAL VERDICT"); _flush()
    ref = [r for r in allv if r[5]=="REFUTED"]; al = [r for r in allv if r[5]=="ALIVE"]
    print(f"  families REFUTED (a bad pattern spreads): {len(ref)}")
    print(f"  families ALIVE   (all bad co-locate):     {len(al)}")
    if ref:
        print("  => FOLD-TRANSPORT DERANDOMIZATION REFUTED at toy scale: MCA-bad error")
        print("     supports do NOT co-locate to 1-sqrt(rho); unfolding loss L > L*(rho),")
        print("     so the route cannot carry random-RS capacity to explicit smooth RS.")
    elif al and not ref:
        print("  => co-location holds at toy scale: escalate before any claim.")
    else:
        print("  => inconclusive (no bad patterns in window).")
    _flush()

if __name__ == "__main__":
    main()
