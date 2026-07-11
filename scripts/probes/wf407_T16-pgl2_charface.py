#!/usr/bin/env python3
"""
WF407 T16-pgl2: Does the PGL2 torus-normalizer symmetry transfer to the CHAR-SUM FACE
(Cayley graph Cay(F_q, mu_n) / Gauss periods eta_b = sum_{x in mu_n} e_p(b*x)) and give
a NON-relation concentration input on B = max_{b!=0} |eta_b| ?

EXACT enumeration (no sampling). For each (p, n) with n | (p-1) we compute the full
period vector eta_b, b in F_p^*, and test, ONE BY ONE, every candidate "PGL2 lever":

 (Q1) Does x |-> -1/x preserve mu_n-incidence, and what relation (if any) does it
      force on eta beyond negation?
 (Q2) [confirm-only] negation x |-> -x : eta_{-b} = conj(eta_b) ; the relation is
      eta_{-b} = bar(eta_b), already known; does inversion ADD anything?
 (Q3) The 4 torus-normalizer maps {1, neg, inv, neg.inv} acting on the FREQUENCY b:
      do they permute the period-MULTISET / coset structure in a way that constrains
      max_b|eta_b| BEYOND what negation already gives? i.e. is there a *concentration*
      (not relation) consequence: does the normalizer orbit of the WORST b coincide
      with the worst b, pinning the argmax, or shrink the effective max-over count
      m=(p-1)/n by a further factor up to 4 (the claimed Katz floor n/4 analogue)?

We report, exactly:
  - inv_perm_ok : x|->-1/x maps mu_n -> mu_n  (incidence preserved)  [Q1]
  - eta under b-action of each of the 4 normalizer maps; whether |eta_b| is INVARIANT
    under each (a relation) or not.
  - the number of DISTINCT |eta_b| values, vs m=(p-1)/n (the Gauss-period count), vs
    m/2 (negation already folds conj-pairs into equal modulus), vs m/4 (would-be Katz).
  - whether the argmax b is fixed by the normalizer (concentration), and the orbit size
    of the worst coset under the normalizer-on-frequency action.
"""
import cmath, math
import sympy

def prim_root(p):
    return int(sympy.primitive_root(p))

def musub(n, p):
    g = prim_root(p)
    h = pow(g, (p - 1) // n, p)
    return sorted({pow(h, j, p) for j in range(n)})

def eta(b, G, p, w):
    return sum(cmath.exp(1j * w * ((b * y) % p)) for y in G)

def run(p, n):
    assert (p - 1) % n == 0
    w = 2 * math.pi / p
    G = musub(n, p)
    Gset = set(G)
    m = (p - 1) // n

    # ---- Q1: inversion x |-> -1/x preserves mu_n-incidence?  (mu_n inv- & neg-closed) ----
    inv_closed = all(pow(x, p - 2, p) in Gset for x in G)          # x^{-1} in mu_n
    neg_closed = all((p - x) % p in Gset for x in G)               # -x in mu_n
    neginv_closed = all((p - pow(x, p - 2, p)) % p in Gset for x in G)  # -1/x in mu_n

    # ---- eta vector over all nonzero b ----
    etas = {b: eta(b, G, p, w) for b in range(1, p)}
    inv = {b: pow(b, p - 2, p) for b in range(1, p)}

    # the 4 torus-normalizer maps acting on the FREQUENCY b
    maps = {
        'id':      lambda b: b,
        'neg':     lambda b: (p - b) % p,
        'inv':     lambda b: inv[b],
        'neg.inv': lambda b: (p - inv[b]) % p,
    }

    # which of the 4 leave |eta_b| INVARIANT for ALL b? (= a relation among periods)
    rel = {}
    for name, f in maps.items():
        ok_mod = all(abs(abs(etas[b]) - abs(etas[f(b)])) < 1e-7 for b in range(1, p))
        ok_eta = all(abs(etas[b] - etas[f(b)]) < 1e-7 for b in range(1, p))         # eta itself equal
        ok_conj = all(abs(etas[b] - etas[f(b)].conjugate()) < 1e-7 for b in range(1, p))
        rel[name] = (ok_eta, ok_conj, ok_mod)

    # distinct values
    vals = [round(abs(etas[b]), 6) for b in range(1, p)]
    distinct_mod = len(set(vals))                       # distinct |eta| values
    distinct_eta = len({(round(etas[b].real,6), round(etas[b].imag,6)) for b in range(1,p)})

    # ---- Q3: concentration. orbit of the worst-modulus coset under normalizer-on-b ----
    bmax = max(range(1, p), key=lambda b: abs(etas[b]))
    Bval = abs(etas[bmax])
    # normalizer orbit of bmax
    orb = {f(bmax) for f in maps.values()}
    # is the argmax fixed (up to the coset it lives in)? compute coset reps
    # coset of b is b*mu_n
    def coset(b):
        return frozenset((b * y) % p for y in G)
    coset_bmax = coset(bmax)
    # which normalizer images land in the SAME coset (period value) as bmax
    same_coset = sum(1 for f in maps.values() if coset(f(bmax)) == coset_bmax)

    # how many distinct period-COSETS achieve the max modulus
    max_cosets = set()
    for b in range(1, p):
        if abs(abs(etas[b]) - Bval) < 1e-6:
            max_cosets.add(coset(b))
    n_max_cosets = len(max_cosets)

    # normalizer orbits on the set of m cosets: count orbits (the "effective DOF")
    reps = {}
    for b in range(1, p):
        reps.setdefault(coset(b), b)
    coset_reps = list(reps.values())
    # build action of neg, inv on cosets via reps
    seen = set()
    n_orbits = 0
    repset = set(coset_reps)
    # map a frequency to its coset-rep
    rep_of = {}
    for c, r in reps.items():
        for b in range(1, p):
            if coset(b) == c:
                rep_of[b] = r
    n_orbits = 0
    visited = set()
    for r in coset_reps:
        if r in visited: continue
        # orbit under group generated by neg, inv
        stack = [r]; orbit = set()
        while stack:
            x = stack.pop()
            rx = rep_of[x]
            if rx in orbit: continue
            orbit.add(rx)
            for f in maps.values():
                stack.append(f(x))
        visited |= orbit
        n_orbits += 1

    return dict(p=p, n=n, m=m, inv_closed=inv_closed, neg_closed=neg_closed,
                neginv_closed=neginv_closed, rel=rel, distinct_mod=distinct_mod,
                distinct_eta=distinct_eta, Bval=Bval, orb=len(orb),
                same_coset=same_coset, n_max_cosets=n_max_cosets,
                n_norm_orbits=n_orbits)

if __name__ == "__main__":
    cases = []
    # small enumerable: n=8,16,32; pick a few primes per n with n|(p-1)
    for n in [8, 16, 32]:
        cnt = 0
        c = n + 1
        while cnt < 3:
            if sympy.isprime(c) and (c - 1) % n == 0:
                cases.append((c, n)); cnt += 1
            c += n
    # also a couple "prize-shaped" primes p ~ n^2..n^3 to see m larger
    for n in [8, 16]:
        target = n**3
        c = target - (target % n) + 1
        while True:
            if sympy.isprime(c) and (c - 1) % n == 0:
                cases.append((c, n)); break
            c += n

    hdr = f"{'p':>7}{'n':>4}{'m':>5}  invcl negcl ninvcl | id(eta/conj/mod) neg inv neg.inv | dmod deta | B/sqrt(n) | normOrb | maxCos same"
    print(hdr)
    print("-" * len(hdr))
    for (p, n) in cases:
        r = run(p, n)
        def fmt(t):  # (eta,conj,mod)
            return "".join("1" if x else "0" for x in t)
        print(f"{r['p']:>7}{r['n']:>4}{r['m']:>5}  "
              f"{int(r['inv_closed'])}    {int(r['neg_closed'])}    {int(r['neginv_closed'])}   | "
              f"{fmt(r['rel']['id'])}            {fmt(r['rel']['neg'])} {fmt(r['rel']['inv'])} {fmt(r['rel']['neg.inv'])}    | "
              f"{r['distinct_mod']:>4} {r['distinct_eta']:>4} | "
              f"{r['Bval']/math.sqrt(n):>9.3f} | "
              f"{r['n_norm_orbits']:>5} (m/4={r['m']/4:.1f}) | "
              f"{r['n_max_cosets']:>3} {r['same_coset']}")
    print()
    print("LEGEND: rel triple = (eta_b==eta_{f(b)}, eta_b==conj(eta_{f(b)}), |eta_b|==|eta_{f(b)}|)")
    print("        normOrb = #orbits of the m cosets under <neg,inv> on frequency b.")
    print("        If normOrb ~ m/4 the normalizer cuts the period DOF by x4 (Katz floor analogue).")
    print("        maxCos = #distinct cosets achieving B; same = #of 4 norm-maps fixing the worst coset.")
