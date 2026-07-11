#!/usr/bin/env python3
"""
Probe (#444 / I031 metric-entropy): does the distinct-MODULUS alphabet |{‖η_b‖ : b≠0}| collapse
STRICTLY BELOW the coset count (q-1)/n at prize scale, and is any such collapse THINNESS-ESSENTIAL?

Context. I031DistinctPeriodCount proves |{‖η_b‖}| ≤ (q-1)/n via the coset-label factoring (η constant
on μ_n-cosets, (q-1)/n cosets). The Lean theorem is only ≤. The actual prize objective is the SUP of
‖η_b‖; the union-bound metric entropy is log(alphabet size). If the modulus alphabet is STRICTLY
smaller than (q-1)/n (extra cross-coset modulus collisions), the metric entropy is < log((q-1)/n),
which would TIGHTEN the I031 union bound. We measure:
  (a) M2 = #distinct ‖η_b‖  vs  Mcoset = (q-1)/n         [is M2 < Mcoset? by how much?]
  (b) M1 = #distinct complex η_b values                  [coset structure already collapses to this]
  (c) THINNESS test: same n at varying thickness β=log_n(q). Rule 3 demands any prize lever be
      thinness-ESSENTIAL (false in thick window). If the collapse ratio M2/Mcoset is the SAME for
      thin and thick, it is thickness-INVARIANT => NOT a prize lever (rule 3), log it as a constraint.
PROPER thin μ_n: n=2^a, n|p-1, p≫n^3 + a structured Fermat-type, NEVER n=q-1.
"""
import cmath, sys

def is_prime(m):
    if m < 2: return False
    i = 2
    while i*i <= m:
        if m % i == 0: return False
        i += 1
    return True

def primitive_root(p):
    if p == 2: return 1
    phi = p-1; fac=set(); x=phi; d=2
    while d*d <= x:
        while x%d==0: fac.add(d); x//=d
        d += 1
    if x>1: fac.add(x)
    for g in range(2,p):
        if all(pow(g, phi//q, p)!=1 for q in fac): return g
    return None

def measure(n, p):
    g = primitive_root(p)
    step = (p-1)//n
    mu = [pow(g, (k*step)%(p-1), p) for k in range(n)]
    assert len(set(mu))==n
    w = 2.0*cmath.pi/p
    def eta(b):
        s=0j
        for x in mu: s += cmath.exp(1j*w*((b*x)%p))
        return s
    vals=set(); mods=set()
    for b in range(1,p):
        e=eta(b)
        vals.add((round(e.real,6), round(e.imag,6)))
        mods.add(round(abs(e),6))
    return len(vals), len(mods), (p-1)//n

def run(label, cases):
    print(f"\n=== {label} ===")
    print(f"{'n':>5} {'p':>9} {'beta':>5} {'(q-1)/n':>9} {'#vals':>8} {'#|eta|':>8} "
          f"{'val/cos':>8} {'mod/cos':>8}")
    rows=[]
    for (n,p) in cases:
        mv, mm, mc = measure(n,p)
        beta = round(cmath.log(p).real / cmath.log(n).real, 2)
        print(f"{n:>5} {p:>9} {beta:>5} {mc:>9} {mv:>8} {mm:>8} "
              f"{mv/mc:>8.3f} {mm/mc:>8.3f}")
        rows.append((n,p,beta,mc,mv,mm))
    return rows

def find_prime(n, target):
    p = ((target//n)+1)*n + 1
    while not is_prime(p): p += n
    return p

if __name__ == "__main__":
    # THIN prize-regime: p >> n^3 (beta ~ 3-4+)
    thin=[]
    for a in range(2,6):
        n=2**a
        thin.append((n, find_prime(n, max(n**3, 2000))))
    # also a Fermat-type structured prime
    if is_prime(257): thin.append((16, 257))   # 257 = 2^8+1, n=16 | 256
    rows_thin = run("THIN  (p >> n^3, prize regime)", thin)

    # THICK control: beta ~ 2.3 (just above n^2), same n's. Rule-3 essentiality test.
    thick=[]
    for a in range(2,6):
        n=2**a
        thick.append((n, find_prime(n, int(n**2.3))))
    rows_thick = run("THICK (beta ~ 2.3, control)", thick)

    # VERDICT
    print("\n--- VERDICT ---")
    def ratios(rows):
        return [ (n, round(mm/mc,3)) for (n,p,b,mc,mv,mm) in rows ]
    print("thin  mod/cos:", ratios(rows_thin))
    print("thick mod/cos:", ratios(rows_thick))
    # is the collapse ratio essentially identical thin vs thick? (thickness-invariant => not a lever)
    sys.exit(0)
