#!/usr/bin/env python3
"""
wf407_T389-03-phase_inertness.py  — Thread T389-03 (389-T03)

GOAL: settle part (3) of the actionable — is the EXACT cos=1 phase alignment at the worst
frequency b* a STRUCTURALLY INERT fact (cannot bound B without an external analytic input),
or can it be combined with a NON-MOMENT input to bound B = max_{b!=0} |eta_b(mu_n)|?

Setup (n=2^mu, mu_n = order-n subgroup of F_p^*, z generator, half = mu_{n/2}=<z^2>):
  A = eta_{b*}(mu_{n/2}),  B = eta_{b* z}(mu_{n/2}),  worst-period  B(mu_n) = |A+B| (untwisted).
  Alignment (PROVEN exact): at b*, A,B real and same sign => B(mu_n)=|A|+|B|.

We test, EXACTLY (full coset-rep scans, no sampling), three candidate "alignment + X" levers:

  LEVER 1  (alignment as a CEILING from level n/2):  is  B(mu_n) <= 2 * B(mu_{n/2}) ?
           If TRUE always => alignment gives a clean doubling CEILING (tower up-bound), which
           combined with a base B(mu_2)=O(1) would give B(mu_n)<=2^{mu-1} (USELESS, far above
           sqrt(n log)).  Check if the constant is < 2 (would be a real descent) or = 2 / > .. .

  LEVER 2  (alignment + the EXACT energy E_2 magnitude pin, non-moment):  the alignment says
           B = |A|+|B| with A,B two specific half-periods.  Combined with |A|^2+|B|^2 <= (energy
           bound at level n/2) does it cap |A|+|B|?  We measure  (|A|+|B|)^2 / (|A|^2+|B|^2)  =
           1 + 2|A||B|/(|A|^2+|B|^2) in [1,2].  Alignment forces the cross term POSITIVE but its
           SIZE (|A||B|) is exactly the open quantity.  Is |A||B| bounded by anything structural?

  LEVER 3  (THE decisive test):  can alignment + magnitude-only facts (E_2 pin, Parseval) ever
           give a bound BELOW the trivial Cauchy-Schwarz  B <= sqrt(2(|A|^2+|B|^2)) ?  The point:
           alignment makes B = |A|+|B| EXACTLY (the MAX of the two parallelogram branches), so it
           gives the WORST (largest) value compatible with the magnitudes |A|,|B|.  Hence alignment
           pushes B UP, not down: it is the obstruction, not the lever.  Verify B(mu_n) sits at the
           UPPER parallelogram branch (=|A|+|B|), never the lower (||A|-|B||).

CONCLUSION metric: is there ANY lever where alignment yields B < (trivial magnitude bound)?
"""

import math
import numpy as np
from sympy import isprime, primitive_root


def find_prime(n, beta_target):
    target = int(round(n ** beta_target))
    p = target - (target % n) + 1
    if p <= target:
        p += n
    while not isprime(p) or ((p - 1) // n % 2 == 0 and pow(2, 0) and _odd_part((p - 1) // n) == 1):
        p += n
    return p


def _odd_part(m):
    while m % 2 == 0 and m > 0:
        m //= 2
    return m


def subgroup_data(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    H = np.array([pow(h, i, p) for i in range(n)], dtype=np.int64)
    return g, h, H


def coset_reps(p, n, g):
    m = (p - 1) // n
    return np.array([pow(g, j, p) for j in range(m)], dtype=np.int64)


def Sb(p, H, b):
    ang = (2.0 * math.pi / p) * ((b * H) % p)
    return np.exp(1j * ang).sum()


def worst(p, n, g, H):
    """Return (b*, |S_b*|) exact over all m coset reps."""
    reps = coset_reps(p, n, g)
    best_b, best = 0, -1.0
    for b in reps.tolist():
        if b == 0:
            continue
        v = abs(Sb(p, H, b))
        if v > best:
            best, best_b = v, b
    return best_b, best


def analyze(n, p):
    g, h, H = subgroup_data(p, n)
    z = h
    half = n // 2
    Hhalf = np.array([pow(h, 2 * i, p) for i in range(half)], dtype=np.int64)
    zHhalf = (z * Hhalf) % p

    bstar, Bfull = worst(p, n, g, H)
    A = Sb(p, Hhalf, bstar)
    Bc = Sb(p, zHhalf, bstar)
    a, b = abs(A), abs(Bc)

    # worst over the half-subgroup itself (its own B(mu_{n/2}))
    _, Bhalf = worst(p, half, g, Hhalf) if half >= 2 else (0, 1.0)

    upper_branch = a + b          # |A+B| at alignment
    lower_branch = abs(a - b)     # ||A|-||B|| (twisted magnitude)
    cs_bound = math.sqrt(2 * (a * a + b * b))  # Cauchy-Schwarz on |A+B|

    return dict(
        n=n, p=p, bstar=bstar, Bfull=Bfull, a=a, b=b, Bhalf=Bhalf,
        # LEVER 1: doubling ceiling constant
        L1_ratio=Bfull / Bhalf if Bhalf > 0 else float('nan'),
        # which of A,B equals the half-worst? (is b* a maximizer at level n/2?)
        a_over_half=a / Bhalf if Bhalf > 0 else float('nan'),
        b_over_half=b / Bhalf if Bhalf > 0 else float('nan'),
        # LEVER 2: cross-term inflation factor in [1,2]
        L2_inflate=(upper_branch ** 2) / (a * a + b * b) if (a * a + b * b) > 0 else float('nan'),
        # LEVER 3: is Bfull at the UPPER branch (alignment pushes UP)?
        upper_branch=upper_branch, lower_branch=lower_branch, cs_bound=cs_bound,
        at_upper=abs(Bfull - upper_branch) < 1e-6 * max(1.0, Bfull),
        # gap between Bfull and the trivial magnitude bound (CS): alignment SATURATES CS iff a==b
        cs_slack=cs_bound - Bfull,
    )


def main():
    print("=" * 92)
    print("T389-03  phase alignment: STRUCTURALLY INERT or a lever?  (exact, full coset scan)")
    print("=" * 92)

    rows = []
    for n in [8, 16, 32]:
        for beta in (2.0, 4.0):
            p = find_prime(n, beta)
            m = (p - 1) // n
            if m * n > 40_000_000:
                continue
            r = analyze(n, p)
            rows.append(r)
            print(f"\n[ n={n}  p={p}  beta~{math.log(p)/math.log(n):.2f}  m={m} ]")
            print(f"   B(mu_n)={r['Bfull']:.4f}   B(mu_n/2)={r['Bhalf']:.4f}")
            print(f"   A=|eta_b*(mu_n/2)|={r['a']:.4f}   B=|eta_b*z(mu_n/2)|={r['b']:.4f}")
            print(f"   LEVER1  B(n)/B(n/2) = {r['L1_ratio']:.4f}   (a/Bhalf={r['a_over_half']:.3f}, "
                  f"b/Bhalf={r['b_over_half']:.3f})")
            print(f"   LEVER2  (|A|+|B|)^2/(|A|^2+|B|^2) = {r['L2_inflate']:.4f}  (in [1,2]; 2 iff |A|=|B|)")
            print(f"   LEVER3  Bfull at UPPER branch(|A+B|)={r['at_upper']}   "
                  f"upper={r['upper_branch']:.4f} lower={r['lower_branch']:.4f}  "
                  f"CS-bound={r['cs_bound']:.4f}  CS-slack={r['cs_slack']:.4f}")

    print("\n" + "=" * 92)
    print("VERDICT METRICS")
    print("=" * 92)
    l1 = [r['L1_ratio'] for r in rows if not math.isnan(r['L1_ratio'])]
    print(f" LEVER1 doubling ceiling B(n)<=c*B(n/2): max c = {max(l1):.4f}  "
          f"(<2 => real descent; >=2 => useless / refuted)")
    print(f"        -> ceiling holds with c<2 in ALL cases: {all(c < 2.0 for c in l1)}  "
          f"(but tower of c~{max(l1):.2f} over mu levels = {max(l1):.2f}^mu, NOT sqrt(n log))")
    print(f" LEVER2 cross inflation in [1,2] always: "
          f"{all(1.0 - 1e-9 <= r['L2_inflate'] <= 2.0 + 1e-9 for r in rows)}  "
          f"(range [{min(r['L2_inflate'] for r in rows):.3f}, {max(r['L2_inflate'] for r in rows):.3f}]); "
          f"the SIZE |A||B| is the open quantity, alignment only fixes its SIGN +")
    print(f" LEVER3 Bfull ALWAYS at UPPER (max) parallelogram branch: "
          f"{all(r['at_upper'] for r in rows)}")
    print(f"        => alignment yields the LARGEST B compatible with |A|,|B|: it pushes B UP.")
    print(f"        CS-slack >= 0 always (CS is an UPPER bound, never beaten by alignment): "
          f"{all(r['cs_slack'] >= -1e-9 for r in rows)}")
    print()
    print(" INTERPRETATION:")
    print("  - LEVER1: the doubling CEILING B(n)<=2 B(n/2) is the parallelogram UP-bound (drop")
    print("    |A-B|^2>=0 + alignment); but the constant approaches 2 and the tower gives 2^mu,")
    print("    EXPONENTIALLY WORSE than the sqrt(n log) target. (= the refuted-descent's dual.)")
    print("  - LEVER2: alignment fixes the cross term SIGN (+), the prize is its SIZE |A||B|;")
    print("    that size is governed by E_2 / equidistribution = the SAME analytic wall.")
    print("  - LEVER3: alignment selects the MAXIMAL branch |A|+|B|, i.e. it is the OBSTRUCTION")
    print("    (worst-case mechanism), not a downward lever. No magnitude-only fact + alignment")
    print("    beats Cauchy-Schwarz. => STRUCTURALLY INERT without an external analytic input.")


if __name__ == "__main__":
    main()
