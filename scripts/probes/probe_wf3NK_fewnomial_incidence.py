#!/usr/bin/env python3
"""
wf-NK (#444): KHOVANSKII / FEWNOMIAL lens on the binding over-determined incidence I(n).

VERDICT: REFUTED as a TIGHT a-priori bound on I(n) (with a precise, two-sided reason).
The fewnomial framework *formally applies* (the binding system IS (k+2)-sparse, confirmed) but
every fewnomial/Descartes/uncertainty cap is either exponentially loose or undershoots, and the
sharpest cyclic-group fewnomial bound (Tao uncertainty) is VACUOUS on the prize's n=2^mu domain.

--------------------------------------------------------------------------------------------
THE OBJECT (FarCosetExplosion, NH brick _wf2NH_overdet_single_gamma.lean):
  I(a,b;r) = #{ gamma : x^a + gamma*x^b agrees with SOME RS[k] codeword on >= n-r points of mu_n }.
At the binding radius r*, size = n-r* (the witness size), and the per-witness condition is
over-determined in gamma (NH: <= 1 gamma per witness). So I = |union of forced single gammas|.

THE FEWNOMIAL REFORMULATION (this lane):
  gamma is BAD iff the LAURENT polynomial  f_gamma(X) = X^a + gamma*X^b - h(X),  h in RS[k] (deg<k),
  vanishes on >= n-r points of mu_n.  Support of f_gamma = {a, b, 0,1,...,k-1}: at most k+2
  DISTINCT exponents.  Khovanskii fewnomial theory bounds solution counts of a SPARSE system by
  the NUMBER OF MONOMIALS (m=k+2), degree-free and field-free -- exactly this regime.

MEASURED BINDING DATA (exact, p-independent; n=16 value is in-tree verified, e167dd9de):
  n=8  k=2: r*=4 size=4 binder(a,b)=(5,2)  I=9   support {0,1,2,5}        m=4=k+2
  n=12 k=3: r*=6 size=6 binder(a,b)=(6,4)  I=13  support {0,1,2,4,6}      m=5=k+2
  n=16 k=4: r*=10 size=6 binder(a,b)=(10,4) I=89  support {0,1,2,3,4,10}  m=6=k+2  (I=89 is PRIME)

FEWNOMIAL BOUNDS vs MEASURED I:
  Khovanskii classical 2^C(m,2)*(n_var+1)^m (1 eliminated gamma-variable, n_var=1):
       1024 / 32768 / 2097152   -- OVERSHOOTS I by 100x-24000x, GROWS EXPONENTIALLY in k. Vacuous.
  Descartes-on-circle / cyclic 2(m-1)=2(k+1):  6 / 8 / 10  -- UNDERSHOOTS I=9/13/89.
       (Not a valid upper bound: it caps ROOTS-PER-gamma, not the COUNT of gamma.)
  Trivial union C(n,size): 70 / 924 / 8008 -- valid but loose (=NH's bound), p-free, degree-free,
       but useless for delta* (gives delta*->1).

WHY THE LENS FAILS (the precise wall):
  (1) I(n) is NOT a fewnomial-polynomial sequence: I(16)=89 is PRIME; the old (n/2-1)^2 closed form
      (9,25,49) is REFUTED by it (matches n=8 only by coincidence). A degree-free fewnomial bound is
      a POLYNOMIAL in (n,k); a non-polynomial, prime-valued target cannot be matched tightly.
  (2) The fewnomial cap governs the per-gamma ROOT count, but I is a UNION over C(n,size) witnesses.
      The distinctness collapse (89 distinct out of 8008 size-6 witnesses for n=16) is governed by the
      ADDITIVE/MULTIPLICATIVE structure of mu_n (how the C(n,size) forced gammas COINCIDE) -- NOT by
      the monomial count.  This re-enters the BGK/character-cancellation regime through the back door:
      fewnomial theory is BLIND to coincidence of distinct witnesses' gammas.
  (3) The 2^mu CYCLIC-UNCERTAINTY COLLAPSE (in-tree 6507e61aa): the sharpest fewnomial-on-a-cyclic-
      group bound (Tao uncertainty: a nonzero fn on Z/n with t nonzero Fourier coeffs has <= n-t
      zeros) requires n PRIME.  For n=2^mu it is VACUOUS.  The prize's defining smooth-domain feature
      (n=2^mu highly composite) is exactly what defeats the fewnomial/uncertainty lens.

TAG: refuted (fewnomial lens does NOT yield a tight degree-free p-free bound on I(n)); the formal
     applicability + the (k+2)-sparsity + the precise failure mode are proven-per-fixed-n facts.
"""
import math

# (n, k, size, binder_a, binder_b, I)  -- exact binding data (n=16 value in-tree verified e167dd9de)
BIND = [(8, 2, 4, 5, 2, 9), (12, 3, 6, 6, 4, 13), (16, 4, 6, 10, 4, 89)]


def support(n, k, a, b):
    return sorted(set(range(k)) | {a % n, b % n})


def main():
    print("wf-NK FEWNOMIAL lens on binding over-determined incidence I(n)\n")
    print(f"{'n':>3} {'k':>2} {'size':>4} {'(a,b)':>7} {'I':>4} | "
          f"{'support':>22} {'m':>2} {'Khov':>9} {'Desc':>5} {'C(n,sz)':>8}")
    for n, k, size, a, b, I in BIND:
        sup = support(n, k, a, b)
        m = len(sup)
        khov = 2 ** math.comb(m, 2) * 2 ** m          # 1 eliminated gamma-variable
        desc = 2 * (m - 1)
        cns = math.comb(n, size)
        print(f"{n:>3} {k:>2} {size:>4} {str((a, b)):>7} {I:>4} | "
              f"{str(sup):>22} {m:>2} {khov:>9} {desc:>5} {cns:>8}")

    print("\n--- ratios (tight if ~1) ---")
    for n, k, size, a, b, I in BIND:
        m = len(support(n, k, a, b))
        khov = 2 ** math.comb(m, 2) * 2 ** m
        desc = 2 * (m - 1)
        cns = math.comb(n, size)
        print(f"n={n}: I={I:3}  Khov/I={khov / I:10.1f} (OVERSHOOT)  "
              f"Desc/I={desc / I:.2f} (UNDERSHOOT, invalid bound)  "
              f"C(n,sz)/I={cns / I:.1f} (loose)")

    print("\n--- I(n) is NOT a fewnomial-polynomial: (n/2-1)^2 closed form REFUTED ---")
    for n, k, size, a, b, I in BIND:
        guess = (n // 2 - 1) ** 2
        print(f"n={n}: I={I}  (n/2-1)^2={guess}  {'MATCH' if guess == I else 'MISS'}"
              + ("  [I=89 is PRIME -> no polynomial fewnomial form]" if I == 89 else ""))

    print("\n--- 2^mu cyclic-uncertainty (Tao zeros<=n-t) requires n PRIME -> VACUOUS here ---")
    for n in (8, 16, 32):
        print(f" n={n}=2^{int(math.log2(n))}: prime={n == 2}  -> sharpest fewnomial-cyclic cap inapplicable")

    print("\nVERDICT: fewnomial lens REFUTED as a tight degree-free/p-free bound on I(n).")
    print("  Loosest valid bound = C(n,size) (= NH union bound); fewnomial adds nothing beyond it.")
    print("  The distinctness/coincidence of witness gammas is the BGK-residual the lens cannot see.")


if __name__ == '__main__':
    main()
