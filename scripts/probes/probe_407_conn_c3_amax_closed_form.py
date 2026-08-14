#!/usr/bin/env python3
"""
#407 C3 (part 4) — closed form of a_max^0, and the EXACT relation to the count-lane structure.

Findings so far:
  - r=2:  a_max^0 = n EXACTLY (= n^{r-1}).  q-independent.
  - r>=3: a_max^0 < (2r-1)!! (so the energy bound E_r <= a_max^0 n^r is STRICTLY WEAKER than Wick).
          a_max^0 / n^{r-1} = constant per n,r (0.328 for n=8, 0.176 for n=16, 0.091 for n=32 at r=3,4).
          Note 0.328 ~ 21/64, 0.176~45/256? 45/256=0.1758 yes; 0.091~93/1024=0.0908 yes.

GOAL: identify WHICH sum c achieves a_max^0, and tie it to the count-lane "spurious/antipodal"
structure, to see if there is an IDENTITY linking a_max (energy upper-bound driver) to the count.

KEY HYPOTHESIS: a_max^0 is achieved at c=0 (the all-antipodal-cancellation sum), and equals the
number of r-tuples summing to 0 in Z[zeta_n] = the char-0 "r-fold zero-sum count" = closely tied
to (r-1)-fold convolution diagonal. For r=2: tuples (x,y) with x+y=0 <=> y=-x: exactly n of them.
=> a_max(c=0) = n for r=2. Test for r>=3 whether a_max is at c=0 and what it counts.
"""
import sys, itertools
from collections import Counter

def char0_coord(exps, n):
    half = n//2; v=[0]*half
    for e in exps:
        e%=n
        if e<half: v[e]+=1
        else: v[e-half]-=1
    return tuple(v)

def char0_a(n, r):
    a=Counter()
    for tup in itertools.product(range(n), repeat=r):
        a[char0_coord(tup,n)] += 1
    return a

def main():
    print("="*100)
    print("C3 part 4: closed form of a_max^0 and which c achieves it (tie to count-lane structure)")
    print("="*100)
    zero = None
    for mu in [3,4,5]:
        n=2**mu
        zero = tuple([0]*(n//2))
        for r in [2,3,4]:
            if n**r > 5_000_000: continue
            a=char0_a(n,r)
            am=max(a.values())
            argmax_is_zero = (a.get(zero,-1)==am)
            a_zero = a.get(zero,0)
            # how many distinct c achieve the max?
            n_argmax = sum(1 for v in a.values() if v==am)
            print(f"n={n:>3} r={r}: a_max^0={am:>5}  a(c=0)={a_zero:>5}  "
                  f"argmax_at_0={str(argmax_is_zero):>5}  #argmax={n_argmax:>4}  "
                  f"a_max/n^(r-1)={am/n**(r-1):.4f}  a(0)/n^(r-1)={a_zero/n**(r-1):.4f}")
    print()
    print("Conjectured closed forms to test (r=2 proven a_max=n=a(0)):")
    print("  a(c=0) for r-fold = # ordered r-tuples of mu_n summing to 0 in Z[zeta_n].")
    print("  For dyadic n: r=2 -> n (antipodal pairs).  Check r=3: is a(0) the max?")
    # tabulate a(0) closed form guess: for r-fold zero-sum, Lam-Leung => sums of +- pairs.
    # r=2: n.  Let's just print a(0) sequence.

if __name__ == "__main__":
    main()
