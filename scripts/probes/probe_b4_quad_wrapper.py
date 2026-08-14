#!/usr/bin/env python3
"""
PROBE (rule 2): the 4-element rung of the B_h-Sidon ladder for mu_n under the symmetric-function
lift. Extends the proven 3-element brick (UnitCircleSidonTriple: equal e1 + equal e3 -> equal triple,
with e2 free from conjugation).

For 4 roots of unity a,b,c,d on |x|=1 (conj x = 1/x), the elementary symmetric functions e1..e4
satisfy conjugate-reciprocal relations:
   conj(e_k) = e_{m-k} / e_m   (m=4)
so:
   conj(e1) = e3 / e4      (e3 free once e1, e4 fixed)
   conj(e2) = e2 / e4      (e2 is "self-conjugate up to e4": conj(e2)*e4 = e2)
   conj(e3) = e1 / e4
Therefore fixing (e1, e2, e4) DETERMINES e3 = conj(e1)*e4 = e4*conj(e1). e2 is NOT free (it must be
given) because conj(e2)*e4 = e2 only constrains e2 to a "real-up-to-e4" locus, not a single value.

HYPOTHESES TESTED (exact roots of unity, n=2..8, NEVER n=q-1 issue: this is the unit-circle abstract
Sidon fact, the thinness is in conj=inverse which needs |x|=1):
  A. Naive B_4-additive-Sidon from the sum alone: equal e1 -> equal quadruple? (expect MANY collisions)
  B. (e1, e4) fixed -> quadruple? (expect collisions: e2 not pinned)
  C. (e1, e2, e4) fixed -> quadruple? (expect ZERO collisions: the LANE)
  D. conjugation mechanism: conj(e1)*e4 == e3 exactly, and conj(e2)*e4 == e2 exactly?
"""
import itertools, cmath, math

def roots_of_unity(n):
    return [cmath.exp(2j*math.pi*k/n) for k in range(n)]

def esymm(t):
    a,b,c,d = t
    e1 = a+b+c+d
    e2 = a*b+a*c+a*d+b*c+b*d+c*d
    e3 = a*b*c+a*b*d+a*c*d+b*c*d
    e4 = a*b*c*d
    return (e1,e2,e3,e4)

def quant(z, scale=1e7):
    # quantize complex to compare multisets / equalities up to numerical error
    return (round(z.real*scale), round(z.imag*scale))

def multiset_key(t):
    return tuple(sorted(quant(z) for z in t))

EPS = 1e-6

for n in [2,3,4,5,6,8]:
    R = roots_of_unity(n)
    # all unordered 4-multisets (with repetition) of n-th roots of unity
    quads = list(itertools.combinations_with_replacement(range(n), 4))
    # group by various invariant keys
    from collections import defaultdict
    byA = defaultdict(list)   # key = e1 only
    byB = defaultdict(list)   # key = (e1,e4)
    byC = defaultdict(list)   # key = (e1,e2,e4)
    mechfail = 0
    for q in quads:
        t = tuple(R[i] for i in q)
        e1,e2,e3,e4 = esymm(t)
        mk = multiset_key(t)
        byA[(quant(e1),)].append(mk)
        byB[(quant(e1),quant(e4))].append(mk)
        byC[(quant(e1),quant(e2),quant(e4))].append(mk)
        # mechanism: conj(e1)*e4 == e3 ; conj(e2)*e4 == e2
        if abs(e1.conjugate()*e4 - e3) > EPS: mechfail += 1
        if abs(e2.conjugate()*e4 - e2) > EPS: mechfail += 1

    def collisions(d):
        c = 0; tot = 0
        for k, mks in d.items():
            uniq = set(mks)
            tot += len(mks)
            if len(uniq) > 1:
                c += len(mks)  # count members of multi-valued buckets
        return c, tot
    cA,tA = collisions(byA)
    cB,tB = collisions(byB)
    cC,tC = collisions(byC)
    print(f"n={n:2d}  #quads={len(quads):4d}  "
          f"A(e1):coll={cA:4d}/{tA}  B(e1,e4):coll={cB:4d}/{tB}  "
          f"C(e1,e2,e4):coll={cC:4d}/{tC}  mechfail={mechfail}")
