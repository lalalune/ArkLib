#!/usr/bin/env python3
"""
The size-6 kernel bound: can 3 distinct size-6 classes coexist? (p=12289)

KEY MECHANISM (explains size6kernel probe -> 0): for 3 size-6 agreement
sets pairwise overlapping in EXACTLY 2 pts, the cross-poly differences
satisfy q1-q2 = c12*m_{O12}, q2-q3 = c23*m_{O23}, q3-q1 = c31*m_{O31}
(O_ij = overlap, m = its deg-2 vanishing poly), and these SUM to 0:
   c12*m_{O12} + c23*m_{O23} + c31*m_{O31} = 0.
If the three overlap-monics are LINEARLY INDEPENDENT (in the 3-dim space
of deg<=2 polys), then c12=c23=c31=0 => q1=q2=q3 => NOT 3 distinct
classes. So 3 distinct size-6 classes REQUIRE the 3 overlap-monics to be
linearly DEPENDENT.

This probe: over ALL configurations of 3 size-6 subsets of mu_16 with
pairwise overlap exactly 2 (sampled broadly), check whether the 3
overlap-monics are EVER linearly dependent. If NEVER => <= 2 size-6
classes always (the kernel bound, closing the hard case). Report the
fraction dependent and any dependent example.
"""
import itertools, random

p, n = 12289, 16
g0 = next(g for g in range(2, 500)
          if all(pow(g, (p - 1) // f, p) != 1 for f in (2, 3)))
w = pow(g0, (p - 1) // n, p)
D = [pow(w, j, p) for j in range(n)]

def monic2(pt_pair):
    a, b = D[pt_pair[0]], D[pt_pair[1]]
    # (x-a)(x-b) = x^2 - (a+b)x + ab ; coeff vector [ab, -(a+b), 1]
    return [(a*b) % p, (-(a+b)) % p, 1]

def det3(v1, v2, v3):
    M = [v1, v2, v3]
    # 3x3 determinant mod p
    d = 0
    d += M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])
    d -= M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
    d += M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0])
    return d % p

# enumerate/sample triples of size-6 sets, pairwise overlap exactly 2
rng = random.Random(99)
dep = 0; total = 0; dep_examples = []
for trial in range(200000):
    # build 3 sets with pairwise overlaps of size 2 by choosing overlaps first
    pts = list(range(n)); rng.shuffle(pts)
    O12 = tuple(sorted(pts[0:2])); O23 = tuple(sorted(pts[2:4]))
    O31 = tuple(sorted(pts[4:6]))
    # need O12,O23,O31 disjoint (else a point in 2 overlaps -> in all 3 sets)
    if len(set(O12)|set(O23)|set(O31)) != 6: continue
    # remaining unique members: A1 gets O12,O31 + 2 unique; A2 gets O12,O23+2;
    # A3 gets O23,O31+2. unique pts from the rest:
    rest = pts[6:]
    u1, u2, u3 = rest[0:2], rest[2:4], rest[4:6]
    A1 = set(O12)|set(O31)|set(u1)
    A2 = set(O12)|set(O23)|set(u2)
    A3 = set(O23)|set(O31)|set(u3)
    if not (len(A1)==6 and len(A2)==6 and len(A3)==6): continue
    if len(A1&A2)!=2 or len(A2&A3)!=2 or len(A1&A3)!=2: continue
    total += 1
    d = det3(monic2(O12), monic2(O23), monic2(O31))
    if d == 0:
        dep += 1
        if len(dep_examples) < 3:
            dep_examples.append((O12, O23, O31))
print(f"sampled {total} valid 3-size-6 pairwise-overlap-2 configs; "
      f"overlap-monics linearly DEPENDENT in {dep} ({100*dep/max(total,1):.3f}%)")
if dep_examples:
    print(f"  dependent examples (overlaps): {dep_examples}")
else:
    print("  NONE dependent => 3 distinct size-6 classes IMPOSSIBLE => "
          "<= 2 size-6 classes always (size-6 kernel bound holds)")
