#!/usr/bin/env python3
"""
probe_407_realizable_disjoint_check.py  (#407)

Final realizability audit (rule 6): confirm the n=32 break witness g in {-2..2}^16 is genuinely
realizable as g_j = contribZ A j - contribZ B j with A,B DISJOINT signed-point Finsets, matching
the chain's `disjoint_equal_sum_antipodal_int_bounded` hypothesis. (If disjointness obstructed some
g, the witness might be off-spec even at height 2.)

Construction: for each index j with target g_j = a_j - b_j (a_j,b_j in {-1,0,1}):
  contribZ A j = a_j  via fiber:  a_j=+1 -> A has (j,T); a_j=-1 -> A has (j,F); a_j=0 -> A no j-point.
  contribZ B j = b_j  via fiber:  b_j=+1 -> B has (j,T); b_j=-1 -> B has (j,F); b_j=0 -> B no j-point.
A and B are disjoint as POINT SETS iff they never share the SAME (j,bool). With the canonical decomp
  g_j= 2 -> a_j=+1 (A:(j,T)), b_j=-1 (B:(j,F))  : different bools -> disjoint OK
  g_j=-2 -> a_j=-1 (A:(j,F)), b_j=+1 (B:(j,T))  : different bools -> disjoint OK
  g_j= 1 -> a_j=+1 (A:(j,T)), b_j=0  (B: none)  : disjoint OK
  g_j=-1 -> a_j=-1 (A:(j,F)), b_j=0             : disjoint OK
  g_j= 0 -> a_j=0, b_j=0                         : disjoint OK
So at EVERY index the chosen A-point and B-point differ in the bool when both present -> A,B disjoint
always. Verify explicitly + check the equal-sum identity sum_{A} sval = sum_{B} sval holds (it must,
since contribZ A - contribZ B = g and sum g_j omega^j = 0).
"""
import math

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

def primitive_2pow_root(p, m):
    n = 1 << m
    e = (p - 1) // n
    for base in range(2, p):
        r = pow(base, e, p)
        if pow(r, n // 2, p) != 1 and pow(r, n, p) == 1:
            return r
    return None

# sval of point (j,b): isgn=+1 if b=T else -1; value = isgn * omega^j  (half-basis, ζ=omega)
def build_AB(g):
    A = set(); B = set()
    for j, v in enumerate(g):
        if v == 2:   A.add((j, True));  B.add((j, False))
        elif v == -2: A.add((j, False)); B.add((j, True))
        elif v == 1:  A.add((j, True))
        elif v == -1: A.add((j, False))
        # v==0: nothing
    return A, B

def contribZ(S, j):
    s = 0
    for (jj, b) in S:
        if jj == j:
            s += 1 if b else -1
    return s

def main():
    cases = [
        (32801, [-2,-1,2,-1,1,0,2,2,-2,-2,-2,-2,-2,-2,-2,-2]),
        (1048609, [-1,-1,0,2,1,1,-1,2,-2,-2,-2,-2,-2,-2,-2,-2]),
        (33554593, [1,0,0,-1,0,-1,-2,-1,-2,-2,-2,-2,-1,-2,1,-1]),
    ]
    m=5; N=16
    for p, g in cases:
        om = primitive_2pow_root(p, m)
        A, B = build_AB(g)
        disjoint = len(A & B) == 0
        # contribZ A - contribZ B == g ?
        ok = all(contribZ(A, j) - contribZ(B, j) == g[j] for j in range(N))
        # equal-sum: sum_A sval == sum_B sval mod p, with sval(j,b)= (+/-1)*omega^j
        def svalsum(S):
            t = 0
            for (j, b) in S:
                t = (t + (1 if b else -1) * pow(om, j, p)) % p
            return t
        eq = (svalsum(A) - svalsum(B)) % p
        beta = math.log(p, 32)
        print("p=%10d beta=%.2f  disjoint(A,B):%s  contribZ-diff==g:%s  |A|=%d |B|=%d  sval(A)-sval(B) mod p=%d  -> %s" % (
            p, beta, disjoint, ok, len(A), len(B), eq,
            "REALIZABLE contribZ-difference with DISJOINT A,B (on-spec for the chain)" if (disjoint and ok and eq==0) else "OFF-SPEC"))

if __name__ == "__main__":
    main()
