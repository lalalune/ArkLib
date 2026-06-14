"""n=16 GROUND TRUTH at BabyBear: full C(16,9) interpolation census of the
marginal (agree-exactly-9) layer for w = X^10 + lam X^8, lam = -z*, z* = zeta^4.
Then exact (B,O,sigma)-set equality against the general engine at s=8,
plus lemma checks (L4 xi not in mu_16 u {0}; L6 free negation; witness layer = 3).
"""
from itertools import combinations
import sys
sys.path.insert(0, '/tmp/genlaw')
from engine import run

P = 15 * (1 << 27) + 1
g0 = 31
s, n = 8, 16
h16 = pow(g0, (P - 1) // n, P)
H = [pow(h16, i, P) for i in range(n)]
assert len(set(H)) == n and pow(h16, n, P) == 1 and pow(h16, s, P) == P - 1
ZS = H[s // 2]                       # z* = zeta^4, the canonical 4th root
assert pow(ZS, 2, P) == P - 1        # z*^2 = -1
LAM = P - ZS                         # lam = -z*
w = [(pow(x, s + 2, P) + LAM * pow(x, s, P)) % P for x in H]

# --- census: all 9-subsets T; interpolant deg < 8 <=> X^8-coefficient = 0 ---
def topcoef(idx):
    tot = 0
    for i in idx:
        num = w[i]
        den = 1
        for j in idx:
            if j != i:
                den = den * ((H[i] - H[j]) % P) % P
        tot = (tot + num * pow(den, P - 2, P)) % P
    return tot

def interp_eval(idx, x):
    tot = 0
    for i in idx:
        num = w[i]
        nm, den = 1, 1
        for j in idx:
            if j != i:
                nm = nm * ((x - H[j]) % P) % P
                den = den * ((H[i] - H[j]) % P) % P
        tot = (tot + num * nm * pow(den, P - 2, P)) % P
    return tot

agreesets = set()
for T in combinations(range(n), 9):
    if topcoef(T) == 0:
        full = frozenset(i for i in range(n)
                         if interp_eval(T, H[i]) == w[i])
        agreesets.add(full)

marg = sorted(x for x in agreesets if len(x) == 9)
wit = sorted(x for x in agreesets if len(x) >= 10)
print(f"[GT] distinct codewords with agreement >= 9: {len(agreesets)}")
print(f"[GT] marginal (exactly 9): {len(marg)}   witness (>=10): "
      f"{[len(x) for x in wit]} -> {len(wit)} witnesses")
assert len(marg) == 16 and len(wit) == 3 and all(len(x) == 10 for x in wit)
print("[GT] C19 ground truth REPRODUCED: 19 = 3 + 16")

# --- extract (B, O, sigma) from each marginal element; compare with engine ---
data = set()
for T in marg:
    B, O, D = [], [], []
    for z in range(s):
        a, b = z in T, (z + s) in T
        if a and b:
            B.append(z)
        elif a:
            O.append(z); D.append(0)
        elif b:
            O.append(z); D.append(1)
    assert len(B) == s // 2 - 1 and len(O) == 3, (B, O)
    d = [x ^ D[0] for x in D]                     # canonicalize d1 = 0
    sig = (d[1], d[2], d[1] ^ d[2])
    data.add((frozenset(B), tuple(O), sig))
    # L4: xi = -(x1+x2+x3) not in mu_16 and not 0
    X = [H[(O[i] + s * D[i]) % n] for i in range(3)]
    xi = (-(X[0] + X[1] + X[2])) % P
    assert xi != 0 and xi not in H, "L4 FAILS at s=8!"
    # the error's 4th linear root really is xi (and -xi gives the negated elt)
print("[GT] L4 holds on all 16 data elements (xi not in mu_16 u {0})")

R = run(8)
eng = {(B, O, sig) for B, O, sig in R['sols']}
print(f"[GT] data (B,O,sigma) classes: {len(data)}; engine: {len(eng)}; "
      f"EXACT SET EQUALITY: {data == eng}")
assert data == eng

# --- L6 free negation: marginal sets come in antipodal pairs T -> negated ---
neg = {frozenset((i + s) % n for i in T) for T in marg}
assert neg == set(marg) and all(frozenset((i + s) % n for i in T) != T for T in marg)
print("[GT] L6: negation acts freely on the 16 marginal elements (8 orbits)")

# --- witness anatomy: S contains z*-fiber, balance -> C(3,2) = 3 ---
for T in wit:
    S = sorted(z for z in range(s) if z in T and (z + s) in T)
    assert len(S) == 5 and (s // 4) in S and (3 * s // 4) not in S
    rest = [z for z in S if z != s // 4]
    assert all((z + s // 2) % s in rest for z in rest)
print("[GT] witness anatomy: z*-fiber in S, 2 antipodal pairs from the 3 "
      "non-z* axes -> C(3,2) = 3  CONFIRMED")
print("CALIBRATION COMPLETE: engine(s=8) == BabyBear n=16 ground truth, 16 = 16")
