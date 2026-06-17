# PROBE: even-order signed period-power sum = sum of eta_psi^r with eta REAL (neg-closed mu_n),
# hence >= 0, giving W_r >= n^r/q AND M^r >= (q W_r - n^r)/(q-1) for EVEN r.
# Prize discipline: PROPER thin mu_n=2^a, p==1 mod n, (p-1)/n>=2, multi-prime incl p>n^3 + Fermat, NEVER n=q-1.
import cmath, math
from itertools import product

def mu_n(p, n):
    # n-th roots of unity in F_p* as integers mod p (n | p-1)
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)  # order-n element
    return [pow(h, k, p) for k in range(n)]

def primitive_root(p):
    # find primitive root mod p
    phi = p-1
    facs = factor(phi)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in facs):
            return g
    raise RuntimeError

def factor(m):
    fs=set(); d=2
    while d*d<=m:
        while m%d==0: fs.add(d); m//=d
        d+=1
    if m>1: fs.add(m)
    return fs

def eta(S, b, p):
    # eta_b = sum_{x in S} e_p(b x), additive char
    return sum(cmath.exp(2j*math.pi*(b*x % p)/p) for x in S)

def zeroSumCount(S, r, p):
    # #{ (x1..xr) in S^r : sum = 0 mod p }
    cnt=0
    for t in product(S, repeat=r):
        if sum(t) % p == 0:
            cnt+=1
    return cnt

configs = [
    # (p, n) : n=2^a thin, n | p-1, (p-1)/n >= 2, NEVER n=q-1
    (17, 4), (17, 8),       # Fermat 17, n=4,8
    (97, 8), (97, 4),       # p=97, n|96
    (193, 8), (193,16),     # p=193
    (257, 4), (257,8), (257,16),  # Fermat 257
    (4129, 8),              # p>n^3 (8^3=512)
    (40961, 8),             # large
]

print(f"{'p':>6} {'n':>3} {'r':>2} {'W_r':>8} {'n^r/q':>10} {'W>=floor':>8} {'signedReal':>10} {'maxLowB^r':>12} {'M^r':>12} {'M>=lb':>6}")
allok=True
for (p,n) in configs:
    S = mu_n(p,n)
    assert len(S)==n and (p-1)//n>=2 and n!=p-1
    for r in [2,4]:
        W = zeroSumCount(S, r, p)
        # signed sum over psi!=0 = q*W - n^r ; verify it's real and = sum eta^r
        signed = sum(eta(S,b,p)**r for b in range(1,p))  # b=0 excluded => nonzero chars
        # eta real check: max imag part of each eta
        maxim = max(abs(eta(S,b,p).imag) for b in range(1,p))
        identity_lhs = signed
        identity_rhs = p*W - n**r
        idok = abs(identity_lhs - identity_rhs) < 1e-6
        # nonneg => W >= n^r/q
        floor = n**r / p
        wfloor_ok = W >= floor - 1e-9
        # max lower bound: each eta^r = |eta|^r (since real, r even) <= M^r ; sum <= (p-1) M^r
        Mr = max(abs(eta(S,b,p))**r for b in range(1,p))  # M^r over nonzero
        lb = (p*W - n**r)/(p-1)
        mlb_ok = Mr >= lb - 1e-6
        ok = idok and wfloor_ok and mlb_ok and maxim < 1e-6
        allok = allok and ok
        print(f"{p:>6} {n:>3} {r:>2} {W:>8} {floor:>10.3f} {str(wfloor_ok):>8} {str(idok and maxim<1e-6):>10} {lb:>12.3f} {Mr:>12.3f} {str(mlb_ok):>6}")
print("\nALL OK:", allok)
