"""
Cross-check the Bareiss det-based field norm against:
 (1) direct complex conjugate product N(a) = prod_{j odd, 1<=j<63} a(zeta^j)
 (2) the L1->norm SCALE bound: for alpha in Z[zeta_64], |sigma(alpha)| <= L1(alpha)
     for every embedding sigma (since |zeta^k|=1), so |N(alpha)| <= L1^32.
This tells us the FULL-lattice supply-transfer threshold:
 a bad alpha with L1 norm <= Lmax can divide a prime p only if p <= |N| <= Lmax^32.
 The transfer is EXACT (no bad alpha) for p > max over the bad lattice of |N(alpha)|,
 and that max is <= Lmax^32 (an UPPER bound), realised near Lmax^32 for "spread" alpha.
"""
import math, cmath

N = 64; D = 32

def norm_complex(c):
    # primitive 64th roots: zeta^j, j odd, 1<=j<=63 (phi=32 of them)
    prod = 1.0+0j
    for j in range(1, N, 2):
        z = cmath.exp(2j*math.pi*j/N)
        val = sum(c[k]*z**k for k in range(D))
        prod *= val
    return prod

# Bareiss det (copy)
def mul_matrix(c):
    M = [[0]*D for _ in range(D)]
    for j in range(D):
        for k in range(D):
            ck = c[k]
            if ck == 0: continue
            e = k+j; sign = 1
            while e >= D:
                e -= D; sign = -sign
            M[e][j] += sign*ck
    return M

def bareiss_det(mat):
    M=[r[:] for r in mat]; n=len(M); sign=1; prev=1
    for k in range(n-1):
        if M[k][k]==0:
            sw=-1
            for i in range(k+1,n):
                if M[i][k]!=0: sw=i;break
            if sw==-1: return 0
            M[k],M[sw]=M[sw],M[k]; sign=-sign
        for i in range(k+1,n):
            for j in range(k+1,n):
                M[i][j]=(M[i][j]*M[k][k]-M[i][k]*M[k][j])//prev
        prev=M[k][k]
    return sign*M[n-1][n-1]

def norm_det(c):
    return bareiss_det(mul_matrix(c))

# test on a few of the actual flagged supports from norms.py output
tests = {
  "BB r3 minN (L1=14)": {0:-1,4:2,6:-1,10:1,12:1,14:1,16:-2,19:1,20:-1,24:-1,25:1,30:-1},
  "BB r3 maxN (L1=18)": {0:-1,2:-1,3:-1,4:1,6:2,8:-1,10:-1,14:1,16:-2,18:1,20:-1,22:1,24:1,26:1,28:1,31:-1},
  "p2 r5 maxN (L1=18)": {0:-2,1:1,2:-1,3:1,10:-2,14:-1,16:-1,21:-1,22:1,23:-1,24:-1,28:2,30:3},
}
for name, supp in tests.items():
    c=[0]*D
    for k,v in supp.items(): c[k]=v
    nd = norm_det(c)
    nc = norm_complex(c)
    l1 = sum(abs(x) for x in c)
    print(f"{name}: det-norm={nd}  complex-norm~{nc.real:.3e}+{nc.imag:.3e}i  "
          f"|det|=2^{math.log2(abs(nd)):.2f}  L1={l1}  L1^32=2^{32*math.log2(l1):.2f}")

# Full-lattice worst-case scale: max |N| over L1<=Lmax
print()
for Lmax in [12,14,16,18,20]:
    print(f"  L1<={Lmax}:  |N(alpha)| <= {Lmax}^32 = 2^{32*math.log2(Lmax):.2f}")
print()
# AM-GM realistic scale: a 'spread' alpha with L2 energy ~L1 distributes |sigma|~sqrt(L1) typically
# geometric-mean of |sigma|^2 = |N|^(1/16); typical |N| ~ (avg |sigma|^2)^16.
# For an L1=18 alpha spread over ~14 coeffs, avg|sigma|^2 ~ sum c_k^2 ~ (per Parseval) -> see measured 2^41..2^67.
print("Measured realised |N| (from norms.py): r=3 BB 2^60-62, p2 2^43-46; "
      "r=5 BB up to 2^63.7, p2 up to 2^66.9")
