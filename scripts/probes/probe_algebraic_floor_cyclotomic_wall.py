import cmath
# n=16: zeta = primitive 16th root of unity. Smoking gun: gapped minor over rows (1,2,5),
# col_powers (1,5,9) — distinct rows, distinct cols, generically full-rank — vanishes at mu_16.
n=16
z=cmath.exp(2j*cmath.pi/n)
rows=[1,2,5]; cols=[1,5,9]
# minor M[i][j] = (zeta^{rows[i]})^{cols[j]} = zeta^{rows[i]*cols[j]}
import itertools
def det3(M):
    return (M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])
          - M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
          + M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))
M=[[z**((rows[i]*cols[j])%n) for j in range(3)] for i in range(3)]
d=det3(M)
print(f"n={n} gapped minor rows={rows} col_powers={cols}: det at mu_16 = {d:.6f}  |det|={abs(d):.2e}")
print(f"  ==> {'VANISHES (≈0) at distinct roots — smoking gun CONFIRMED' if abs(d)<1e-9 else 'nonzero'}")
# antipodal mechanism: 1 + zeta^8 = ?
print(f"  antipodal: 1 + zeta^8 = {1+z**8:.6f}  (zeta^8 = primitive 2nd root = -1)")
# contiguous control: cols (0,1,2) should be nonzero (plain Vandermonde)
cols0=[0,1,2]
M0=[[z**((rows[i]*cols0[j])%n) for j in range(3)] for i in range(3)]
d0=det3(M0)
print(f"  contiguous control rows={rows} cols={cols0}: |det|={abs(d0):.4f}  ({'nonzero (Dirichlet-able)' if abs(d0)>1e-9 else 'zero'})")
