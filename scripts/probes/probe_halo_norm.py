# The halo threshold: max over non-antipodal E of |Norm_{Q(zeta_2^m)/Q}(antipodalDiff_E(zeta))|.
# antipodalDiff_E = sum_{j<N} c_j x^j, c_j = [j in E]-[j+N in E] in {-1,0,1}, not all 0.
# Norm = prod over primitive 2^m-th roots zeta^s (s odd, 0<s<2^m) of antipodalDiff_E(zeta^s).
# We compute it exactly via resultant with the cyclotomic Phi_{2^m}=x^N+1.
import itertools, cmath, math
from functools import reduce
def norm_of_coeffs(c, m):
    N=2**(m-1)
    # antipodalDiff(x)=sum c_j x^j, deg<N. Norm over Q(zeta_2^m): product over primitive roots.
    # = Res(Phi_{2^m}(x), antipodalDiff(x)) / lc(Phi)^deg ... use numeric product (exact-ish via rounding)
    val=1.0
    for s in range(1,2**m,2):  # primitive 2^m-th roots = zeta^s, s odd
        z=cmath.exp(2j*math.pi*s/2**m)
        p=sum(c[j]*z**j for j in range(N))
        val*=p
    return round(val.real)
print(f"{'m':>3}{'N=2^(m-1)':>10}{'N^N(crude)':>14}{'ACTUAL max|Norm|':>18}{'log2(actual)':>13}")
for m in [2,3,4,5]:
    N=2**(m-1)
    best=0; bestc=None
    # enumerate all c in {-1,0,1}^N (3^N), skip all-zero. For m=5 N=16 -> 3^16=43M too many; sample.
    if N<=8:
        space=itertools.product([-1,0,1],repeat=N)
        for c in space:
            if all(x==0 for x in c): continue
            nm=abs(norm_of_coeffs(c,m))
            if nm>best: best=nm; bestc=c
    else:
        import random; random.seed(0)
        for _ in range(300000):
            c=[random.choice([-1,0,1]) for _ in range(N)]
            if all(x==0 for x in c): continue
            nm=abs(norm_of_coeffs(c,m))
            if nm>best: best=nm; bestc=c
    crude=N**N
    print(f"{m:>3}{N:>10}{crude:>14}{best:>18}{math.log2(best) if best>0 else 0:>13.1f}")
