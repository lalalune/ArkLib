import sympy as sp, random
from itertools import combinations
def mu_n_field(p, n):
    if (p-1) % n: return None
    g = sp.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    return [pow(h, i, p) for i in range(n)]

def count_bad(p, n, k, a, Q0coef, Q1coef):
    mu = mu_n_field(p,n)
    if mu is None: return None
    bad=[]
    for gamma in range(p):
        pts=[]
        for z in mu:
            q0=sum(Q0coef[i]*pow(z,i,p) for i in range(len(Q0coef)))%p
            q1=sum(Q1coef[i]*pow(z,i,p) for i in range(len(Q1coef)))%p
            pts.append((z,(q0+gamma*q1)%p))
        found=False
        for sub in combinations(range(n),a):
            xs=[pts[i][0] for i in sub]; ys=[pts[i][1] for i in sub]
            if len(set(xs))<a: continue
            M=[[pow(xs[r],c,p) for c in range(k)] for r in range(k)]
            try: Mi=sp.Matrix(M).inv_mod(p)
            except: continue
            coef=(Mi*sp.Matrix(ys[:k]))%p
            if all((sum(int(coef[c])*pow(xs[r],c,p) for c in range(k))%p)==ys[r] for r in range(a)):
                found=True; break
        if found: bad.append(gamma)
    return bad

# PLANT: choose Q1 = X^k (monomial, survivor case) and Q0 so that at gamma=g0, Q0+g0 X^k = a deg<k codeword
# on a coset-structured a-subset. Then sweep p and confirm #bad is q-independent and <= resultant degree a.
n,k,a=6,2,4
# Q0 = some deg<k poly minus g0*X^k so pencil hits codeword at gamma=g0=0: Q0 deg<k, Q1=X^k
random.seed(7)
Q0=[3,5,0,0]      # deg 1 (<k=2): a genuine codeword. Q1 = X^2
Q1=[0,0,1,0]      # X^2, k=2
print("PLANTED monomial: Q0=codeword(deg<k), Q1=X^k -> gamma=0 makes pencil=codeword on ALL n.")
print("n,k,a=",n,k,a,"supply C(n,a)=",sp.binomial(n,a), " resultant-deg bound (<=a)=",a)
for p in [7,13,19,31,37,43,61,67,73]:
    if (p-1)%n==0:
        b=count_bad(p,n,k,a,Q0,Q1)
        print(f"  p={p}: #bad gamma = {len(b)}  bad set = {b[:6]}")
