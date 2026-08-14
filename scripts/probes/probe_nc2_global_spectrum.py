import math, sympy
# The "global spectrum" claim: a Ramanujan/zeta argument bounds lambda_2 via ALL eigenvalues at once.
# For Cay(F_p,mu_n) the eigenvalues are {lambda_b}_{b in F_p}. Galois acts: sigma_c: zeta_p -> zeta_p^c
# permutes characters b -> c*b. The n/2 GALOIS CONJUGATES of a fixed lambda_b are {lambda_{cb}}_{c in (Z/p)*/...}.
# Actually conjugates of the ALGEBRAIC NUMBER lambda_b = sum_{mu_n} zeta_p^{bx} live in Q(zeta_p);
# Gal(Q(zeta_p)/Q) = (Z/p)* permutes them, but lambda_b in fixed field of stabilizer.
# The n/2 conjugates relevant to the obstruction are the Gal(Q(zeta_n)/Q)-conjugates of a SPURIOUS
# RELATION beta, NOT the p-1 graph eigenvalues. These are DIFFERENT conjugacy structures.
#
# DECISIVE TEST: A global-spectrum (trace/zeta) argument controls sum_b f(lambda_b) = trace of f(A),
# i.e. CLOSED WALK COUNTS = MOMENTS. We already PROVED the char-0 Wick moment bound E_r<=(2r-1)!!n^r.
# The moment/trace method IS the global-spectrum method. The WALL is the char-0 -> char-p TRANSFER,
# which the obstruction says fails because p | N(beta) for a product over n/2 conjugates.
# So: does the GLOBAL spectrum (=moments) give us anything BEYOND the moment method we already have?
# trace(A^r) = sum_b lambda_b^r = p * (#closed r-walks from 0) = p * E_r-type count.
# Verify trace(A^r) = p * (number of (x_1..x_r) in mu_n^r summing to 0):
def is_prime(m): return sympy.isprime(m)
def find_p(kmax, lo):
    M=1<<kmax; p=((lo//M)+1)*M+1
    while not is_prime(p): p+=M
    return p
p=find_p(5, 50000); g=sympy.primitive_root(p); n=32
h=pow(g,(p-1)//n,p); H=[pow(h,t,p) for t in range(n)]
import itertools
def lam(b):
    tp=2*math.pi; return complex(sum(math.cos(tp*(b*x%p)/p) for x in H), sum(math.sin(tp*(b*x%p)/p) for x in H))
for r in [2,3,4]:
    tr=sum((lam(b)**r).real for b in range(p))
    # count r-tuples in H summing to 0 mod p
    from collections import Counter
    # build via convolution
    c=Counter({0:1})
    for _ in range(r):
        nc=Counter()
        for s,v in c.items():
            for x in H: nc[(s+x)%p]+=v
        c=nc
    cnt=c[0]
    print(f"r={r}: trace(A^r)={tr:.1f}  p*N0={p*cnt}  match={abs(tr-p*cnt)<1:}")
print()
print("=> Global spectrum = moments = trace = CLOSED WALKS. The 'Ramanujan/zeta' framing computes")
print("   exactly sum_b lambda_b^r, which is the moment E_r we ALREADY bound in char 0. It adds NO")
print("   new char-p transfer mechanism: trace is rational-integer-valued and char-0-computable;")
print("   the wall is bounding the MAX from the moments, an Alon-Boppana-reverse problem that the")
print("   abelian (NON-Ramanujan, only finitely-Ramanujan) structure does NOT solve.")
