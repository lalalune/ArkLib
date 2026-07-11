import math, sympy

# Cay(F_p, mu_n) on p vertices. mu_n ⊃ mu_{n/2}. The graph with the LARGER connection set has the
# SMALLER one's edges as a subset: A(mu_n) = A(mu_{n/2}) + A(coset). These do NOT commute as graphs
# but DO share the eigenvECTOR basis (all are diagonalized by additive characters psi_b).
# So eigenvalue OF CHARACTER b: lambda_b(mu_n) = lambda_b(mu_{n/2}) + lambda_b(zeta*mu_{n/2}).
# The point: there's NO covering map Cay(mu_n)->Cay(mu_{n/2}) that would give interlacing
# spec(quotient) subset spec(cover). Both graphs are on the SAME p vertices, simultaneously
# diagonalized. The relationship is per-character ADDITIVE, not interlacing. Verify:

def is_prime(m): return sympy.isprime(m)
def find_p(kmax, lo):
    M=1<<kmax; p=((lo//M)+1)*M+1
    while not is_prime(p): p+=M
    return p

p=find_p(8, 500000)
g=sympy.primitive_root(p); n=256
h=pow(g,(p-1)//n,p)                 # gen of mu_256
def mu(k):
    nk=1<<k; gen=pow(h, n//nk, p); return [pow(gen,t,p) for t in range(nk)]
def lam(b,H):
    tp=2*math.pi
    return complex(sum(math.cos(tp*(b*x%p)/p) for x in H), sum(math.sin(tp*(b*x%p)/p) for x in H))

# zeta = primitive 2^k root generating coset: mu_{2^k} = mu_{2^{k-1}} cup zeta*mu_{2^{k-1}}, zeta=gen of mu_{2^k}
print("Per-character additive law: lambda_b(mu_{2^k}) = lambda_b(mu_{2^{k-1}}) + lambda_b(zeta*mu_{2^{k-1}})")
k=6; Hk=mu(k); Hkm1=mu(k-1)
genk=pow(h,n//(1<<k),p)   # primitive 2^k root = the coset rep
coset=[(genk*y)%p for y in Hkm1]
maxerr=0.0
for b in range(1,200):
    lhs=lam(b,Hk); rhs=lam(b,Hkm1)+lam(b,coset)
    maxerr=max(maxerr,abs(lhs-rhs))
print(f"  max|lhs-rhs| over b=1..199: {maxerr:.2e}  (==0 => exact additive, NO interlacing transmission)")

print()
print("=== KEY: does a SMALL eigenvalue of mu_{n/2} at char b GUARANTEE small at mu_n? ===")
print("If lambda_b(mu_{n/2}) tiny but lambda_b(coset) big, the sum can be big. So GOOD bound on")
print("child does NOT transmit up. Conversely a big BAD eigenvalue can persist. Sample worst case:")
Hkm1=mu(5); Hk=mu(6); genk=pow(h,n//(1<<6),p); coset=[(genk*y)%p for y in Hkm1]
worst=0; wb=0
for b in range(1,p):
    child=abs(lam(b,Hkm1)); parent=abs(lam(b,Hk))
    if parent>worst: worst=parent; wb=b
chb=abs(lam(wb,Hkm1))
print(f"  argmax parent b={wb}: |lambda_b(mu_64)|={worst:.3f}  but |lambda_b(mu_32)|={chb:.3f}")
print(f"  ratio parent/child = {worst/chb if chb>1e-9 else float('inf'):.2f}  => child was {'SMALL' if chb<worst/2 else 'comparable'}, bound did NOT come from child")
