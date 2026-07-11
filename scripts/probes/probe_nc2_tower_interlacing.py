import math, sympy
from collections import Counter

# Cay(F_p, mu_n): vertices F_p, x~y iff x-y in mu_n. mu_n symmetric iff -1 in mu_n (n even => yes).
# Eigenvalues: lambda_b = sum_{g in mu_n} e_p(b g), b in F_p. (Abelian Cayley, characters psi_b(x)=e_p(bx).)
# So lambda_2(Cay) = M(n) = max_{b!=0} |lambda_b|. The "spectral" framing is literally the char sum.
# Ramanujan for n-regular: |lambda_b| <= 2 sqrt(n-1) for nontrivial b. Prize wants <= C sqrt(n log p).

def is_prime(m): return sympy.isprime(m)

def find_p_pow2(kmax, lo):
    M=1<<kmax; p=((lo//M)+1)*M+1
    while not is_prime(p): p+=M
    return p

def subgroups_chain(p, ktop):
    # coherent chain mu_{2^k} for k=1..ktop, all powers of one generator h of mu_{2^ktop}
    n=1<<ktop; g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p)
    out={}
    for k in range(1,ktop+1):
        nk=1<<k; gen=pow(h, n//nk, p)
        out[k]=[pow(gen,t,p) for t in range(nk)]
    return out

def eigs(H,p):
    tp=2*math.pi
    return [ (b, math.hypot(sum(math.cos(tp*(b*x%p)/p) for x in H),
                              sum(math.sin(tp*(b*x%p)/p) for x in H))) for b in range(1,p) ]

def M_and_argmax(H,p):
    es=eigs(H,p); b,m=max(es,key=lambda t:t[1]); return m,b

# COVERING-MAP TEST: mu_{2^k} ⊃ mu_{2^{k-1}}. Cay(F_p, mu_{2^k}) is NOT a cover of Cay(F_p,mu_{2^{k-1}})
# in the usual topological sense; rather adjacency matrices A_k = sum over mu_{2^k}, and
# A_k = A_{k-1}-shifted ... Actually mu_{2^k} = mu_{2^{k-1}} ∪ (coset). Eigenvalue relation:
# lambda_b(2^k) = sum_{mu_{2^{k-1}}} e_p(bx) + sum_{coset} e_p(bx). The coset = zeta * mu_{2^{k-1}} where
# zeta is a primitive 2^k root. So lambda_b(2^k) = lambda_b(2^{k-1}) + lambda_{b'}(2^{k-1})? NO: coset is
# multiplicative. lambda_b(mu_{2^k}) = sum_{y in mu_{2^{k-1}}} e_p(by) + e_p(b zeta y)... not a clean shift.

print("=== Is spec(mu_{2^{k-1}}) a SUBSET of spec(mu_{2^k})? (true covering interlacing) ===")
p=find_p_pow2(7, 200000); lnp=math.log(p)
print(f"p={p}, ln p={lnp:.3f}")
subs=subgroups_chain(p,7)
# Check the per-b eigenvalue relation across levels for a sample of b
for k in range(2,8):
    H=subs[k]; n=len(H)
    M,b=M_and_argmax(H,p)
    print(f"k={k} n={n:>3}: M(n)={M:8.3f}  2sqrt(n-1)={2*math.sqrt(n-1):7.3f}  sqrt(n*lnp)={math.sqrt(n*lnp):7.3f}  M/sqrt(n)={M/math.sqrt(n):.4f}  Ramanujan={'YES' if M<=2*math.sqrt(n-1) else 'NO'}")
