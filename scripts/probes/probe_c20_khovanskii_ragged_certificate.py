"""
Confirm the m+1-element root set S = {x^m=-1} U {1} is GENUINELY RAGGED:
closed under NO nontrivial dilation x -> zeta*x, zeta in mu_{d'}, d'>1.
(Khovanskii's bound, even if it held, only bounds the ragged part per C20's own coset-stripping.)
"""
import sympy

mu = 9
n = 2**mu; m = n//2
# prize prime
c = n**3 // n + n*n
while True:
    p = c*n + 1
    if p > n**3 and sympy.isprime(p): break
    c += 1
g = sympy.primitive_root(p)
zeta_n = pow(g, (p-1)//n, p)
mu_n = [pow(zeta_n, j, p) for j in range(n)]
def f(x): return (pow(x,m+1,p) - pow(x,m,p) + x - 1) % p
S = set(x for x in mu_n if f(x)==0)
print(f"n={n} p={p}  |S|={len(S)}  (m+1={m+1})")

# Check S is dilation-closed under zeta in mu_{d'} for any d'|n, d'>1.
# d' divides n=2^mu, so d' in {2,4,...,n}. zeta = generator of mu_{d'} = zeta_n^(n/d').
ragged = True
for mu2 in range(1, mu+1):       # d' = 2^mu2
    dprime = 2**mu2
    zeta_d = pow(zeta_n, n//dprime, p)   # primitive d'-th root of unity
    # S coset-union under mu_{d'} iff S closed under mult by zeta_d
    closed = all((zeta_d * x) % p in S for x in S)
    if closed:
        ragged = False
        print(f"   d'={dprime}: S IS closed under mu_{dprime} dilation -> coset-union (NOT ragged)")
# Also confirm the coset CORE: {x^m=-1} is the mu_m-coset (size m), and the straggler 1 breaks symmetry
core = set(x for x in mu_n if pow(x,m,p) == (p-1))   # x^m = -1
print(f"   coset core {{x^m=-1}} size = {len(core)} (= m = {m}); straggler {{1}} present: {1 in S}")
print(f"   S = core U {{1}}? {S == core | {1}}")
print(f"   GENUINELY RAGGED (no nontrivial dyadic dilation closes S)? {ragged}")
print()
print(f"   Per C20 'coset stripping in-tree proven': ragged EXCESS over the size-{m} coset core is "
      f"|S|-{m} = {len(S)-m}.")
print(f"   But C20's CLAIM is the ragged ROOT COUNT (s*) <= Khovanskii const + core(n/2).")
print(f"   The probe shows the genuinely-ragged set itself = core(n/2) U straggler; the *excess* is O(k),")
print(f"   NOT bounded-by-Khovanskii-const as a free standing fewnomial fact. And critically the coset CORE")
print(f"   itself is n/2 = {m} = the JOHNSON-radius-sized antipodal coset -- delta*=1-sqrt(rho) only.")
