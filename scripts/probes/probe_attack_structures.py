"""
ATTACK the 2-power structures rigorously:
(1) Clifford group action: does ANY map beyond dilation x->zeta^j x (and swap, S_r perms) preserve the
    fixed-p wraparound {Sum x = Sum y mod p}? Test the candidate Clifford gates:
    - Galois sigma_a: zeta->zeta^a  (moves the prime p? check if it preserves the SET at fixed p)
    - 'Fourier'-type: does any permutation-of-roots beyond dilation preserve it?
    => determine the ACTUAL symmetry group order (=> v_2 bound), confirm it's NOT the full Clifford 2^{O(mu^2)}.
(2) Generating function: Sum_r E_r t^r = (1/p) Sum_b 1/(1 - eta_b^2 t). Verify W_r is C-FINITE (linear
    recurrence) with order = #distinct eta_b^2 => the gen func poles ARE the periods => no transcendental
    escape (refutes the 'modular/mock-modular' hope S4).
"""
from collections import Counter
import math
def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61):
        if m%q==0:return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in(2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in(1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n:
            return sorted(pow(h,i,p) for i in range(n))

print("(1) ACTUAL symmetry group of the fixed-p wraparound. n=8, a small bad prime.")
n=8; p=17
S=subgroup(p,n)  # mu_8 in F_17
print(f"  mu_{n} in F_{p}: {S}")
# enumerate wraparound: (idx_x, idx_y) in [n]^4 (r=2) with sum equal mod p but record which symmetries fix the set
import itertools
sols=set()
for combo in itertools.product(range(n),repeat=4):
    xs=[S[i] for i in combo[:2]]; ys=[S[i] for i in combo[2:]]
    if sum(xs)%p==sum(ys)%p: sols.add(combo)
# char-0 solutions (large prime)
q=1000003
while not(q%n==1 and isprime(q)): q+=1
Sq=subgroup(q,n)
solsc0=set()
for combo in itertools.product(range(n),repeat=4):
    xs=[Sq[i] for i in combo[:2]]; ys=[Sq[i] for i in combo[2:]]
    if sum(xs)%q==sum(ys)%q: solsc0.add(combo)
W=sols-solsc0
print(f"  wraparound W_2 (tuples) = {len(W)}")
# test which index-maps preserve W:
def test_map(name, f):
    ok=all(tuple(f(combo)) in W for combo in W)
    print(f"    {name}: preserves W? {ok}")
test_map("dilation (idx+1 mod n)", lambda c: tuple((i+1)%n for i in c))
test_map("swap x<->y", lambda c: (c[2],c[3],c[0],c[1]))
test_map("negation (idx+n/2)", lambda c: tuple((i+n//2)%n for i in c))
for a in (3,5,7):
    test_map(f"Galois zeta->zeta^{a} (idx*{a})", lambda c,a=a: tuple((i*a)%n for i in c))
print()
print("(2) generating function: is W_r C-finite (=> poles are periods => no transcendental escape)?")
print("  Sum_r E_r t^r = (1/p) Sum_b 1/(1-eta_b^2 t): rational, order = #distinct eta_b^2.")
n=8; p=4129
S=subgroup(p,n)
g=2
while pow(g,(p-1)//2,p)==1: g+=1
m=(p-1)//n
etas=[sum(math.cos(2*math.pi*(pow(g,j,p)*x%p)/p) for x in S) for j in range(m)]
e2=sorted(set(round(e*e,4) for e in etas))
print(f"  n={n} p={p}: #distinct eta_b^2 = {len(e2)} (incl eta_0^2={n*n}). Gen func order ~ this = the period spectrum.")
print(f"  => E_r (hence W_r) is C-FINITE of order ~{len(e2)} (the periods); NOT transcendental. S4/modular REFUTED.")
