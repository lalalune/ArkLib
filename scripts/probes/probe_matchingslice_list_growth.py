# The matching-slice list for the monomial word x^a on 2-power mu_n is exactly
# #{a-subsets S of mu_n : sum(S)=0} (monomial_list_eq_zeroSum). This is the supply
# object the floor uses. Compute its EXACT growth for a=4 (and a=6), n=8..64, over a
# clean prime (char-0 regime), and fit: poly(n) (floor-supporting) or bigger?
from itertools import combinations
from collections import Counter
import math
def is_prime(x):
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return x>1
def subgroup(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p); s,x=set(),1
        for _ in range(n): s.add(x); x=x*h%p
        if len(s)==n: return sorted(s)
    return None
def clean_prime(n):
    base=int(n**3.5); p=base+((1-base)%n)
    while not(is_prime(p) and (p-1)%n==0): p+=1
    return p
def zerosum_subsets(H,p,a):
    return sum(1 for S in combinations(H,a) if sum(S)%p==0)
print("Matching-slice list = #{a-subsets of mu_n, sum=0} (char-0 clean prime):\n")
for a in (4,6):
    print(f"a={a} (agreement floor; code deg<{a-1}):")
    prev=None
    for m in range(3,7):
        n=1<<m
        if a>n: continue
        p=clean_prime(n); H=subgroup(p,n)
        if n<=64:
            L=zerosum_subsets(H,p,a)
            Nfib=math.comb(1<<(m-1), a//2)
            ratio=f", L/L_prev={L/prev:.2f}(n doubled)" if prev else ""
            exp=math.log(L)/math.log(n) if L>1 else 0
            print(f"   n={n:>2}: zero-sum {a}-subsets = {L:>6}  (N_fib=C(2^{m-1},{a//2})={Nfib})  "
                  f"~n^{exp:.2f}{ratio}")
            prev=L
    print()
print("Reading: if L doubles by ~2^(a-1) when n doubles ⟹ L ~ n^(a-1)/poly = POLYNOMIAL")
print("(floor-supporting: the matching-slice list is poly(n), not exponential).")

print("\nPRIZE-REGIME (constant rate a~ρn): the matching-slice list N_fib=C(n/2, a/2):")
for rho_lbl,rd in (("1/4",4),("1/8",8)):
    vals=[]
    for m in range(4,9):
        n=1<<m; a=n//rd  # a~ρn (even)
        if a<2 or a%2: a=(a//2)*2
        vals.append((n,a,math.comb(n//2, a//2)))
    print(f"  ρ={rho_lbl}: "+" ".join(f"n={n}:C({n//2},{a//2})={v}" for n,a,v in vals))
print("  ⟹ at CONSTANT rate the matching list is EXPONENTIAL in n — the sub-Johnson")
print("     supply wall, confirmed. (poly only at vanishing rate / fixed a.)")
