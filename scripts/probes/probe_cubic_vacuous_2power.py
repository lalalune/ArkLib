# Finding: for 2-power smooth domains the cubic supply T=#{a+b+c=0} is IDENTICALLY 0
# (3 does not divide 2^m, so no weight-3 vanishing sum of 2-power roots, Mann). So the
# cubic CS bridge T^2<=nE is vacuous for the PRIZE case; the operative supply is the
# EVEN/4-term subset-sum (energy-based). Verify both.
from collections import Counter
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
print("Cubic (3-term) vs even (4-term) supply for 2-power mu_n (char-0 clean prime):\n")
for n in (8,16,32):
    p=clean_prime(n); H=subgroup(p,n); Hs=set(H)
    T3=sum(1 for a in H for b in H if (-(a+b))%p in Hs)      # ordered zero-sum triples
    # even/4-term: #{(a,b,c,d): a+b+c+d=0} = sum_s N2(s)*N2(-s), N2(s)=#{(a,b):a+b=s}
    N2=Counter((a+b)%p for a in H for b in H)
    T4=sum(N2[s]*N2[(-s)%p] for s in N2)
    E=sum(v*v for v in N2.values())                          # additive energy a+b=c+d
    print(f"n={n} p={p}: T_cubic(3-term zero-sum)={T3}  | T_4term(zero-sum quad)={T4}  "
          f"| E(energy)={E}=3n(n-1)={3*n*(n-1)}{'✓' if E==3*n*(n-1) else '✗'}")
print("\n⟹ T_cubic ≡ 0 for every 2-power n (Mann: 3∤2^m). The energy→list link for the")
print("  prize's 2-power case is the EVEN 4-term/subset-sum route, NOT the cubic CS bound.")
