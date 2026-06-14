# The line forces e2 = phi(e1); via Newton p2 = e1^2 - 2 e2. The TOP-freq line carries x^{k_c} and x^{k_c-1}?
# Let me search for the deficit-2 relation that reproduces ALL six ladder values simultaneously.
# Candidate: p2(S) = t * e1(S)^2 for a fixed rational t (the line slope), OR e2(S)=t*e1^2, OR e1^2 = c*e2.
# Also try the "both top coeffs vanish" => e1 and e2 BOTH equal specific line values, but since gamma free,
# the actual constraint relating them is a single homogeneous relation. Sweep t over small rationals.
from itertools import combinations
from fractions import Fraction
p=2013265921
def gen_order(p,n):
    for g in range(2,500):
        cand=pow(g,(p-1)//n,p)
        if pow(cand,n,p)==1 and all(pow(cand,n//q,p)!=1 for q in (2,)):
            return cand
n=16
g=gen_order(p,n)
H=[pow(g,i,p) for i in range(n)]
Hsq=[pow(h,2,p) for h in H]
expected={3:97,4:145,5:89,6:113,7:225,8:104}
def e1(S): return sum(H[i] for i in S)%p
def p2(S): return sum(Hsq[i] for i in S)%p
# precompute per a the list of (e1,p2)
data={}
for a in range(4,10):
    L=[]
    for S in combinations(range(n),a):
        L.append((e1(S),p2(S)))
    data[a]=L
def count_with_relation(a, num, den):
    # p2 == (num/den)*e1^2  i.e. den*p2 == num*e1^2  mod p
    s=set()
    invden = num%p  # we use den*p2 - num*e1^2 == 0
    for (s1,sp2) in data[a]:
        if (den*sp2 - num*(s1*s1))%p==0:
            s.add(s1)
    return len(s)
# sweep t=num/den
best=None
for num in range(0,9):
    for den in range(1,9):
        ok=True; got={}
        for a in range(4,10):
            c=count_with_relation(a,num,den)
            got[a-1]=c
        if got==expected:
            print(f"MATCH p2 = ({num}/{den}) e1^2 :", got); best=(num,den)
# also try e2 relation: e2 = t e1^2  <=> p2 = e1^2 - 2 e2 = (1-2t) e1^2, same family.
if not best:
    print("no single homogeneous p2=t*e1^2 match; sample counts:")
    for num in [0,1,2,3,4]:
        for den in [1,2,4]:
            print(f"  t={num}/{den}: ", {a-1:count_with_relation(a,num,den) for a in range(4,10)})
