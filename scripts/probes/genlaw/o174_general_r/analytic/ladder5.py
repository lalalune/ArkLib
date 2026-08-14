# Reproduce r=3 -> 97 in char 0 / large prime to fix the EXACT band definition, then run the ladder.
# r=3 closed form: #bad = n*C(n/4,2)+1 = 16*C(4,2)+1 = 16*6+1 = 97. n=16.
# Structure (CONNECT): bad gamma = -e1(S). The r=3 antipodal/parity-split: bad set = e1-sums of
# pair-products of the order-(n/4) subgroup... Let me find which 4-subset family gives EXACTLY 97 distinct e1.
from itertools import combinations
p=2013265921
def gen_order(p,n):
    for g in range(2,500):
        cand=pow(g,(p-1)//n,p)
        if pow(cand,n,p)==1 and all(pow(cand,n//q,p)!=1 for q in (2,)):
            return cand
n=16
g=gen_order(p,n)
H=[pow(g,i,p) for i in range(n)]
assert len(set(H))==16
# The deep band for r=3, agreement a0, deficit 2. Try a0 = r+1 = 4 subsets with the line forcing top-2:
# Candidate definitions to hit 97 distinct e1:
# D1: ALL 4-subsets, distinct e1  (=spectrum size, will be huge)
def e1(S): return sum(H[i] for i in S)%p
def e2(S):
    s=0; L=list(S)
    for i in range(len(L)):
        for j in range(i+1,len(L)):
            s=(s+H[L[i]]*H[L[j]])%p
    return s
def p2(S): return sum(pow(H[i],2,p) for i in S)%p
allsum=set()
# D2: 4-subsets that are "antipodal-closed-ish": contain an antipodal pair {x,-x} (i.e. indices i, i+8)
anti_e1=set()
# D3: 4-subsets with e2 = 0 (some natural deficit condition)
e2zero_e1=set()
# D4: 4-subsets with p2 = 0 (sum of squares zero)
p2zero_e1=set()
# D5: 4-subsets being a union of two antipodal pairs {x,-x,y,-y} -> e1=0 always; not 97.
for S in combinations(range(16),4):
    allsum.add(e1(S))
    if any((i+8)%16 in S for i in S):
        anti_e1.add(e1(S))
    if e2(S)==0: e2zero_e1.add(e1(S))
    if p2(S)==0: p2zero_e1.add(e1(S))
print("r=3 (4-subsets):")
print("  all distinct e1:", len(allsum))
print("  contain antipodal pair, distinct e1:", len(anti_e1))
print("  e2=0, distinct e1:", len(e2zero_e1))
print("  p2=0, distinct e1:", len(p2zero_e1))
