from itertools import combinations
# Large prime with 16 | p-1, big enough to avoid e1 collisions in char 0.
# Find p ~ 2^31 with 16 | p-1.
def isprime(m):
    if m<2: return False
    for d in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%d==0: return m==d
    d=m-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True
p=2013265921  # 2^31*15//... known FFT prime; check 16|p-1
assert (p-1)%16==0 and isprime(p)
def subgroup_gen(p,n):
    # find element of order exactly n
    for g in range(2,200):
        if pow(g,(p-1)//2,p)!=1:  # primitive enough check skipped; just take generator power
            cand=pow(g,(p-1)//n,p)
            if pow(cand,n,p)==1 and all(pow(cand,n//q,p)!=1 for q in (2,)):
                return cand
    return None
n=16
gen=subgroup_gen(p,n)
H=[pow(gen,i,p) for i in range(n)]
assert len(set(H))==n, len(set(H))
def esym_top2(elems):
    # e1 = sum, e2 = sum of pairwise products; do e3..ea via Newton needed for deficit pattern
    m=len(elems)
    pw=[sum(pow(x,j,p) for x in elems)%p for j in range(1,m+1)]
    e=[1]
    for j in range(1,m+1):
        s=0
        for i in range(1,j+1):
            s=(s+ ((-1)**(i-1))*e[j-i]*pw[i-1])%p
        e.append(s*pow(j,p-2,p)%p)
    return e
# Test hypothesis: deep-band bad config = a-subset with e_3=...=e_a=0 (interior vanish, top-2 free).
print(f"p={p}")
for a in range(4, n//2+2):
    e1set=set()
    cnt_configs=0
    for S in combinations(range(n),a):
        elems=[H[i] for i in S]
        e=esym_top2(elems)
        if all(e[j]==0 for j in range(3,a+1)):  # e3..ea all zero
            e1set.add(e[1]); cnt_configs+=1
    print(f"a={a} (r={a-1}): interior-vanish configs={cnt_configs}  distinct e1={len(e1set)}")
