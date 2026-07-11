import itertools, math
def zeta_pow(e, half):
    e %= (2*half); v=[0]*half
    if e<half: v[e]=1
    else: v[e-half]=-1
    return v
def vanishes_upto(S,n,r):
    half=n//2
    for j in range(1,r+1):
        acc=[0]*half
        for i in S:
            v=zeta_pow((i*j)%n,half)
            for t in range(half): acc[t]+=v[t]
        if any(acc): return False
    return True
def is_coset_union(S,n,d):
    # S is a union of cosets of the subgroup d*Z/n (step d) i.e. closed under +d? for mu: subgroup mu_{n/d}
    # cosets of mu_{n/gcd} ... here: closed under translation by n/d? Let's test: closed under +n//blk
    # subgroup of order blk = n/d. coset of subgroup of order 'sub' = {i + t*(n/sub)}. 
    Sset=set(S)
    # test closure under shift by n//blk where blk = subgroup order
    return None
# Hypothesis: V_r counts subsets that are unions of cosets of the order-(n/2^j) subgroup? No—
# the COUNT 2^{n/2^j} = number of subsets of a set of size n/2^j = choosing which of n/2^j 'blocks' to include.
# So: vanishing p_1..p_r  <=>  S is a union of cosets of the subgroup H of INDEX n/2^j (i.e. |H|=2^j),
# giving n/2^j cosets, each in-or-out => 2^{n/2^j} subsets. blk=2^j = 2^{floor(log2 r)+1}.
# Verify for n=16, r=3 (block=2^2=4, index 4, expect coset-unions of the order-4 subgroup, 2^4=16 subsets):
n=16
for r in [1,2,3,4,5]:
    blk = 2**(math.floor(math.log2(r))+1)  # subgroup order
    H = blk  # |subgroup|
    # subgroup of mu_n of order H = {0, n/H, 2n/H, ...} in Z/n
    step = n//H
    subgroup = set(range(0,n,step))  # indices forming order-H subgroup (additive: multiples of step)
    # cosets: {c + subgroup}; a coset-union is determined by which of the n/H? no, |cosets|=n/|subgroup|=step... 
    # number of cosets = n / H = step. Each coset has H elements. union choices = 2^{n/H}=2^step.
    ncos = n//H
    # enumerate coset-unions and check ALL vanish p_1..p_r, AND count matches V_r
    cosets=[]
    seen=set()
    for c in range(n):
        cos=frozenset((c+s)%n for s in subgroup)
        if cos not in seen: seen.add(cos); cosets.append(sorted(cos))
    cu_count=0; cu_all_vanish=True
    for mask in range(2**len(cosets)):
        S=[]
        for b in range(len(cosets)):
            if mask>>b&1: S+=cosets[b]
        if vanishes_upto(S,n,r): cu_count+=1
        else: cu_all_vanish=False
    print(f"r={r}: block|H|={H} #cosets={len(cosets)} -> coset-unions that vanish p_1..p_{r}: {cu_count}/2^{len(cosets)}={2**len(cosets)}  all_vanish={cu_all_vanish}")
