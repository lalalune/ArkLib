# CONFIRMED model: deep-band #bad(r) = #{ distinct e1(S) : S in C(mu_n, r+1), p2(S) := sum x^2 = 0 }.
# (The top-frequency deep-band line forces the sum-of-squares to vanish; bad gamma = -e1.)
# Verify full n=16 ladder r=3..8 should be 97,145,89,113,225,104.
from itertools import combinations
p=2013265921
def gen_order(p,n):
    for g in range(2,500):
        cand=pow(g,(p-1)//n,p)
        if pow(cand,n,p)==1 and all(pow(cand,n//q,p)!=1 for q in (2,)):
            return cand
def ladder(n, p):
    g=gen_order(p,n)
    H=[pow(g,i,p) for i in range(n)]
    assert len(set(H))==n
    Hsq=[pow(h,2,p) for h in H]
    out={}
    for a in range(4, n//2+2):  # a=r+1, r=3..n/2
        e1set=set()
        for S in combinations(range(n),a):
            if sum(Hsq[i] for i in S)%p==0:
                e1set.add(sum(H[i] for i in S)%p)
        out[a-1]=len(e1set)
    return out
res=ladder(16,p)
print("n=16 ladder (r:#bad):", res)
expected={3:97,4:145,5:89,6:113,7:225,8:104}
print("expected:           ", expected)
print("MATCH:", res==expected)
