# The sub-Johnson list for smooth RS: for RS[mu_n, k] over F_p (n | p-1), and a WORST-CASE word w,
# count codewords c (deg<k) with agree(c,w) >= a, for a in the sub-Johnson range.
# KEY structural question: are the high-agreement codewords' agreement sets COSET-structured (union of
# cosets of subgroups of mu_n)? If so, the tower/cyclotomic structure bounds the list.
# Test on the KKH26 deep-band bad word: w = bad-line point; the explaining codewords are the near ones.
import itertools
from math import comb
def setup(n):
    p=n+1
    while True:
        if all(p%d for d in range(2,int(p**0.5)+1)) and (p-1)%n==0 and p>3*n: break
        p+=1
    for g in range(2,p):
        if pow(g,n,p)==1 and all(pow(g,n//q,p)!=1 for q in set([2] if n%2==0 else []) ) and pow(g,n//2,p)!=1: break
    return p,g
def listsize_and_structure(n, k, a, p, g, w):
    G=[pow(g,j,p) for j in range(n)]
    # codewords = deg<k polys; enumerate all p^k (small) -> too many. Instead enumerate via agreement:
    # a codeword agreeing with w on >=a points: pick a-subset S, interpolate deg<k through... but deg<k
    # poly through a>k points is over-determined. So a codeword with agree>=a is the deg<k interp of any
    # k agreement points, checked to agree on >=a. Enumerate k-subsets, interpolate, count agreement.
    def interp_agree(Tk):
        # deg<k interp of w on Tk (k points), return (poly-coeffs as tuple, agreement count, agreement set)
        xs=[G[i] for i in Tk]; ys=[w[i] for i in Tk]
        full=[]
        for jx in range(n):
            tot=0
            for idx,i in enumerate(Tk):
                num=1;den=1
                for i2 in Tk:
                    if i2!=i: num=(num*(G[jx]-G[i2]))%p; den=(den*(G[i]-G[i2]))%p
                tot=(tot+ys[idx]*num*pow(den,p-2,p))%p
            full.append(tot)
        aset=frozenset(jx for jx in range(n) if full[jx]==w[jx])
        return tuple(full), aset
    cws={}  # codeword (as full eval tuple) -> agreement set
    for Tk in itertools.combinations(range(n), k):
        cw, aset = interp_agree(Tk)
        if len(aset)>=a: cws[cw]=aset
    return cws
# Test: n=8, k=2 (rate 1/4), a = k+1 = 3 (deep band m=0 boundary) and a=k+2.
# worst-case w: try the all-zero (codeword, list huge) is degenerate; use a generic deep word.
import random
for n in [8, 16]:
    p,g=setup(n); G=[pow(g,j,p) for j in range(n)]
    k=max(2, n//4)
    rnd=random.Random(7)
    # build a "deep" word: agree with several codewords. Take w = sum hint: a random non-codeword.
    best=0; beststruct=None
    for trial in range(30):
        w=[rnd.randrange(p) for _ in range(n)]
        for a in [k+1]:
            cws=listsize_and_structure(n,k,a,p,g,w)
            if len(cws)>best:
                best=len(cws)
                # check coset structure of the union of agreement sets
                allpts=set().union(*cws.values()) if cws else set()
                beststruct=(len(cws), [sorted(s) for s in list(cws.values())[:4]])
    print(f"n={n} k={k} a={k+1} (sub-Johnson, Johnson agree~sqrt(kn)={(k*n)**0.5:.1f}): max list over 30 words = {best}")
    if beststruct: print(f"   sample agreement sets: {beststruct[1]}")
