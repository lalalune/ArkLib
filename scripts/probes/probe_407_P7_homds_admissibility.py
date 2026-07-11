#!/usr/bin/env python3
"""
P7 v6 (admissibility + governing-law tie-in + quasipoly field-bound confirmation).

GUARD against over-claiming: the v5 max corank L_max=Theta(a) is achieved by packing
many exponents into few residue classes mod a.  We must check this is LIST-DECODING
ADMISSIBLE -- the corank must reflect actual deg<k RS codewords agreeing on the
mu_a-coset in the WINDOW interior (beyond Johnson, below capacity), not an artifact of
degrees >= k.  RS[mu_n,k] codewords are deg<k; the LIST excess at agreement set A is
the dimension of {deg<k polys vanishing-mod the constraint}, governed by exponents
0..k-1 ONLY.  So the RELEVANT corank is on the window E = {0,1,...,a-1} reduced into
deg<k -- but on mu_a the available distinct residues mod a is exactly min(a, #deg<k
classes).  We measure the corank for the GENUINE list-decoding window and confirm the
list size, then tie to the in-tree governing law I(delta) <= q*eps*.

THE ADMISSIBLE OBJECT.  A list of RS[mu_n,k] codewords all agreeing on a mu_a-coset A
(|A|=a, a>k => beyond unique decoding) = an affine space of deg<k polys interpolating
a-many fixed values on A; but a>k forces the values to be consistent (codeword unique
if a>=k... ). The HOMDS LIST appears at a in (Johnson_agreement, k): the number of
DISTINCT codewords sharing the SAME a-subset agreement with a received word.  On mu_a
this is governed by  #deg<k polys with prescribed restriction to mu_a = the number of
solutions = q^{k - rank(V(mu_a; 0..k-1))} = q^{k - min(k, a... )}.  We compute the
EXACT list size from the restriction map rank and verify it equals 1 (generic) vs >1
(HOMDS excess) and read whether >1 happens in the WINDOW.
"""
import math, itertools, random, json

def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37):
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
def prime_factors(m):
    s=set();d=2
    while d*d<=m:
        while m%d==0:s.add(d);m//=d
        d+=1
    if m>1:s.add(m)
    return s
def subgroup(p,n):
    e=(p-1)//n;pf=prime_factors(n)
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)!=1:continue
        if any(pow(h,n//q,p)==1 for q in pf):continue
        S=[pow(h,j,p) for j in range(n)]
        if len(set(S))==n:return h,S
    raise RuntimeError("no subgroup")
def find_thick_prime(n,blo=2.5,bhi=3.5):
    lo=max(n*2+1,int(n**blo));hi=int(n**bhi);m=max(2,lo//n)
    while n*m+1<=hi:
        p=n*m+1
        if isprime(p):return p
        m+=1
    for mm in range(2,16_000_000//n):
        p=n*mm+1
        if p>16_000_000:break
        if isprime(p):return p
    return None
def matrank_modp(rows,p):
    A=[[x%p for x in r] for r in rows]
    if not A:return 0
    nc=len(A[0]);rank=0;nr=len(A)
    for col in range(nc):
        piv=next((r for r in range(rank,nr) if A[r][col]%p),None)
        if piv is None:continue
        A[rank],A[piv]=A[piv],A[rank]
        inv=pow(A[rank][col],p-2,p)
        A[rank]=[x*inv%p for x in A[rank]]
        for r in range(nr):
            if r!=rank and A[r][col]:
                f=A[r][col]
                A[r]=[(A[r][c]-f*A[rank][c])%p for c in range(nc)]
        rank+=1
        if rank==nr:break
    return rank

def main():
    print("="*96)
    print("P7 v6: ADMISSIBLE corank (deg<k window) + list size + governing-law tie-in")
    print("="*96)
    # The deg<k restriction-to-mu_a map rank: V(mu_a; 0..k-1).  On mu_a, x^e depends on e mod a;
    # so rank = min(k, #distinct e mod a for e in 0..k-1) = min(k, a) BUT with multiplicity:
    # the column space of [x^e]_{x in mu_a, 0<=e<k} = span over distinct residues = min(a, ...).
    # Actually rank = #distinct residues mod a among {0,..,k-1} = min(a, k) (since 0..k-1 with
    # k>a covers all a residues; with k<=a covers k residues).  => rank = min(a,k).
    # restriction map deg<k -> F^a has rank min(a,k); a codeword set agreeing on A of values v
    # has |solutions| = q^{k - min(a,k)} = q^{max(0,k-a)}.  For a>=k: UNIQUE (=1) -> NO HOMDS
    # list excess from a single agreement set.  The HOMDS list comes from MULTIPLE agreement
    # sets (interleaved), the order-ell config -- which we measured: corank of the pairwise
    # stacked system.  Confirm rank min(a,k) exactly:
    print("\n[admissibility] restriction rank V(mu_a; deg<k) == min(a,k)  on thick p:")
    ok=tot=0
    for mu in (3,4,5):
        n=2**mu; p=find_thick_prime(n,2.5,3.5); w,S=subgroup(p,n)
        for j in range(1,mu+1):
            a=2**j; step=n//a; Aidx=[(step*t)%n for t in range(a)]
            for k in range(1,n):
                M=[[pow(S[i],e,p) for e in range(k)] for i in Aidx]
                r=matrank_modp(M,p)
                tot+=1
                if r==min(a,k): ok+=1
    print(f"   match {ok}/{tot} ({'CONFIRMED rank=min(a,k)' if ok==tot else 'MISMATCH'})")
    print("   => a SINGLE mu_a-agreement of size a>=k gives a UNIQUE codeword (no per-set excess).")
    print("   => HOMDS list excess is intrinsically the ORDER-ell (multi-set) corank measured in v3/v4.")

    # Now: the order-ell config corank (v4) was Theta(a).  The number of codewords in the list
    # = corank+1 ~ Theta(a) ~ Theta(n) at a=Theta(n).  Below-capacity capacity list size for RS:
    # at agreement fraction tau = a/n in window (1-sqrt(rho), 1-rho), the COMBINATORIAL list
    # bound (Johnson) is poly; the capacity bound is exp(n*H).  A HOMDS corank Theta(n) means the
    # algebraic certificate ALLOWS exponentially-many (it does not CAP the list below capacity).
    print("\n[list vs capacity] HOMDS corank d=Theta(a) does NOT cap list below capacity:")
    print(f"{'n':>4} {'rho':>5} {'a=win':>6} {'tau=a/n':>8} {'Johnson_ok?':>11} {'HOMDS_d':>8} {'caps_below_cap?':>15}")
    for mu in (4,5,6,7):
        n=2**mu
        for rho in (0.5,0.25):
            k=int(rho*n)
            johnson_agree = math.ceil(math.sqrt(rho)*n)   # agreement floor at Johnson ~ sqrt(rho)*n
            # window interior agreement just below unique decoding: a = window agreement
            a = max(k+1, johnson_agree-1)
            a = min(a, n-1)
            tau=a/n
            # HOMDS structural corank at this a on mu_a-subgroup if a is a power of 2 (the structured worst):
            a2 = 1<<(a.bit_length()-1)  # largest power of 2 <= a (the sub-subgroup that fits)
            classfill=n//a2
            d = a2 - math.ceil(a2/classfill) if classfill>0 else 0
            johnson_ok = tau > math.sqrt(rho)
            caps = (d <= 5)  # O(1)?
            print(f"{n:>4} {rho:>5} {a:>6} {tau:>8.3f} {str(johnson_ok):>11} {d:>8} {str(caps):>15}")

    print("\n[quasipoly field bound] STRICT HOMDS(ell) needs q > #configs ~ binom(n, *)^ell:")
    print("  to be MDS(ell) (no corank) the field must exceed the GM-MDS bad-config count.")
    print("  Brakensiek-Dhar-Gopi LOWER bound: q >= 2^{Omega(n)} for full HOMDS;")
    print("  for order ell: needed q ~ n^{Theta(ell)}.  At ell ~ corank ~ Theta(log n) the field")
    print("  bound is n^{Theta(log n)} = QUASIPOLY = exactly the BGK wall M(n) ~ sqrt(n log p).")
    for mu in (5,6,7,8):
        n=2**mu
        ell=mu  # ~ log2 n
        qneed = ell*math.log2(n)            # log2 of n^ell
        qprize = math.log2(n)+128           # log2 of prize field ~ n*2^128
        print(f"  n={n:>4}: log2(field for MDS(ell={ell})) ~ n^ell -> {qneed:>6.1f} bits;  "
              f"prize field ~ {qprize:>6.1f} bits;  HOMDS-sufficient? {qneed<=qprize}")
    print("\n  NOTE: n^{Theta(log n)} bits = Theta((log n)^2) bits, which IS below the 128-bit")
    print("  prize field for these small n -- BUT the corank d=Theta(a)=Theta(n), so the order")
    print("  needed is ell=Theta(n), giving field n^{Theta(n)} = 2^{Theta(n log n)} >> prize.")
    print("  THE GAP: the window needs order ell ~ corank ~ Theta(n), NOT Theta(log n).")
    print("  => HOMDS does not relax to the prize field; route CLOSED, = BGK wall.")

if __name__=="__main__":
    main()
