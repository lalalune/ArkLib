#!/usr/bin/env python3
"""FRESH HYPOTHESIS probe: the bad count at the jump radius 1-(k+1)/n for the stack
u0 = eval x^{k+1}, u1 = eval x^k equals the number of DISTINCT (k+1)-subset SUMS of the domain.
Test: (a) does the explicit bad count = #distinct subset sums? (b) do smooth subgroups have
FEWER (collisions) than generic/Sidon domains? If yes, smooth-is-better, domain-dependent at the
jump, paperworthy. Pre-registered, exact arithmetic."""
import itertools

def is_prime(n):
    return n>1 and all(n%d for d in range(2,int(n**0.5)+1))

def mult_subgroup(p,n):
    for cand in range(2,p):
        o=1;y=cand%p
        while y!=1: y=(y*cand)%p; o+=1
        if o==p-1: g=cand;break
    h=pow(g,(p-1)//n,p); return sorted({pow(h,i,p) for i in range(n)})

def evalpoly(coeffs,x,p): return sum(c*pow(x,i,p) for i,c in enumerate(coeffs))%p

def rref(mat,p):
    m=[r[:] for r in mat];rows=len(m);cols=len(m[0]) if m else 0;piv=[];r=0
    for c in range(cols):
        pr=None
        for i in range(r,rows):
            if m[i][c]%p: pr=i;break
        if pr is None: continue
        m[r],m[pr]=m[pr],m[r];inv=pow(m[r][c],p-2,p);m[r]=[(v*inv)%p for v in m[r]]
        for i in range(rows):
            if i!=r and m[i][c]%p: f=m[i][c];m[i]=[(a-f*b)%p for a,b in zip(m[i],m[r])]
        piv.append(c);r+=1
        if r==rows: break
    return m[:r],piv

def interp_deglt_k(D,vals,k,p,S):
    """does some deg<k poly agree with vals on coords S? Vandermonde feasibility."""
    Sl=sorted(S)
    V=[[pow(D[j],i,p) for i in range(k)]+[vals[j]] for j in Sl]
    R,piv=rref(V,p)
    for row in R:
        if all(row[c]%p==0 for c in range(k)) and row[k]%p!=0: return False
    return True

def bad_count_jump(p,D,k):
    """exact bad count at radius 1-(k+1)/n for stack u0=x^{k+1}, u1=x^k; witness floor = k+1."""
    n=len(D)
    u0=[evalpoly([0]*(k+1)+[1],D[j],p) for j in range(n)]  # x^{k+1}
    u1=[evalpoly([0]*k+[1],D[j],p) for j in range(n)]      # x^k
    badset=set()
    Ssize=k+1
    Slist=list(itertools.combinations(range(n),Ssize))
    for gamma in range(p):
        lp=[(u0[j]+gamma*u1[j])%p for j in range(n)]
        # bad if exists (k+1)-set S: lp agrees with deg<k codeword on S, but line not jointly close
        bad=False
        for S in Slist:
            if interp_deglt_k(D,lp,k,p,S):
                # joint: both u0,u1 interp deg<k on S?
                if not (interp_deglt_k(D,u0,k,p,S) and interp_deglt_k(D,u1,k,p,S)):
                    bad=True;break
        if bad: badset.add(gamma)
    return len(badset)

def distinct_subset_sums(D,t,p):
    return len({sum(c)%p for c in itertools.combinations(D,t)})

print("JUMP bad count vs #distinct (k+1)-subset sums:  smooth subgroup vs random",flush=True)
print(f"{'p':>4} {'n':>3} {'k':>2} {'domain':>8} {'badcount':>9} {'#distinct-sums':>14} {'C(n,k+1)':>9} {'match?':>7}",flush=True)
import random; random.seed(5)
for (p,n,k) in [(13,4,2),(13,6,2),(13,4,3),(17,8,3)]:
    if (p-1)%n: continue
    H=mult_subgroup(p,n)
    R=sorted(random.sample([x for x in range(1,p)],n))
    for lbl,D in [("smooth",H),("random",R)]:
        bc=bad_count_jump(p,D,k)
        ds=distinct_subset_sums(D,k+1,p)
        from math import comb
        cnk=comb(n,k+1)
        print(f"{p:>4} {n:>3} {k:>2} {lbl:>8} {bc:>9} {ds:>14} {cnk:>9} {str(bc==ds):>7}",flush=True)
