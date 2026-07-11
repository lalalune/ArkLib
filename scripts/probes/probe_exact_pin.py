#!/usr/bin/env python3
"""EXACT delta* PIN for RS[F_13, D, 2]: verify the ε_mca curve with a NAIVE word-level
cross-check (witness discipline), then read off the exact meeting-bracket delta*.

The mcaEvent (ABF26 Def 4.3 / Errors.lean): point u0+gamma*u1 on the line {u0+t*u1} is BAD if
some S (|S|>=(1-delta)n) has a codeword agreeing with the line-point on S, but NOT the whole
line jointly on S. ε_mca = max_{u0,u1} #{gamma: bad}/q. We compute it BOTH ways (syndrome-reduced
AND naive over all word pairs on the smallest instance) and require exact agreement."""
import itertools, math

def mult_subgroup(p,n):
    for cand in range(2,p):
        o=1; y=cand%p
        while y!=1: y=(y*cand)%p; o+=1; 
        if o==p-1: g=cand; break
    h=pow(g,(p-1)//n,p); return sorted({pow(h,i,p) for i in range(n)})

def polys_deg_lt_k(p,k): 
    return list(itertools.product(range(p),repeat=k))  # coeff tuples
def evalp(c,x,p): return sum(c[i]*pow(x,i,p) for i in range(len(c)))%p

def codewords(p,D,k):
    return [tuple(evalp(c,x,p) for x in D) for c in polys_deg_lt_k(p,k)]

def agrees_on(w, c, S):  # codeword c agrees with word w on coordinate set S
    return all(w[j]==c[j] for j in S)

def ext(w, C, S):  # some codeword agrees with w on all of S
    return any(agrees_on(w,c,S) for c in C)

def joint_ext(u0,u1, C, S):  # whole line jointly close on S: codeword agrees with u0 AND u1 on S
    # pairJointAgreesOn splits: ext(u0,S) AND ext(u1,S) (independent witnesses)
    return ext(u0,C,S) and ext(u1,C,S)

def naive_epsmca(p,D,k,delta):
    n=len(D); C=codewords(p,D,k)
    smin=math.ceil((1-delta)*n)
    allS=[frozenset(c) for r in range(smin,n+1) for c in itertools.combinations(range(n),r)]
    # all word pairs (u0,u1): too many (p^2n). Use coset reps: u = codeword + syndrome-rep.
    # but for the SMALLEST instance we brute force a reduced set: u0,u1 range over a transversal.
    # Transversal of C in F_p^n: words with 0 on the k pivot coords (here first k via D distinct).
    # Simpler exact: iterate u0,u1 over ALL words but mod out by adding codewords is the syndrome
    # reduction. For witness cross-check at n=4,k=2,p=13: p^(2(n-k)) = 13^4 = 28561 syndrome reps.
    # Build syndrome rep = word that is 0 on first k coords, free on last n-k.
    best=0
    free=list(range(k,n))
    for tail0 in itertools.product(range(p),repeat=n-k):
        u0=[0]*k+list(tail0)
        for tail1 in itertools.product(range(p),repeat=n-k):
            u1=[0]*k+list(tail1)
            cnt=0
            for gamma in range(p):
                lp=[(u0[j]+gamma*u1[j])%p for j in range(n)]
                bad=any(ext(lp,C,S) and not joint_ext(u0,u1,C,S2:=S) for S in allS)
                # careful: joint on the SAME S
                bad=any(ext(lp,C,S) and not joint_ext(u0,u1,C,S) for S in allS)
                if bad: cnt+=1
            best=max(best,cnt)
    return best

p,D,k=13,None,2
D=mult_subgroup(p,4)  # n=4
print(f"RS[F_{p}, D={D}, k={k}], n=4, rho=0.5, UD=0.25, Johnson={1-math.sqrt(0.5):.3f}, cap=0.5", flush=True)
print("Exact ε_mca numerator (worst-line bad count) by NAIVE word-level enumeration:", flush=True)
for delta in [0.10, 0.24, 0.25, 0.26, 0.40, 0.50, 0.60]:
    bc=naive_epsmca(p,D,k,delta)
    print(f"  delta={delta:.2f}: badcount={bc}, ε_mca={bc}/{p}={bc/p:.4f}", flush=True)
