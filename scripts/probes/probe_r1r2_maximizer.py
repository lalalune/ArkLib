#!/usr/bin/env python3
"""R1/R2 test, OPTIMIZED: invert each Vandermonde ONCE per subset S, reuse across all stacks.
Tests: does a coset-structured stack (b-a | n) maximize the bad-scalar count at each window radius,
and does the worst-stack orbit-subgroup s=n/gcd(b-a,n) SHRINK as delta -> threshold? Proper subgroup."""
import itertools, math, sys

def is_prime(m):
    if m<2: return False
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return True
def find_q(n, beta):
    base=n**beta; m=base+((1-base)%n)
    while not((m-1)%n==0 and is_prime(m)): m+=n
    return m
def egcd(a,b):
    if b==0: return (a,1,0)
    g,x,y=egcd(b,a%b); return (g,y,x-(a//b)*y)
def inv(a,q):
    a%=q; g,x,_=egcd(a,q); return x%q
def subgroup(n,q):
    for cand in range(2,q):
        h=pow(cand,(q-1)//n,q)
        if pow(h,n,q)!=1: continue
        if n>1 and pow(h,n//2,q)==1: continue
        return [pow(h,i,q) for i in range(n)]
def matinv(M,q):
    t=len(M); A=[row[:]+[1 if i==j else 0 for j in range(t)] for i,row in enumerate(M)]
    for c in range(t):
        piv=next((r for r in range(c,t) if A[r][c]%q),None)
        if piv is None: return None
        A[c],A[piv]=A[piv],A[c]; ip=inv(A[c][c],q); A[c]=[(x*ip)%q for x in A[c]]
        for r in range(t):
            if r!=c and A[r][c]%q:
                f=A[r][c]; A[r]=[(A[r][j]-f*A[c][j])%q for j in range(2*t)]
    return [row[t:] for row in A]

def analyze(n,rho_num,rho_den,beta):
    q=find_q(n,beta); elts=subgroup(n,q); k=max(1,(n*rho_num)//rho_den)
    print(f"\n=== n={n}, q={q} (~n^{beta}, PROPER mu_{n}), rho={rho_num}/{rho_den}, k={k} ===",flush=True)
    XS=[[pow(x,a,q) for a in range(n)] for x in elts]  # XS[i][a]=elts[i]^a
    tau_j=int(math.sqrt(rho_num/rho_den)*n)
    taus=[t for t in range(k+1,min(tau_j+1,n)) ]
    if not taus: taus=[k+1]
    for tau in taus:
        # per stack accumulate set of valid alphas
        bad={}  # (a,b)->set(alpha)
        for Sidx in itertools.combinations(range(n),tau):
            S=[elts[i] for i in Sidx]
            V=[[pow(x,j,q) for j in range(tau)] for x in S]
            Vi=matinv(V,q)
            if Vi is None: continue
            W=Vi[k:tau]                       # rows k..tau-1 : (tau-k) x tau
            # M[r][a] = sum_i W[r][i]*XS[Sidx[i]][a]  -> (tau-k) x n
            M=[[sum(W[r][i]*XS[Sidx[i]][a] for i in range(tau))%q for a in range(n)] for r in range(tau-k)]
            for a in range(n):
                for b in range(a+1,n):
                    al=None; ok=True
                    for r in range(tau-k):
                        pj=M[r][a]; qj=M[r][b]
                        if qj%q==0:
                            if pj%q: ok=False; break
                        else:
                            v=(-pj*inv(qj,q))%q
                            if al is None: al=v
                            elif al!=v: ok=False; break
                    if ok and al is not None and al%q!=0:
                        bad.setdefault((a,b),set()).add(al)
        rows=[]
        for (a,b),st in bad.items():
            g=math.gcd(b-a,n); s=n//g; coset=((b-a)!=0 and n%(b-a)==0)
            rows.append((len(st),a,b,b-a,g,s,coset))
        if not rows:
            print(f" tau={tau} (delta={1-tau/n:.3f}): NO bad scalars for any stack",flush=True); continue
        rows.sort(reverse=True); mx=rows[0][0]
        win=[r for r in rows if r[0]==mx]
        ncos=[r for r in rows if not r[6]]
        topnc=ncos[0] if ncos else None
        any_c=any(w[6] for w in win)
        refuted = (topnc is not None and topnc[0]>mx)  # non-coset STRICTLY beats every coset
        worst_s=min(w[5] for w in win)   # smallest orbit-subgroup among maximizers
        print(f" tau={tau} (delta={1-tau/n:.3f}): max={mx}  worst-stack s∈{{{','.join(str(w[5]) for w in win[:5])}}}  coset achieves max={any_c}  R1/R2-REFUTED={refuted}",flush=True)
        print(f"     top maximizers (a,b,b-a,s,coset): {[(w[1],w[2],w[3],w[5],w[6]) for w in win[:4]]}",flush=True)
        if topnc: print(f"     best NON-coset: (a={topnc[1]},b={topnc[2]},b-a={topnc[3]},s={topnc[5]}) count={topnc[0]} vs max {mx}",flush=True)

if __name__=="__main__":
    analyze(8,1,4,4); analyze(8,1,2,4)
    analyze(16,1,4,3); analyze(16,1,2,3)
