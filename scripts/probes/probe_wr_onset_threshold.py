#!/usr/bin/env python3
"""probe_wr_onset_threshold.py (#444) — the char-p energy excess W_r is an ONSET THRESHOLD, not
Fermat. W_r = E_r(F_p) - E_r(char-0). Computes W_2,W_3,W_4 for n=16 across primes; shows W_r=0
for p above the r-th wraparound threshold (incl. all prize-scale p>~n^4), nonzero below. Confirms
W_3=0 for prize primes => di Benedetto T_3=O(n^3) conditional discharged at prize scale."""
from collections import defaultdict
def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
def subgroup(n,p):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if pow(h,n,p)==1 and all(pow(h,n//q,p)!=1 for q in [2] if n%q==0):
            return [pow(h,i,p) for i in range(n)]
def energy(n,p,rmax):
    S=subgroup(n,p); cur=defaultdict(int)
    for x in S: cur[x]+=1
    Es={1:n}
    for r in range(2,rmax+1):
        nxt=defaultdict(int)
        for t,c in cur.items():
            for x in S: nxt[(t+x)%p]+=c
        cur=nxt; Es[r]=sum(c*c for c in cur.values())
    return Es
def char0(r,n):
    return {2:3*n**2-3*n,3:15*n**3-45*n**2+40*n,4:105*n**4-630*n**3+1435*n**2-1155*n}[r]
if __name__=="__main__":
    n=16; c={r:char0(r,n) for r in [2,3,4]}
    print(f"n={n} char-0 E2/E3/E4 = {c[2]}/{c[3]}/{c[4]}")
    print(f"{'p':>8} {'p>n^4?':>7} | W2 W3 W4")
    for p in [97,193,257,65537,70657,196657,786433]:
        if not(p%n==1 and isprime(p)): continue
        Es=energy(n,p,4)
        print(f"{p:>8} {str(p>n**4):>7} | {Es[2]-c[2]} {Es[3]-c[3]} {Es[4]-c[4]}")
