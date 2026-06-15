#!/usr/bin/env python3
"""LB2 next-lever: does any d=32 antipodal-free config achieve the FULL odd-descent
(all odd power sums =0 mod p) at prize scale => genuine V_32^prim point => R_32 bad reduction?
wf-LB showed p_1=0 configs exist (384/384) but only checked p_3!=0. Here we check the FULL
descent: is there ANY config with p_1=p_3=...=p_31=0 mod p (= an antipodal point mod p that is
char-0-antipodal-FREE)? That is the genuine Q1 obstruction at d=32."""
import itertools
def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True
def primes_1_mod_n(nn,lo,cap):
    out=[];p=lo|1
    while len(out)<cap:
        if (p-1)%nn==0 and is_prime(p): out.append(p)
        p+=2
    return out
def find_gen(p,nn):
    for g0 in range(2,p):
        w=pow(g0,(p-1)//nn,p)
        if pow(w,nn,p)==1 and all(pow(w,nn//q,p)!=1 for q in (2,3,5,7) if nn%q==0): return w
n=32; half=16
def cz_nonzero(Y):
    v=[0]*half
    for j in Y:
        e=j%n
        if e<half: v[e]+=1
        else: v[e-half]-=1
    return any(x!=0 for x in v)
print("LB2 next-lever: d=32 FULL odd-descent (genuine V_32^prim) at prize scale")
# Full C(32,size) is huge; use MITM on p_1=0 over antipodal-free, then filter full descent.
# We sample sizes; MITM by splitting the 16 antipodal pairs into two halves (3-way choice each).
def search(p, size_target=None, cap=2000000):
    w=find_gen(p,n)
    rv=[pow(w,j,p) for j in range(n)]
    # antipodal pairs (j, j+16); each contributes 0,+j,or +(j+16). MITM on p_1.
    pairs=list(range(half))
    L=half//2
    def gen(idxs):
        d={}
        for combo in itertools.product(range(3),repeat=len(idxs)):
            s=0; exps=[]
            for ci,t in zip(combo,idxs):
                if ci==1: s=(s+rv[t])%p; exps.append(t)
                elif ci==2: s=(s+rv[t+half])%p; exps.append(t+half)
            d.setdefault(s,[]).append(tuple(exps))
        return d
    left=gen(pairs[:L]); right=gen(pairs[L:])
    fulls=0; p1only=0; checked=0
    for ls,llist in left.items():
        tgt=(-ls)%p
        if tgt in right:
            for le in llist:
                for re in right[tgt]:
                    Y=le+re
                    if len(Y)<2: continue
                    if not cz_nonzero(Y): continue
                    checked+=1
                    p1only+=1
                    # full odd descent
                    if all(sum(pow(w,(a*j)%n,p) for j in Y)%p==0 for a in range(3,n,2)):
                        fulls+=1
                    if checked>=cap: break
                if checked>=cap: break
        if checked>=cap: break
    return p1only,fulls,checked
for p in primes_1_mod_n(32, 32**4, cap=4):
    p1,full,chk=search(p)
    print(f"  p={p} (~32^4): p1=0 configs (char0-nonzero)={p1}  FULL-descent(genuine V_32^prim)={full}  [checked {chk}]")
print("If FULL>0 at prize scale => R_32 bad reduction => Action-Orbit lane gated for prize d=32.")
print("If FULL=0 => d=32 also Q1-clean for the genuine obstruction (only p1-entry artifacts).")
