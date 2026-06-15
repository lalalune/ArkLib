#!/usr/bin/env python3
"""LB2: pin the EXACT bad-reduction threshold at d=16. The spurious p_1=0 configs at
small p — do they (a) persist to prize scale, (b) form genuine gap-variety points
(p_1=p_3=...=0, the route-i full descent), or (c) are they only the p_1=0 entry that
the higher-odd-vanishing kills? This is the direct Q1/resultant question."""
import itertools
from math import gcd, log

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True
def primes_1_mod_n(nn, lo, cap):
    out=[]; p=lo|1
    while len(out)<cap:
        if (p-1)%nn==0 and is_prime(p): out.append(p)
        p+=2
    return out
def find_gen(p,nn):
    for g0 in range(2,p):
        w=pow(g0,(p-1)//nn,p)
        if pow(w,nn,p)==1 and all(pow(w,nn//q,p)!=1 for q in (2,3,5,7) if nn%q==0): return w
n=16; half=8

def coordvec_nonzero(Y):
    v=[0]*half
    for j in Y:
        e=j%n
        if e<half: v[e]+=1
        else: v[e-half]-=1
    return any(x!=0 for x in v)

def spurious_at_p(p, require_full=False):
    """antipodal-free, char0-nonzero, p_1=0 mod p. If require_full also p_3,p_5,p_7=0 (route-i
    full odd descent => genuine V_16^prim point => true Q1 obstruction)."""
    w=find_gen(p,16)
    PW=[[pow(w,(a*j)%n,p) for j in range(n)] for a in range(n)]
    out=[]; fullout=[]
    for size in range(2,half+1):
        for Y in itertools.combinations(range(n),size):
            Ys=set(Y)
            if any(((j+half)%n) in Ys for j in Y): continue
            if not coordvec_nonzero(Y): continue
            if sum(PW[1][j] for j in Y)%p!=0: continue
            out.append((Y,size))
            # full odd descent: all odd power sums vanish => genuine antipodal point mod p
            if all(sum(PW[a][j] for j in Y)%p==0 for a in range(3,n,2)):
                fullout.append((Y,size))
    return out, fullout

print("="*88)
print("LB2: exact bad-reduction threshold for the d=16 p_1=0 slice + genuine-Vprim test")
print("="*88)
# Scan increasing primes, record where spurious-p1 count drops to 0, and whether any FULL point.
print("\np_1=0 entry spurious (antipodal-free, char0-nonzero) vs FULL odd-descent (genuine V_16^prim):")
last_spurious=0
for lo in [256, 512, 1024, 2048, 4096, 8192, 16384, 65536, 16**5, 2**24]:
    ps=primes_1_mod_n(16, lo, cap=4)
    for p in ps:
        sp, full = spurious_at_p(p)
        if sp: last_spurious=p
        ex = sp[0] if sp else None
        print(f"  p={p:>10} (~2^{round(log(p,2),1)}): p1-spurious={len(sp):4d}"
              f"{' e.g.'+str(ex) if ex else ''}   FULL-Vprim(genuine Q1 obstruction)={len(full)}"
              + ("  <-- !!! GENUINE" if full else ""))
print(f"\nLargest prime with ANY p_1=0 spurious (antipodal-free) config: {last_spurious}")
print("If FULL-Vprim is always 0 => the p_1=0 entries are NOT genuine gap-variety points:")
print("the higher odd-power vanishing (route-i descent / full odd-symmetric) kills them => Q1 HOLDS at d=16.")
