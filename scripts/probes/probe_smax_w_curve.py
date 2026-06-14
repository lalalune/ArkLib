import itertools
from collections import Counter
def valid_fast(A,n):
    h=n//2; r=[0]*n
    for i in range(len(A)):
        for j in range(i+1,len(A)): r[(A[i]+A[j])%n]+=1
    for c in range(h):
        if r[c]!=r[c+h]: return False
    return True
def singles(A,n):
    h=n//2; S=set(A); return sum(1 for a in A if (a+h)%n not in S)
def e1(A,n):
    h=n//2; v=[0]*h
    for a in A: v[a%h]+= (1 if a<h else -1)
    return tuple(v)
def curve(n, wmax):
    out={}
    for w in range(2, wmax+1):
        e1s=set(); smax=0; cnt=0
        for A in itertools.combinations(range(n),w):
            if valid_fast(A,n):
                ev=e1(A,n)
                if any(ev):
                    e1s.add(ev); smax=max(smax,singles(A,n)); cnt+=1
        if cnt: out[w]=(len(e1s), smax)
    return out
print("n=16 s_max(w) curve [w: (#distinct-e1, s_max)]:")
c16=curve(16,16)
for w,(d,s) in c16.items(): print(f"  w={w:2d} (ρ=(w-2)/16={ (w-2)/16:.3f}): #bad={d:4d}  s_max={s}", flush=True)
print("n=32 s_max(w) curve (w<=9 feasible):")
c32=curve(32,9)
for w,(d,s) in c32.items(): print(f"  w={w:2d} (ρ={(w-2)/32:.3f}): #bad={d:5d}  s_max={s}", flush=True)
