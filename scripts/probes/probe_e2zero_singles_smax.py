import itertools
from collections import Counter
def valid_fast(A,n):
    h=n//2; r=[0]*n; L=len(A)
    for i in range(L):
        for j in range(i+1,L): r[(A[i]+A[j])%n]+=1
    for c in range(h):
        if r[c]!=r[c+h]: return False
    return True
def singles_count(A,n):
    h=n//2; S=set(A); s=0
    for a in A:
        if a<h:
            if (a+h) not in S: s+=1
        else:
            if (a-h) not in S: s+=1
    return s
def analyze(n,w):
    sc=Counter(); 
    for A in itertools.combinations(range(n),w):
        if valid_fast(A,n):
            sc[singles_count(A,n)]+=1
    return dict(sorted(sc.items()))
print("singles-count (s) distribution among valid e2=0 sets:")
for n in [8,16]:
    for w in range(3,n+1):
        sc=analyze(n,w)
        if sc: print(f"  n={n} w={w:2d}: s-distribution {sc}   max-s={max(sc) if sc else '-'}")
