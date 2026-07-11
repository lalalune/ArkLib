import itertools
# Verify P(zeta)^2 = P(zeta^2) characterization == e_2=0 (valid_fast), and confirm n=64 s_max.
def poly_eval_vec(coeffs_exp, n):
    # element of Z[zeta_n]/(zeta^{n/2}+1): return length-h vector
    h=n//2; v=[0]*h
    for a,c in coeffs_exp:
        a%=n
        if a<h: v[a]+=c
        else: v[a-h]-=c
    return tuple(v)
def Pzeta_sq_minus_Pzeta2(A,n):
    h=n//2
    # P(zeta)^2 : sum over a,a' zeta^{a+a'}
    v=[0]*h
    for a in A:
        for b in A:
            e=(a+b)%n
            if e<h: v[e]+=1
            else: v[e-h]-=1
    # P(zeta^2): sum zeta^{2a}
    for a in A:
        e=(2*a)%n
        if e<h: v[e]-=1
        else: v[e-h]+=1
    return all(x==0 for x in v)
def valid_fast(A,n):
    h=n//2; r=[0]*n
    for i in range(len(A)):
        for j in range(i+1,len(A)): r[(A[i]+A[j])%n]+=1
    for c in range(h):
        if r[c]!=r[c+h]: return False
    return True
# verify equivalence on n=16 all subsets up to size 9
import random
n=16; bad=0; checked=0
for w in range(2,10):
    for A in itertools.combinations(range(n),w):
        if valid_fast(A,n)!=Pzeta_sq_minus_Pzeta2(A,n): bad+=1
        checked+=1
print(f"equivalence P(z)^2=P(z^2) <=> e_2=0 : checked {checked}, mismatches={bad}")

# n=64 s_max via balance criterion (s=5 and s=6 only)
def s_exists(n,s):
    h=n//2
    for classes in itertools.combinations(range(h),s):
        for signs in itertools.product([0,1],repeat=s):
            Q=[classes[t]+signs[t]*h for t in range(s)]
            r=[0]*n
            for i in range(s):
                for j in range(i+1,s): r[(Q[i]+Q[j])%n]+=1
            ok=True; need=[]
            for c in range(h):
                d=r[c]-r[c+h]
                if c%2==1:
                    if d!=0: ok=False;break
                else:
                    if abs(d)>1: ok=False;break
                    if d==1: need.append(c+h)
                    elif d==-1: need.append(c)
            if not ok: continue
            uc=set(classes); idx=set(); good=True
            for p in need:
                placed=False
                for i in range(h):
                    if (2*i+h)%n==p and i not in uc and i not in idx: idx.add(i);placed=True;break
                if not placed: good=False;break
            if good: return True
    return False
import time
for s in [5,6]:
    t=time.time(); e=s_exists(64,s)
    print(f"n=64 s={s}: exists={e}  ({time.time()-t:.0f}s)", flush=True)
