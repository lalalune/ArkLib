import itertools
def valid_fast(A,n):
    h=n//2; r=[0]*n
    for i in range(len(A)):
        for j in range(i+1,len(A)): r[(A[i]+A[j])%n]+=1
    for c in range(h):
        if r[c]!=r[c+h]: return False
    return True
def e2_is_zero_via_poly(A,n):
    # P(zeta)^2 == P(zeta^2) independent check
    h=n//2; v=[0]*h
    for a in A:
        for b in A:
            e=(a+b)%n
            v[e%h]+= (1 if e<h else -1)
    for a in A:
        e=(2*a)%n; v[e%h]-= (1 if e<h else -1)
    return all(x==0 for x in v)
def s_exists_ret(n,s):
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
            if good:
                # reconstruct full A
                A=list(Q)
                for i in idx: A+= [i, i+h]
                return sorted(set(A)), Q, sorted(idx)
    return None,None,None
n=64
for s in [5,6]:
    A,Q,F=s_exists_ret(n,s)
    if A:
        # count singles in reconstructed A
        S=set(A); sing=[a for a in A if (a+32)%64 not in S]
        v=valid_fast(A,n); v2=e2_is_zero_via_poly(A,n)
        print(f"n=64 s={s}: |A|={len(A)} #singles={len(sing)} valid_fast={v} poly_e2zero={v2}")
        print(f"   A={A}")
        print(f"   singles positions={sing}")
