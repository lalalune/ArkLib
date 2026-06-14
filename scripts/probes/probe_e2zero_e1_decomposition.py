import itertools
# n=2^mu. zeta^(n/2) = -1, basis {1,...,zeta^(n/2-1)}. e_1(A) -> integer vector length n/2.
def e1_vec(A,n):
    h=n//2; v=[0]*h
    for a in A:
        a%=n
        if a<h: v[a]+=1
        else: v[a-h]-=1
    return tuple(v)
def p2_vec(A,n):
    # sum zeta^{2a}; 2a mod n, reduce
    h=n//2; v=[0]*h
    for a in A:
        b=(2*a)%n
        if b<h: v[b]+=1
        else: v[b-h]-=1
    return tuple(v)
def e1_sq_vec(A,n):
    # (e1)^2 as element of Z[zeta]/(zeta^{n/2}+1): multiply the vector by itself
    h=n//2; v=e1_vec(A,n); out=[0]*h
    for i in range(h):
        if v[i]==0: continue
        for j in range(h):
            if v[j]==0: continue
            k=i+j; c=v[i]*v[j]
            if k<h: out[k]+=c
            else: out[k-h]-=c   # zeta^h=-1
    return tuple(out)
def valid(A,n):
    # e_2=0 <=> e1^2 = p2
    return e1_sq_vec(A,n)==p2_vec(A,n)
def analyze(n,w,cap=None):
    h=n//2
    e1set=set(); count=0
    elems=range(n)
    for A in itertools.combinations(elems,w):
        if valid(A,n):
            ev=e1_vec(A,n)
            if any(ev):  # e1 != 0
                e1set.add(ev); count+=1
            else:
                pass
    # dilation orbits: g in Z/n acts A->A+g (exponent shift), e1 -> zeta^g * e1
    # orbit count = #distinct e1 / orbit-size; compute orbits directly on e1set
    def rot(ev):  # multiply vector by zeta: shift, with wrap negation
        return tuple((-ev[h-1] if i==0 else ev[i-1]) for i in range(h))
    seen=set(); orbits=0
    for ev in e1set:
        if ev in seen: continue
        orbits+=1; cur=ev
        for _ in range(n):
            if cur in seen: break
            seen.add(cur); cur=rot(cur)
    return len(e1set), count, orbits
for n in [8,16]:
    for w in range(3, n//2+3):
        d,c,o=analyze(n,w)
        if d>0: print(f"n={n} w={w}: #valid-sets(e1≠0)={c:5d}  #distinct-e1={d:4d}  #dilation-orbits={o}")
