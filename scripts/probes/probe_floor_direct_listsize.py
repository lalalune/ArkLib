import itertools, random
# Direct worst-case list-size measurement for RS[mu_n, k] over F_p, radii spanning Johnson->capacity.
# Floor holds iff worst-case list stays <= budget(~n) below prizeDeltaStar.
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if h==1 or pow(h,n//2,p)==1: continue
        S=[];x=1
        for _ in range(n): x=(x*h)%p; S.append(x)
        if len(set(S))==n: return S
    return None
def rs_codewords(p,S,k):
    # all deg<k polys evaluated on S
    n=len(S); out=[]
    for coeffs in itertools.product(range(p),repeat=k):
        cw=tuple(sum(coeffs[j]*pow(x,j,p) for j in range(k))%p for x in S)
        out.append(cw)
    return out
def worst_list(p,S,k,r,nsamp=300000):
    n=len(S); C=rs_codewords(p,S,k)
    best=0; bestw=None
    # structured words: each codeword itself, and random words, and pairwise "centers"
    cands=set()
    for c in C: cands.add(c)
    rng=random.Random(12345)
    for _ in range(nsamp):
        cands.add(tuple(rng.randrange(p) for _ in range(n)))
        if len(cands)>nsamp: break
    # also: for random pairs of codewords, a word agreeing with c1 on half, c2 on half
    for _ in range(20000):
        c1=rng.choice(C); c2=rng.choice(C)
        w=tuple(c1[i] if i%2==0 else c2[i] for i in range(n)); cands.add(w)
    for w in cands:
        cnt=sum(1 for c in C if sum(1 for i in range(n) if c[i]!=w[i])<=r)
        if cnt>best: best=cnt; bestw=w
    return best
print("Direct worst-case list size of RS[mu_n,k]/F_p, r=floor(delta*n). Johnson=1-sqrt(rho).")
for (p,n,k) in [(17,8,2),(41,8,2),(41,8,4),(97,16,4)]:
    S=subgroup(p,n)
    if S is None: continue
    rho=k/n; from math import sqrt
    Jdelta=1-sqrt(rho); cap=1-rho
    print(f"\np={p} n={n} k={k} rho={rho:.2f} Johnson_delta={Jdelta:.3f}(r={int(Jdelta*n)}) cap_delta={cap:.3f}(r={int(cap*n)}) budget~n={n}")
    for r in range(int(Jdelta*n), int(cap*n)+1):
        if 2**(k*1.0) > 200000 and p>50: 
            # too many codewords; skip heavy
            pass
        wl=worst_list(p,S,k,r, nsamp=60000 if p**k>5000 else 200000)
        delta=r/n
        print(f"  r={r} delta={delta:.3f} | worst-case list size = {wl}  (budget {n})  {'<=budget' if wl<=n else 'EXCEEDS budget'}")
