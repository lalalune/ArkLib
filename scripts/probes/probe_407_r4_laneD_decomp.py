import itertools

def primitive_root(p):
    phi=p-1; fac=set(); m=phi; d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g
def isprime(n):
    if n<2: return False
    d=2
    while d*d<=n:
        if n%d==0: return False
        d+=1
    return True
def mun(n,p):
    g=primitive_root(p); b=pow(g,(p-1)//n,p)
    return [pow(b,i,p) for i in range(n)]
def find_prize_prime(n, lo):
    p=lo
    while True:
        if (p-1)%n==0 and isprime(p): return p
        p+=1

# Hypothesis: every w=5 e2=0 set in mu_n (4|n) = (a 4-element coset of mu_4) UNION {one extra point}
# mu_4 in exponent terms = {0, n/4, n/2, 3n/4}. cosets = {j, j+n/4, j+n/2, j+3n/4}.
for n in [8,12,16,20,24]:
    if n%4: continue
    p=find_prize_prime(n,n**3)
    mu=mun(n,p)
    h=n//4
    ok_all=True
    total=0
    for S in itertools.combinations(range(n),5):
        vals=[mu[i] for i in S]
        e1=sum(vals)%p
        if e1==0: continue
        p2=sum((x*x)%p for x in vals)%p
        if (e1*e1-p2)%p!=0: continue
        total+=1
        # check: does S contain a full coset of mu_4 (exponent AP with diff n/4)?
        found_coset=False
        for j in range(h):  # coset reps
            coset={j,(j+h)%n,(j+2*h)%n,(j+3*h)%n}
            if coset<=set(S):
                found_coset=True; break
        if not found_coset: ok_all=False
    print(f"n={n} p={p}: total w5 e2=0 sets={total}, ALL decompose as mu_4-coset + point: {ok_all}")

# Also: does the EXTRA point matter, or is ANY mu_4-coset + ANY point an e2=0 set?
print("\n=== Is (mu_4-coset) ∪ {any point} automatically e2=0? ===")
for n in [8,12,16]:
    p=find_prize_prime(n,n**3); mu=mun(n,p); h=n//4
    cosrep=0
    coset_exp={cosrep,(cosrep+h)%n,(cosrep+2*h)%n,(cosrep+3*h)%n}
    coset_vals=[mu[i] for i in coset_exp]
    cnt_e2zero=0; cnt_tested=0
    for extra in range(n):
        if extra in coset_exp: continue
        S=coset_vals+[mu[extra]]
        e1=sum(S)%p
        if e1==0: continue
        cnt_tested+=1
        p2=sum((x*x)%p for x in S)%p
        if (e1*e1-p2)%p==0: cnt_e2zero+=1
    print(f"  n={n}: coset(rep 0) ∪ {{extra}}: e2=0 for {cnt_e2zero}/{cnt_tested} extras")
