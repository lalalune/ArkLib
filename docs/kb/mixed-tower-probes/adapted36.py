import itertools, cmath, random
n=36
roots=[cmath.exp(2j*cmath.pi*k/n) for k in range(n)]
# packets: mu_2 (k,k+18), mu_3 (k,k+12,k+24)
P2=[frozenset([k,(k+18)%36]) for k in range(18)]
P3=[frozenset([k,(k+12)%36,(k+24)%36]) for k in range(12)]
def decomps_sample(s, acc, out, limit=400):
    if len(out)>=limit: return
    if not s: out.append(acc); return
    k=min(s)
    cands=[P for P in P2+P3 if k in P and P<=s]
    random.shuffle(cands)
    for P in cands:
        decomps_sample(s-P, acc+[P], out, limit)
def win(S,t):
    return all(abs(sum(roots[k]**j for k in S))<1e-8 for j in range(1,t+1))
def spec_ok(D,t):
    R=[roots[min(P)]**2 for P in D if len(P)==2]
    return all(abs(sum(x**e for x in R))<1e-8 for e in range(1,t//2+1))
# alive cosets for t: mu_d-cosets, d|36, d>t
def coset(d, shift):
    return frozenset([(shift + j*(36//d))%36 for j in range(d)])
random.seed(7)
bad=0; tot=0
for t in (4,6,9):
    alive=[d for d in (2,3,4,6,9,12,18,36) if d>t]
    for trial in range(120):
        # random union of 1-4 alive cosets (disjoint)
        S=frozenset()
        for _ in range(random.randint(1,4)):
            d=random.choice(alive); sh=random.randrange(36)
            C=coset(d,sh)
            if C & S: continue
            S=S|C
        if not S or not win(S,t): continue
        xs=[x for x in S if frozenset([x,(x+18)%36])<=S]
        if not xs: continue
        x=random.choice(xs)
        orb=frozenset([x,(x+18)%36])
        outs=[]; decomps_sample(S-orb,[],outs)
        tot+=1
        if not any(spec_ok(D+[orb],t) for D in outs):
            bad+=1
            if bad<=4: print(f"NO-GOOD t={t} |S|={len(S)} x={x}")
print(f"cases: {tot}, no-good-completion: {bad}")
