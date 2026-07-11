#!/usr/bin/env python3
"""#357 exactness-converse lane: the EXPLICIT 14 matching patterns + congruence systems.

Recomputes (and records in full — C8/C9 stored only M1/M4/M6) the matching-pattern
census of the wide-circuit classification, the per-pattern congruence systems, the
class-profile structure, the collision profiles, and verifies the two structural
kill-lemmas of the claimed Lean route:

  K1 (equal products): a balanced Distinct6 triple with exactly two equal m's is
      IMPOSSIBLE (the m-multiplicity is 1 or 3) — "partial horizontal collapse" is empty.
  K2 (equal sums): a balanced Distinct6 triple with exactly two equal e-values is
      IMPOSSIBLE (the e-value multiplicity is 1 or 3) — "partial vertical collapse" empty.

Pre-registered expectations (from the C8/C9 notes + the class-profile derivation):
  E1: exactly 14 multiplicity-free patterns at n=16 and n=32, identical lists;
  E2: stratification 1 vertical + 1 horizontal + 4 family + 8 second-layer;
  E3: each pattern's congruence system dedupes to exactly 3 congruences;
  E4: collision profiles among balanced Distinct6 triples are exactly
      (2,2,1^8), (2^4,1^4), (2^6);
  E5: K1/K2 hold (zero partial-collapse configs).
"""
from itertools import combinations

# symbol order: a1 b1 a2 b2 a3 b3
EXPVEC = [
    (0,0,1,0,1,1), (0,0,0,1,1,1),    # e2*m3  [+]
    (1,1,1,0,0,0), (1,1,0,1,0,0),    # e2*m1  [-]
    (1,0,0,0,1,1), (0,1,0,0,1,1),    # e1*m3  [-]
    (0,0,1,1,1,0), (0,0,1,1,0,1),    # e3*m2  [-]
    (1,0,1,1,0,0), (0,1,1,1,0,0),    # e1*m2  [+]
    (1,1,0,0,1,0), (1,1,0,0,0,1),    # e3*m1  [+]
]
SIGN = [1,1,-1,-1,-1,-1,-1,-1,1,1,1,1]
# m-class of each index (which s_j the term carries): s3,s3,s1,s1,s3,s3,s2,s2,s2,s2,s1,s1
MCLASS = [3,3,1,1,3,3,2,2,2,2,1,1]

def exps(P1,P2,P3):
    (a1,b1),(a2,b2),(a3,b3) = P1,P2,P3
    v = (a1,b1,a2,b2,a3,b3)
    return [sum(c*x for c,x in zip(vec,v)) for vec in EXPVEC]

def shifted(n, P1,P2,P3):
    h = n//2
    E = exps(P1,P2,P3)
    return [ (E[i] + (0 if SIGN[i]==1 else h)) % n for i in range(12) ]

def balanced(n, P1,P2,P3):
    h = n//2
    cnt = [0]*n
    for r in shifted(n,P1,P2,P3): cnt[r]+=1
    return all(cnt[t]==cnt[t+h] for t in range(h))

def e_fold(n,i,j):
    h=n//2; c=[0]*h
    for ex in (i,j):
        r=ex%n
        if r<h: c[r]+=1
        else: c[r-h]-=1
    return tuple(c)

def stratum(n, T):
    ms = {(i+j)%n for (i,j) in T}
    es = {e_fold(n,i,j) for (i,j) in T}
    if len(ms)==1: return 'H'
    if len(es)==1: return 'V'
    if len(ms)==2 or len(es)==2: return 'PARTIAL'   # K1/K2 say this never happens
    return 'S'

def pattern_and_profile(n, T):
    sh = shifted(n,*T)
    h = n//2
    from collections import Counter
    cnt = Counter(sh)
    profile = tuple(sorted(cnt.values(), reverse=True))
    if max(cnt.values())==1:
        pos = {r:i for i,r in enumerate(sh)}
        pairs = set()
        for i,r in enumerate(sh):
            j = pos[(r+h)%n]
            pairs.add(frozenset((i,j)))
        assert len(pairs)==6
        return frozenset(pairs), profile
    return None, profile

def congruence_system(pat):
    """Per matching pair: same-sign -> exp_x - exp_y = h; cross-sign -> exp_x - exp_y = 0.
    Returns deduped canonical congruences as (6-tuple over symbols, hflag)."""
    sys_ = set()
    for pr in pat:
        x,y = sorted(pr)
        vec = tuple(EXPVEC[x][k]-EXPVEC[y][k] for k in range(6))
        hflag = 1 if SIGN[x]==SIGN[y] else 0
        neg = tuple(-c for c in vec)
        sys_.add(min((vec,hflag),(neg,hflag)))
    return sorted(sys_)

def class_profile(pat):
    from collections import Counter
    c = Counter()
    for pr in pat:
        x,y = sorted(pr)
        c[tuple(sorted((MCLASS[x],MCLASS[y])))]+=1
    return tuple(sorted(c.items()))

def fmt_congr(con):
    names = ['a1','b1','a2','b2','a3','b3']
    vec,hf = con
    terms=[]
    for c,nm in zip(vec,names):
        if c==0: continue
        if c==1: terms.append('+'+nm)
        elif c==-1: terms.append('-'+nm)
        else: terms.append(f'{c:+d}{nm}')
    s=''.join(terms).lstrip('+')
    return f"{s} = {'h' if hf else '0'}"

def collinear_triples_modp(n, p):
    g = next(c for c in range(2,p) if pow(c,n,p)==1 and pow(c,n//2,p)!=1)
    pts = list(combinations(range(n),2))
    em = {P: ((pow(g,P[0],p)+pow(g,P[1],p))%p, pow(g,P[0]+P[1],p)) for P in pts}
    from collections import defaultdict
    lines = defaultdict(list)
    for i in range(len(pts)):
        for j in range(i+1,len(pts)):
            (e1,m1),(e2,m2) = em[pts[i]], em[pts[j]]
            if e1==e2:
                key=('v',e1)
            else:
                sl = (m2-m1)*pow(e2-e1,p-2,p)%p
                key=('s',sl,(m1-sl*e1)%p)
            lines[key].append((i,j))
    seen=set()
    for key, prs in lines.items():
        members=set()
        for (i,j) in prs: members.add(i); members.add(j)
        if len(members)<3: continue
        for T in combinations(sorted(members),3):
            if T in seen: continue
            seen.add(T)
            yield (pts[T[0]],pts[T[1]],pts[T[2]])

def run(n, p):
    pat_strat = {}
    coll = {}
    partial = []
    nbal=0
    for T in collinear_triples_modp(n,p):
        P1,P2,P3 = T
        if len({*P1,*P2,*P3})!=6: continue
        if not balanced(n,P1,P2,P3): continue   # char-0 filter kills mod-p surplus
        nbal+=1
        st = stratum(n,T)
        if st=='PARTIAL': partial.append(T)
        pat, prof = pattern_and_profile(n,T)
        if pat is None:
            coll.setdefault((prof,st),[]).append(T)
        else:
            pat_strat.setdefault(pat,{}).setdefault(st,[]).append(T)
    return nbal, pat_strat, coll, partial

print("== n=16 (p=12289) ==")
n16 = run(16,12289)
print("balanced Distinct6 triples:", n16[0])
print("PARTIAL configs (K1/K2 falsifier — expect 0):", len(n16[3]))
print("== n=32 (p=40961) ==")
n32 = run(32,40961)
print("balanced Distinct6 triples:", n32[0])
print("PARTIAL configs (K1/K2 falsifier — expect 0):", len(n32[3]))

def report(tag, res):
    nbal, ps, coll, _ = res
    print(f"\n--- {tag}: {len(ps)} multiplicity-free patterns ---")
    for k,(pat,sts) in enumerate(sorted(ps.items(), key=lambda kv: sorted(map(sorted,kv[0])))):
        prs = '('+')('.join(' '.join(map(str,sorted(pr))) for pr in sorted(map(sorted,pat)))+')'
        strs = {s:len(v) for s,v in sts.items()}
        sys_=congruence_system(pat)
        print(f"P{k}: {prs}  strata={strs}  classprof={class_profile(pat)}")
        for con in sys_: print("      ", fmt_congr(con))
        ex = next(iter(next(iter(sts.values()))))
        print("       example:", ex)
    print("--- collision profiles ---")
    for (prof,st),v in sorted(coll.items()):
        print(f"  profile {prof} stratum {st}: {len(v)} configs, example {v[0]}")

report("n=16", n16)
report("n=32", n32)

# cross-scale pattern identity check (E1)
p16 = set(n16[1].keys()); p32 = set(n32[1].keys())
print("\npatterns @16:", len(p16), " @32:", len(p32), " identical:", p16==p32)
print("DONE")
