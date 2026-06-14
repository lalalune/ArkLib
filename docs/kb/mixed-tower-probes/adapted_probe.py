import itertools, cmath
n=12
roots=[cmath.exp(2j*cmath.pi*k/n) for k in range(n)]
P2=[frozenset([k,(k+6)%12]) for k in range(6)]
P3=[frozenset([k,(k+4)%12,(k+8)%12]) for k in range(4)]
def all_decomps(s, acc, out, limit=200):
    if len(out)>=limit: return
    if not s: out.append(acc); return
    k=min(s)
    for P in P2+P3:
        if k in P and P<=s:
            all_decomps(s-P, acc+[P], out, limit)
def win(S,t):
    return all(abs(sum(roots[k]**j for k in S))<1e-9 for j in range(1,t+1))
def spec_window_ok(D, t, q=2):
    # spectrum R from q-packets (squares), T from 3-packets (cubes)
    R=[roots[min(P)]**2 for P in D if len(P)==2]
    ok=True
    for e in range(1, t//2+1):
        if abs(sum(x**e for x in R))>1e-9: ok=False
    return ok
bad_elements=0; total_elements=0
for r in range(2,13):
    for E in itertools.combinations(range(12),r):
        Es=frozenset(E)
        for t in (4,6):
            if not win(Es,t): continue
            # for each x with full 2-orbit in S: peel it, check completions
            for x in sorted(Es):
                orb=frozenset([x,(x+6)%12])
                if not orb<=Es: continue
                total_elements+=1
                rest=Es-orb
                outs=[]; all_decomps(rest,[],outs)
                # completions: decomposition of rest + the peeled packet
                best=any(spec_window_ok(D+[orb], t) for D in outs)
                if not best:
                    bad_elements+=1
                    if bad_elements<=5:
                        print(f"NO-GOOD-COMPLETION: S={sorted(Es)} t={t} x={x} (#completions={len(outs)})")
print(f"peeled-element cases: {total_elements}, no-good-completion: {bad_elements}")
