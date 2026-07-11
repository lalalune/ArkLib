#!/usr/bin/env python3
"""
PROVABLE component of the prize soundness count, via multilinear Schwartz-Zippel.
Claim: the full mu-round dyadic fold of any word e on D (|D|=N=2^mu) to its single final value is a
MULTILINEAR polynomial Fold^mu(e,lambda_1..lambda_mu) in the challenges (degree 1 per variable). The map
e |-> Fold^mu(e,.) is a linear bijection from F^N to multilinear polys (the per-position weight functions
W(x,.) form a basis). Hence for e != 0 the poly is NONZERO, total degree mu, so by Schwartz-Zippel
  #{lambda : Fold^mu(e,lambda)=0} <= mu * q^{mu-1},  i.e. bad-fraction <= mu/q = log2(N)/|F|.
This bounds, UNCONDITIONALLY, the per-codeword 'f_0 folds exactly to c_0 image' commit event by log2(N)/|F|.

We verify: (1) injectivity/basis (Fold^mu(e,.)=0 forall lambda <=> e=0); (2) the bad-fraction <= mu/q,
exactly, for random far e, by exhaustively evaluating over all lambda in F^mu.
"""
import itertools,random,functools,math
print=functools.partial(print,flush=True)
def run(q,N,checks=200,seed=2):
    inv=[0]*q
    for a in range(1,q): inv[a]=pow(a,q-2,q)
    mu=N.bit_length()-1
    om=next((g for g in range(2,q) if pow(g,N,q)==1 and pow(g,N//2,q)!=1),None)
    if om is None or pow(om,N//2,q)!=q-1: print(f"skip q={q} N={N}");return
    Ds=[[pow(om,i,q) for i in range(N)]]
    while len(Ds[-1])>1: Ds.append(sorted(set(pow(x,2,q) for x in Ds[-1])))
    inv2=inv[2]
    foldmap=[]
    for L in range(mu):
        prev,nxt=Ds[L],Ds[L+1];pos={v:i for i,v in enumerate(nxt)};seen=set();fm=[]
        for x in prev:
            y=pow(x,2,q)
            if y not in seen: seen.add(y);fm.append((pos[y],prev.index(x),prev.index((q-x)%q),x))
        foldmap.append((prev,nxt,fm))
    def fold1(vec,L,lam):
        prev,nxt,fm=foldmap[L];g=[0]*len(nxt)
        for (yi,xi,nxi,x) in fm:
            a=((vec[xi]+vec[nxi])*inv2)%q;b=((vec[xi]-vec[nxi])*inv[(2*x)%q])%q;g[yi]=(a+lam*b)%q
        return g
    def foldmu(vec,lams):
        v=vec
        for L in range(mu): v=fold1(v,L,lams[L])
        return v[0]
    random.seed(seed)
    # (1) injectivity check: a few random nonzero e must have foldmu nonzero for SOME lambda
    inj_ok=True
    for _ in range(30):
        e=[random.randrange(0,q) for _ in range(N)]
        if all(x==0 for x in e): continue
        # evaluate over all lambda in F^mu; if always 0 -> injectivity fails
        allzero=all(foldmu(e,lams)==0 for lams in itertools.product(range(q),repeat=mu))
        if allzero: inj_ok=False;break
    # (2) bad-fraction <= mu/q, exact over all lambda in F^mu
    worst_frac=0.0; total=q**mu
    for _ in range(checks):
        e=[random.randrange(0,q) for _ in range(N)]
        if all(x==0 for x in e): continue
        bad=sum(1 for lams in itertools.product(range(q),repeat=mu) if foldmu(e,lams)==0)
        fr=bad/total
        if fr>worst_frac: worst_frac=fr
    bound=mu/q
    print(f" q={q} N={N} mu={mu}: injective(basis)={inj_ok} | worst bad-fraction={worst_frac:.4f} "
          f"<= mu/q={bound:.4f} ? {'YES' if worst_frac<=bound+1e-9 else 'NO!!'}")
print("Multilinear Schwartz-Zippel fold bound: bad-fraction <= log2(N)/|F|, UNCONDITIONAL:")
run(17,8); run(41,8); run(17,16); run(97,8)
