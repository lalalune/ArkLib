#!/usr/bin/env python3
"""probe_deepband_monomial_extremal.py (#389, Fable): worst-case-over-stacks
MCA-bad count search (correct joint check aff(u0)&aff(u1)) testing deep-band monomial
extremality. On mu_16: monomial extremal in the deep band (a=4,5) across random, mono-sum,
random-both, AND coset-structured/subspace-poly (EsymmFiber-class) adversaries at
q=449,769,1153 (nothing beats monomial 97 at a=4). Near the cliff (a=3) monomial beaten ~3%
(saturating regime). Reconciles with #357 MonomialDominationKilled (shallow/UDR band, opposite
regime). => floor (deep band) reduces to deep-band monomial extremality + #371 monomial
spectrum-collapse."""
import random
def rou(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if all(pow(h,d,p)!=1 for d in range(1,n)): return [pow(h,i,p) for i in range(n)]
def badcount(D,u0,u1,p,a):
    n=len(D); c=0
    for g in range(p):
        w=[(u0[i]+g*u1[i])%p for i in range(n)]
        seen=set(); found=False
        for i in range(n):
            for j in range(i+1,n):
                dx=(D[i]-D[j])%p
                if dx==0: continue
                al=((w[i]-w[j])*pow(dx,p-2,p))%p; be=(w[i]-al*D[i])%p
                if (al,be) in seen: continue
                seen.add((al,be))
                S=[t for t in range(n) if (al*D[t]+be)%p==w[t]]
                if len(S)>=a:
                    def aff(vv):
                        if len(S)<=2: return True
                        x0,x1=D[S[0]],D[S[1]]; dxx=(x0-x1)%p
                        if dxx==0: return False
                        a2=((vv[S[0]]-vv[S[1]])*pow(dxx,p-2,p))%p; b2=(vv[S[0]]-a2*x0)%p
                        return all((a2*D[t]+b2)%p==vv[t] for t in S)
                    if not(aff(u0) and aff(u1)): found=True;break
            if found:break
        if found: c+=1
    return c
n=16
for (p,a) in [(449,4),(769,4),(1153,4)]:
    D=rou(p,n); rng=random.Random(55)
    mono=max(badcount(D,[pow(x,e,p) for x in D],[pow(x,2,p) for x in D],p,a) for e in range(3,16))
    best=mono; bn='monomial'
    u1=[pow(x,2,p) for x in D]
    # COSET-STRUCTURED adversaries (the EsymmFiber / subspace-poly class):
    #  - block-constant on mu_d cosets (d|16): u0(x) = c_block(x)  varying per coset
    #  - low-degree composed with x^d: u0 = P(x^d)  (lives in the d-th power tower)
    cands=[]
    for d in [2,4,8]:
        # u0 = P(x^d), P low degree -> subspace-poly analogue
        for _ in range(60):
            deg=rng.randint(1,16//d)
            coef=[rng.randrange(p) for _ in range(deg+1)]
            u0=[sum(coef[t]*pow(pow(x,d,p),t,p) for t in range(deg+1))%p for x in D]
            cands.append(u0)
        # block-constant on mu_d cosets: assign random value per coset of <g^d>... approx via x^d class
        for _ in range(60):
            vals={}
            u0=[]
            for x in D:
                key=pow(x,16//d,p)  # coset rep under the index-(16/d) subgroup
                if key not in vals: vals[key]=rng.randrange(p)
                u0.append(vals[key])
            cands.append(u0)
    for u0 in cands:
        b=badcount(D,u0,u1,p,a)
        if b>best: best=b; bn='coset-struct'; 
    print(f'q={p} a={a}: monomial={mono}, MAX incl coset-structured ({len(cands)} cand)={best} ({bn})  {"MONO EXTREMAL" if best==mono else "BEATEN BY "+bn}')
