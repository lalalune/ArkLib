#!/usr/bin/env python3
"""EXACT line-list-size and bad-count measurement across [halfJ, J) for mu_16 RS, k=2.

This is the decisive instance: n=16, k=2, rho=1/8 (prize rate). The half-Johnson
cap is vacuous on t in {10,9,8,7,6} (delta in [0.375, 0.625]) but we are still
BELOW full Johnson (t=5 onward). We measure EXACTLY (full codeword enumeration,
p^2 codewords) the worst line-list size L and bad-count over mu_n stacks, to decide
whether the obstruction past half-Johnson is (B) the list bound or (A) support.

We use mu_n second rows (guaranteeing full support, the 'rows in mu_n' regime),
and exact mca-event (no proxy): a scalar g is bad iff the line u0+g*u1 is delta-close
to the code (some codeword agrees on >= t coords) while the STACK is delta-far
(no single codeword agrees with both u0 and u1 each on a >= t coordinate set).
"""
import itertools, math, random

def is_prime(p):
    if p<2: return False
    for d in range(2,int(p**0.5)+1):
        if p%d==0: return False
    return True

def find_prime(n, lo):
    p=lo+1
    while True:
        if is_prime(p) and (p-1)%n==0: return p
        p+=1

def find_gen(p):
    phi=p-1; m=phi; facs=set(); d=2
    while d*d<=m:
        while m%d==0: facs.add(d); m//=d
        d+=1
    if m>1: facs.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs): return g

def main(n=16, k=2, p=None, trials=12, seed=0):
    if p is None: p=find_prime(n, 16)
    g=find_gen(p); w=pow(g,(p-1)//n,p)
    mu=[pow(w,i,p) for i in range(n)]
    assert 0 not in mu and len(set(mu))==n
    rho=k/n; J=1-math.sqrt(rho); halfJ=J/2
    print(f"n={n} k={k} p={p} rho={rho:.4f} halfJ={halfJ:.4f} J={J:.4f}  |mu|={len(mu)}")
    # enumerate all RS codewords (deg<k)
    cws=set()
    for c in itertools.product(range(p),repeat=k):
        cws.add(tuple(sum(c[j]*pow(x,j,p) for j in range(k))%p for x in mu))
    cws=list(cws)
    print(f"  #codewords={len(cws)}")
    muset=set(mu)
    random.seed(seed)
    def agree(cw,line): return sum(1 for a,b in zip(cw,line) if a==b)
    def line_list(u0,u1,t):
        S=set()
        for gg in range(p):
            line=tuple((a+gg*b)%p for a,b in zip(u0,u1))
            for ci,cw in enumerate(cws):
                if agree(cw,line)>=t: S.add(ci)
        return len(S)
    def stack_far(u0,u1,t):
        # stack is t-CLOSE iff some cw agrees with u0 on >=t AND with u1 on >=t (joint).
        # mcaEvent fires for g iff line close but stack far (we test per-g below).
        pass
    def joint_close(u0,u1,t):
        # does some single codeword agree with BOTH u0 and u1 on a >= t coordinate set?
        # i.e. exists cw, S with |S|>=t, cw=u0 on S and cw=u1 on S? That forces u0=u1 on S.
        # The MCA 'good' condition: u0 and u1 are jointly t-close to the SAME codeword on SAME S.
        # Standard: exists cw0,cw1 (codewords) and S, |S|>=t, u0=cw0 on S, u1=cw1 on S.
        # We use the proximity-gap MCA: stack far means NOT all line points share a witness.
        # For the bad-count we use the established proxy from the f5 probe: bad g = line ext
        # at t while NOT (u0 ext at S and u1 ext at S jointly). Match probe_transversal exactly:
        return None
    # Replicate the exact mcaEvent proxy used in probe_transversal_kit_f5 (subset based).
    subsets_by_size={}
    # too many subsets for n=16; instead use agreement-count form which is equivalent for
    # "exists S size>=t with cw=line on S" == "agree(cw,line)>=t". Joint version:
    def ext_word(word,t):
        return any(agree(cw,word)>=t for cw in cws)
    def ext_joint(u0,u1,t):
        # exists cw with cw=u0 and cw=u1 on a common size>=t set -> needs u0=u1 there; rare.
        # Proper joint: exists S size>=t, ext(u0,S) and ext(u1,S) meaning some cw0=u0|S, cw1=u1|S.
        # Approx via: there is a size-t coordinate set on which BOTH rows are individually
        # explained. We compute the max set where u0 is row-close and u1 is row-close using
        # per-coordinate "explainable" — but RS explainability is global. Use exact:
        # build, per codeword, the agreement set with u0 and with u1; joint over S means
        # |agreeset(cw0,u0) ∩ agreeset(cw1,u1)| >= t for some cw0,cw1.
        best=0
        ag0=[set(i for i in range(n) if cw[i]==u0[i]) for cw in cws]
        ag1=[set(i for i in range(n) if cw[i]==u1[i]) for cw in cws]
        for s0 in ag0:
            for s1 in ag1:
                if len(s0&s1)>=t: return True
        return False
    def bad_count(u0,u1,t):
        cnt=0
        for gg in range(p):
            line=tuple((a+gg*b)%p for a,b in zip(u0,u1))
            if ext_word(line,t) and not ext_joint(u0,u1,t):
                cnt+=1
        return cnt
    print(f"  {'t':>3} {'delta':>6} {'L_act':>6} {'bad':>4} {'a^2-ne':>7} {'supp':>5} region (q-budget: bad<q*2^-128 ~ 0)")
    for t in range(n,0,-1):
        d=1-t/n
        a=2*t-n; e=k-1; den=a*a-n*e
        reg='<halfJ' if d<halfJ-1e-9 else ('[halfJ,J)' if d<J-1e-9 else '>=J')
        maxL=0; maxbad=0; supp=True
        for _ in range(trials):
            u0=tuple(random.randrange(p) for _ in range(n))
            u1=tuple(random.choice(mu) for _ in range(n))  # in mu_n => full support
            if any(v==0 for v in u1): supp=False
            maxL=max(maxL,line_list(u0,u1,t))
            maxbad=max(maxbad,bad_count(u0,u1,t))
        # also the deep-band monomial stack
        u0=tuple(random.randrange(p) for _ in range(n)); u1=tuple(pow(x,k,p) for x in mu)
        maxL=max(maxL,line_list(u0,u1,t)); maxbad=max(maxbad,bad_count(u0,u1,t))
        print(f"  {t:>3} {d:>6.3f} {maxL:>6} {maxbad:>4} {den:>7} {str(supp):>5} {reg}")

if __name__=="__main__":
    main(16,2,trials=10)
