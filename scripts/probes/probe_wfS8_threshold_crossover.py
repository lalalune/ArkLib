#!/usr/bin/env python3
# wf-S8 threshold crossover: for each norm bound on Nmax(n,w), find the largest n=2^mu for which
# the prize prime p = n^beta still exceeds Nmax at the optimal moment depth r* (w*=2r*), hence
# the char-0 -> F_p transfer is spurious-FREE and the prize is PROVEN unconditionally.
#
# No-spurious condition at depth w:  p > Nmax(n,w).   Prize prime: p = n^beta = 2^{mu*beta}.
# Optimal depth for the moment->maxbound conversion: r* ~ ln(p)/2 = (beta*mu*ln2)/2, w*=2r*=beta*mu*ln2.
# But we only NEED the no-spurious window to cover the depth actually used. We report the threshold
# n-bound for several depth conventions and the three Nmax models:
#   crude house:  Nmax = w^{n/2}                  -> log = (n/2) ln w
#   L2 (Parseval AM-GM, in-tree):  Nmax = (2w)^{n/4}  -> log = (n/4) ln(2w)
#   SHARP (measured this lane): base = sqrt(w):  Nmax = w^{n/4}  -> log = (n/4) ln w
# Transfer iff beta*mu*ln2 > log Nmax(n=2^mu, w*).

import math

LN2 = math.log(2)

def logNmax(model, n, w):
    half = n/2
    if model=="crude": return half*math.log(w)
    if model=="L2":    return (n/4)*math.log(2*w)
    if model=="sharp": return (n/4)*math.log(w)
    raise ValueError

def threshold_n(model, beta, depth_law):
    """largest n=2^mu with p=n^beta > Nmax(n, w*(mu)). depth_law in {'rstar','fixed4','fixed6'}."""
    best_mu = 0
    for mu in range(2, 200):
        n = 2**mu
        logp = beta*mu*LN2
        if depth_law=='rstar':
            w = max(2, beta*mu*LN2)   # w*=2r*=ln p
        elif depth_law=='fixed4':
            w = 4
        elif depth_law=='fixed6':
            w = 6
        lN = logNmax(model, n, w)
        if logp > lN:
            best_mu = mu
        else:
            # not necessarily monotone for fixed w (n grows faster), but for our laws it crosses once
            pass
    return best_mu

if __name__=="__main__":
    print("# wf-S8 unconditional-prize threshold N0 = largest n=2^mu with spurious-free transfer\n")
    for beta in [4, 8, 30]:
        print(f"### beta = {beta} (p = n^{beta})")
        for depth_law, desc in [('rstar','optimal depth w*=ln p (the prize moment depth)'),
                                 ('fixed4','depth r=2 / w=4 (shallow)'),
                                 ('fixed6','depth r=3 / w=6')]:
            print(f"  depth = {desc}")
            for model in ["crude","L2","sharp"]:
                mu = threshold_n(model, beta, depth_law)
                print(f"    {model:6s}: largest mu={mu:3d}  => n=2^{mu} = {2**mu if mu<60 else '2^'+str(mu)}")
        print()
    # Direct crossover at prize regime: how many BITS of prime does each model need vs available beta*log2(n)?
    print("# At a FIXED n, what beta (prime size n^beta) makes transfer spurious-free at depth w*=ln p?")
    print("# (self-consistent: need beta*mu*ln2 > logNmax(n, w*=beta*mu*ln2))")
    for mu in [5,6,7,8,10,12,16,20,30]:
        n=2**mu
        # solve smallest beta s.t. condition holds, for each model
        line=f"  mu={mu:2d} n={n if mu<40 else '2^'+str(mu):>8}: "
        for model in ["crude","L2","sharp"]:
            found=None
            b=0.1
            while b<10000:
                logp=b*mu*LN2; w=max(2,logp)
                if logp>logNmax(model,n,w): found=b; break
                b*=1.05
            line+=f"{model}_beta>={found:.1f} " if found else f"{model}=NEVER "
        print(line)
