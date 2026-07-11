#!/usr/bin/env python3
# PROBE: the deficit-twist TELESCOPE up the dyadic tower.
# eta_split_parallelogram: |eta_{2k}(b)|^2 = 2(|eta_k(b)|^2+|eta_k(wb)|^2) - twist_k(b),
#   twist_k(b) = |eta_k(b)-eta_k(wb)|^2.
# QUESTION (never formalized): track V_mu = max_b |eta_{2^mu}(b)|^2 up the tower and the
#   per-level deficit D_mu = 4*V_{mu-1} - V_mu (>=0 by tower ceiling). Does sum of D_mu
#   account for the gap between trivial 4^mu = n^2 and the actual M^2 ~ C n log(q/n)?
#   I.e. is M(n)^2 = n^2 - (telescoped deficit)? And is the deficit ~ n^2 - C n log(q/n)?
# THINNESS: proper 2-power mu_n in F_q^*, n=2^a, n|q-1, prize q>>n. NEVER n=q-1.
import cmath, math
def primfind(n, lo):
    q=max(n+1,lo)
    while True:
        if all(q%p for p in range(2,int(q**.5)+1)) and (q-1)%n==0:
            for g in range(2,q):
                if all(pow(g,d,q)!=1 for d in range(1,q-1)) and pow(g,q-1,q)==1:
                    return q,g
        q+=1
def maxeta_sq(G,p):
    best=0.0
    for b in range(1,p):
        v=abs(sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in G))**2
        if v>best:best=v
    return best
print("tower from bottom; per-level deficit D_mu=4 V_{mu-1}-V_mu, M^2=V_top, n^2 trivial",flush=True)
print(f"{'a':>2} {'n':>5} {'V_mu':>9} {'4V_prev':>9} {'D_mu':>9} {'n^2':>8} {'M^2/(n log(q/n))':>16}",flush=True)
for abig in [4,5,6,7]:
    n=2**abig
    p,g=primfind(n,5000)          # q>>n prize-ish; q grows with n
    # full 2-power tower subgroups mu_{2^a} for a=1..abig, all inside F_q^*
    Vprev=None
    for a in range(1,abig+1):
        na=2**a
        z=pow(g,(p-1)//na,p)
        G=[pow(z,i,p) for i in range(na)]
        V=maxeta_sq(G,p)
        if a==abig:
            D = 4*Vprev - V if Vprev is not None else float('nan')
            logfac = na*math.log(p/na)
            print(f"{a:>2} {na:>5} {V:>9.2f} {4*Vprev:>9.2f} {D:>9.2f} {na*na:>8} {V/logfac:>16.3f}",flush=True)
        Vprev=V
print("\nREADING: if M^2/(n log(q/n)) ~ O(1) const across n => prize shape holds in data.",flush=True)
print("D_mu = the top-level deficit (4 V_{mu-1} - V_mu); if D_mu ~ 4 V_{mu-1} - C n log(q/n)",flush=True)
print("the deficit is LARGE (most of the trivial bound is killed). PROBE ONLY.",flush=True)
