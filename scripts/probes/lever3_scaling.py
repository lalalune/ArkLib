import math
from collections import deque

# For FIXED n=2^mu, how does min-l1-weight of a vanishing relation grow with p?
# This is the real prize question: at n=128 (d=64), p~2^128, what is the
# minimum number of signed n-th-roots-of-unity that sum to 0 mod p?
#
# THEORY (this is the crux): a weight-w relation sum_{i} eps_i g^{a_i} == 0 mod p
# with a_i in {0..d-1}, eps_i = +-1. There are ~ (2d)^w such signed words.
# Each lands on a "random" residue in Z/p. A vanishing one (residue 0) appears
# when (2d)^w >~ p, i.e. w >~ log p / log(2d) = log p / log n  (since 2d = n).
# So the PROBABILISTIC min-l1 weight = log p / log n  =  log_n p.
#
# At prize scale: log_n p = log(2^128)/log(128) = 128 ln2 / (7 ln2) = 128/7 ~ 18.3.
# NEEDED depth budget 2r ~ 2 ln q ~ 2*128*ln2 ~ 177.
# So min-l1-weight ~ 18 << budget 177  ==>  Q4 != 0 at prize scale (witnesses EXIST).
#
# This is the HEIGHT-GATE FAILURE: at n=128 the wrap-around DOES turn on at the
# needed depth, because log_n p ~ 18 < 2 ln q ~ 177.  The geometry does NOT cover.
#
# CONTRAST with in-tree optimistic claim p^{1/d}: that is the WRONG model.
#   p^{1/d} = exp(ln p / d). With d=64, ln p = 128 ln2 = 88.7, ln p/d = 1.38,
#   so p^{1/d} = 4.0 = 2^{2/d * 128/2}... this measures the GEOMETRIC-MEAN
#   coordinate, NOT the l1 girth. The l1 girth is log_n p (a COUNTING bound),
#   which is what the small-case ground truth (min_l1=3 at p~200, n=64:
#   log_64(200) = 1.27 ... hmm small. Let me recompute and CHECK.

def primitive_nth_root_mod_p(n, p):
    for g in range(2, p):
        if pow(g, n, p) == 1 and pow(g, n//2, p) != 1:
            return g
    return None

def is_prime(p):
    if p<2: return False
    return all(p%q for q in range(2,int(p**0.5)+1))

def min_l1_weight(d, p, g):
    gp = [pow(g, k, p) for k in range(d)]
    sset = list({s for k in range(d) for s in (gp[k], (-gp[k])%p)})
    INF=10**9
    dist=[INF]*p; parent=[-1]*p; pgen=[-1]*p
    dist[0]=0; dq=deque([0]); girth=INF
    while dq:
        u=dq.popleft()
        if dist[u]*2+1>=girth: continue
        for s in sset:
            v=(u+s)%p
            if dist[v]==INF:
                dist[v]=dist[u]+1; parent[v]=u; pgen[v]=s; dq.append(v)
            elif not (v==parent[u] and s==(-pgen[u])%p):
                girth=min(girth,dist[u]+dist[v]+1)
    return girth

print("Test the COUNTING model min_l1 ~ log_n(p) = ln p / ln n:")
print(f"{'n':>4} {'d':>3} {'p':>9} {'min_l1':>7} {'log_n(p)':>9} {'p^(1/d)':>9}")
import random
for mu in [3,4,5,6]:
    n=2**mu; d=n//2
    tested=0; p=n*200
    while tested<4 and p < 3_000_000:
        if is_prime(p) and p%n==1:
            g=primitive_nth_root_mod_p(n,p)
            if g and p < 600000:   # BFS feasibility
                w=min_l1_weight(d,p,g)
                logn_p = math.log(p)/math.log(n)
                p13 = p**(1.0/d)
                print(f"{n:>4} {d:>3} {p:>9} {w:>7} {logn_p:>9.3f} {p13:>9.3f}")
                tested+=1
        p+=1
print()
print("Prize-scale projection (n=128, p=2^128) of the COUNTING girth:")
for mu in [7,8,10,20,30]:
    n=2**mu; d=n//2
    lnp = (n.bit_length()-1 + 128)*math.log(2) if False else (math.log(n)+128*math.log(2))
    logn_p = lnp/math.log(n)
    budget = 2*lnp   # 2r, r~ln q
    print(f" n={n:>10} d={d:>9}  min_l1~log_n(p)={logn_p:7.2f}  2r_budget={budget:7.1f}  "
          f"=> Q4 {'OFF (girth>budget)' if logn_p>budget else 'ON (girth<budget): WITNESSES EXIST'}")
