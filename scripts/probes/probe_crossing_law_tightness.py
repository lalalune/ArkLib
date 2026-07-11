#!/usr/bin/env python3
"""Test the crossing law:  delta* = radius where worst spurious subgroup s* has s*^(s*/2) ~ q.
For fixed n, vary q (via beta); report worst spurious-s at the threshold edge (largest tau with
any count>n).  Prediction: s* grows with q as s*^(s*/2) ~ q  (=> s* ~ 2 log q / log log q)."""
import itertools, math

def is_prime(m):
    if m < 2: return False
    i = 2
    while i*i <= m:
        if m % i == 0: return False
        i += 1
    return True
def find_q(n, beta):
    base = n**beta; m = base + ((1-base) % n)
    while not ((m-1) % n == 0 and is_prime(m)): m += n
    return m
def egcd(a,b):
    if b == 0: return (a,1,0)
    g,x,y = egcd(b, a % b); return (g, y, x-(a//b)*y)
def inv(a,q):
    a %= q; g,x,_ = egcd(a,q); return x % q
def subgroup(n,q):
    for cand in range(2,q):
        h = pow(cand,(q-1)//n,q)
        if pow(h,n,q) != 1: continue
        if n > 1 and pow(h,n//2,q) == 1: continue
        return [pow(h,i,q) for i in range(n)]
def matinv(M,q):
    t = len(M); A = [row[:]+[1 if i==j else 0 for j in range(t)] for i,row in enumerate(M)]
    for c in range(t):
        piv = next((r for r in range(c,t) if A[r][c] % q), None)
        if piv is None: return None
        A[c],A[piv] = A[piv],A[c]; ip = inv(A[c][c],q); A[c] = [(x*ip) % q for x in A[c]]
        for r in range(t):
            if r != c and A[r][c] % q:
                f = A[r][c]; A[r] = [(A[r][j]-f*A[c][j]) % q for j in range(2*t)]
    return [row[t:] for row in A]

def threshold_worst_s(n, rho_num, rho_den, beta):
    q = find_q(n,beta); elts = subgroup(n,q); k = max(1,(n*rho_num)//rho_den)
    XS = [[pow(x,a,q) for a in range(n)] for x in elts]
    tau_j = int(math.sqrt(rho_num/rho_den)*n)
    edge = None  # (tau, worst_s, s_values, maxcount)
    for tau in range(k+1, n):
        bad = {}
        for Sidx in itertools.combinations(range(n), tau):
            S = [elts[i] for i in Sidx]
            V = [[pow(x,j,q) for j in range(tau)] for x in S]; Vi = matinv(V,q)
            if Vi is None: continue
            W = Vi[k:tau]
            M = [[sum(W[r][i]*XS[Sidx[i]][a] for i in range(tau)) % q for a in range(n)] for r in range(tau-k)]
            for a in range(n):
                for b in range(a+1,n):
                    al = None; ok = True
                    for r in range(tau-k):
                        pj = M[r][a]; qj = M[r][b]
                        if qj % q == 0:
                            if pj % q: ok = False; break
                        else:
                            v = (-pj*inv(qj,q)) % q
                            if al is None: al = v
                            elif al != v: ok = False; break
                    if ok and al is not None and al % q != 0:
                        bad.setdefault((a,b), set()).add(al)
        spur = [(len(st), n//math.gcd(b-a,n)) for (a,b),st in bad.items() if len(st) > n]
        if spur:
            smax = max(c for c,_ in spur)
            ws = min(s for c,s in spur if c == smax)
            svals = sorted(set(s for _,s in spur))
            edge = (tau, ws, svals, smax)  # keep updating; last spurious tau = threshold edge
    return q, k, edge

for n in (8,16):
    print(f"\n=== n={n}: worst spurious-s at threshold edge vs q ===", flush=True)
    print(f"{'rho':>5} {'beta':>4} {'q':>8} {'s*':>4} {'s*^(s*/2)':>10} {'q/s*^(s*/2)':>11} {'s-vals@edge':>14}", flush=True)
    for (rn,rd) in [(1,4),(1,2)]:
        for beta in (3,4,5,6):
            q,k,edge = threshold_worst_s(n,rn,rd,beta)
            if edge is None:
                print(f"{rn}/{rd:>3} {beta:>4} {q:>8}   (no spurious at any radius)", flush=True); continue
            tau,ws,svals,smax = edge
            bound = ws**(ws//2)
            print(f"{rn}/{rd:>3} {beta:>4} {q:>8} {ws:>4} {bound:>10} {q/bound:>11.2f} {str(svals):>14}", flush=True)
