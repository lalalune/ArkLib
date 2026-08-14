#!/usr/bin/env python3
"""Spurious-only worst-s scan: among stacks whose bad-count EXCEEDS the trivial O(n) baseline,
what is the worst-case orbit subgroup s=n/gcd(b-a,n) as delta -> threshold? Re-tests the
small-subgroup synthesis after subtracting the trivial single-full-orbit baseline."""
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

def scan(n, rho_num, rho_den, beta):
    q = find_q(n,beta); elts = subgroup(n,q); k = max(1,(n*rho_num)//rho_den)
    print(f"\n--- n={n} q={q} rho={rho_num}/{rho_den} k={k}  baseline=n={n} ---", flush=True)
    XS = [[pow(x,a,q) for a in range(n)] for x in elts]
    tau_j = int(math.sqrt(rho_num/rho_den)*n)
    for tau in range(k+1, min(tau_j+2, n)):
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
        allr = [(len(st), a, b, n//math.gcd(b-a,n)) for (a,b),st in bad.items()]
        spur = [t for t in allr if t[0] > n]
        if not allr:
            print(f"  tau={tau} d={1-tau/n:.3f}: none", flush=True); continue
        allr.sort(reverse=True); gmax = allr[0][0]; gs = allr[0][3]
        if spur:
            spur.sort(reverse=True); smax = spur[0][0]
            sws = min(t[3] for t in spur if t[0] == smax)
            allsp = sorted(set(t[3] for t in spur))
            print(f"  tau={tau} d={1-tau/n:.3f}: SPURIOUS(>n) max={smax} worst-s={sws}  s-values-present={allsp}  | global max={gmax}", flush=True)
        else:
            print(f"  tau={tau} d={1-tau/n:.3f}: NO spurious (all <= baseline {n}); global max={gmax} s={gs}  <-- trivial regime (delta<=delta*)", flush=True)

scan(16,1,4,3)
scan(16,1,2,3)
