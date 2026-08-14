# THE CLIFF TEST: is L(a) = Theta(n^k) only at a=k+1, dropping to O(n) for a>=k+2 on mu_n at q>>n?
# k=2 (lines). For each n, large prime p (n | p-1, p ~ 10^7 so n << p). Measure L(a) = #a-rich lines
# for a = 3,4,5 across structured words + a fast hill-climb. Cliff => L(3) ~ n^2/6, L(4),L(5) ~ O(n).
import sys
from collections import Counter

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def find_prime(n, lo):
    # smallest prime p > lo with n | p-1
    p = lo - (lo % n) + 1
    while p <= lo or not is_prime(p):
        p += n
    return p

def subgroup(n, p):
    # find element of order n
    for g0 in range(2, p):
        g = pow(g0, (p-1)//n, p)
        if g != 1 and pow(g, n, p) == 1:
            # verify exact order
            ok = all(pow(g, n//d, p) != 1 for d in range(2, n+1) if n % d == 0)
            if ok:
                D = []
                x = 1
                for _ in range(n):
                    D.append(x); x = x*g % p
                if len(set(D)) == n:
                    return D
    raise RuntimeError("no subgroup")

def spectrum(w, D, p):
    # pair-hash lines; return Counter {agreement: #lines}
    inv = {}
    n = len(D)
    pc = Counter()
    for i in range(n):
        xi, wi = D[i], w[i]
        for j in range(i+1, n):
            xj, wj = D[j], w[j]
            # line through (xi,wi),(xj,wj): slope s=(wj-wi)/(xj-xi), intercept b=wi-s*xi
            s = (wj - wi) * pow(xj - xi, p-2, p) % p
            b = (wi - s*xi) % p
            pc[(s,b)] += 1
    spec = Counter()
    for cnt in pc.values():
        # cnt = C(t,2) => t = (1+sqrt(1+8cnt))/2
        t = (1 + int((1+8*cnt)**0.5 + 0.5)) // 2
        # robust: find t with t(t-1)/2 = cnt
        tt = 2
        while tt*(tt-1)//2 < cnt: tt += 1
        spec[tt] += 1
    return spec

def L(spec, a):
    return sum(c for t,c in spec.items() if t >= a)

def nodal_word(D, p, gamma):
    return [(x*x + gamma*pow(x,p-2,p)) % p for x in D]

def monomial(D, p, t):
    return [pow(x, t, p) for x in D]

def main():
    results = {}
    for n in [16, 24, 32, 48]:
        p = find_prime(n, 10_000_000)
        D = subgroup(n, p)
        invD = [pow(x,p-2,p) for x in D]
        # structured candidates, max L(a) over them
        best = {3:(0,None), 4:(0,None), 5:(0,None)}
        cands = []
        # nodal cubics over all gamma in D (and -D)
        for g in D:
            cands.append(('nodal+%d'%g, nodal_word(D,p,g)))
            cands.append(('nodal-%d'%g, nodal_word(D,p,(-g)%p)))
        # monomials
        for t in range(3, 9):
            cands.append(('x^%d'%t, monomial(D,p,t)))
        # nodal quartic x^3+g/x
        for g in D[:8]:
            cands.append(('q3+%d'%g, [(pow(x,3,p)+g*pow(x,p-2,p))%p for x in D]))
        for name, w in cands:
            spec = spectrum(w, D, p)
            for a in (3,4,5):
                la = L(spec, a)
                if la > best[a][0]:
                    best[a] = (la, name)
        results[n] = {a: best[a] for a in (3,4,5)}
        print(f"n={n} p={p}: L3={best[3][0]} ({best[3][1]}) [n^2/6={n*(n-1)//6}, /n={best[3][0]/n:.2f}]  "
              f"L4={best[4][0]} ({best[4][1]}) [/n={best[4][0]/n:.2f}]  "
              f"L5={best[5][0]} ({best[5][1]}) [/n={best[5][0]/n:.2f}]")
    # verdict
    print("\nCLIFF VERDICT (L(a)/n should be ~n/6 for a=3, ~const for a>=4 if cliff holds):")
    for n in results:
        r = results[n]
        print(f"  n={n}: L3/n={r[3][0]/n:.1f} (grows~n/6={n/6:.1f}?)  L4/n={r[4][0]/n:.2f}  L5/n={r[5][0]/n:.2f}")

main()
