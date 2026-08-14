#!/usr/bin/env python3
"""
Door-IV Lane 1 PROBE — is the worst-b (argmax|S|) multiplicatively SUBFIELD/NORM-structured?

Deconfliction: prior worst-b structure probes tested the coset-INDEX arithmetic (a2ad4130b: v2-val,
AP, mod-d residue of the quotient index — UNSTRUCTURED) and the worst-b VALUE quotient (1e22ed805)
and the worst-b INTERNAL complex geometry (78d1df596). NONE tested whether the worst-b VALUE itself
lies in a proper MULTIPLICATIVE SUBSTRUCTURE of F_p* — specifically a power-coset b in (F_p*)^d for
small d (the natural "norm/subfield-like" thin set). If the worst-b were forced into such a thin
multiplicative set, an anti-concentration bound could restrict the search; if it is multiplicatively
GENERIC (its discrete-log mod small d is flat), that class-restriction lever is dead.

Object: at b* = argmax_b |S(b)|, S(b)=sum_{x in mu_n} e_p(b x), record the discrete log L = log_g0(b*)
and test, over many structured primes, whether L mod d is biased for small d in {2,3,4,5,8} (i.e. is b*
disproportionately a d-th power / in a fixed power-coset). A bias would mean worst-b sits in a thin
multiplicative subset (exploitable). Flatness => generic => lever dead.

NB: |S| is constant on mu_n-cosets b*mu_n. The mu_n-coset of b is {b g^j}, whose discrete logs are
L + j*((p-1)/n) for j=0..n-1, i.e. L is only well-defined MOD (p-1)/n = m (the coset index). So the
honest invariant is the COSET INDEX I = L mod m... which is exactly what a2ad4130b tested at the index
level. The NEW content here: test L mod d for d | gcd considerations vs m, AND test the genuinely
coset-INVARIANT multiplicative invariant: whether b* is a d-th POWER in F_p* is well-defined on the
mu_n-coset ONLY when d | (p-1)/gcd(...); to be honest we test the d-th-power character chi_d(b*) which
IS coset-dependent, so we instead test the coset-INVARIANT quantity: the d-th power character of the
COSET REP's index I=L mod m, for d | m. This is distinct from a2ad4130b (which tested v2(I), AP, mod-3
of I) — here we test the MULTIPLICATIVE d-th-power residue structure of I in Z_m, not its additive
arithmetic. Probe-first; PROPER mu_n; p>>n^3; many structured primes; never n=q-1.
"""
import cmath, math
from collections import Counter

def is_prime(p):
    if p<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if p%q==0: return p==q
    d=p-1;r=0
    while d%2==0: d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a%p==0: continue
        x=pow(a,d,p)
        if x==1 or x==p-1: continue
        ok=False
        for _ in range(r-1):
            x=x*x%p
            if x==p-1: ok=True;break
        if not ok: return False
    return True

def find_primes(n,count,beta=4):
    out=[];k=(n**beta)//n+1
    while len(out)<count:
        p=k*n+1
        if is_prime(p): out.append(p)
        k+=1
    return out

def primitive_root(p):
    phi=p-1;factors=set();m=phi;f=2
    while f*f<=m:
        if m%f==0:
            factors.add(f)
            while m%f==0: m//=f
        f+=1
    if m>1: factors.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in factors): return g
    raise RuntimeError

def worstb_index(n,p,cap):
    g0=primitive_root(p)
    g=pow(g0,(p-1)//n,p)
    elems=[1]
    for _ in range(n-1): elems.append(elems[-1]*g%p)
    tp=2*math.pi/p
    def epv(t): a=tp*(t%p); return complex(math.cos(a),math.sin(a))
    m=(p-1)//n
    cap=min(m,cap)
    best=-1.0; bestI=None
    b=1
    for t in range(cap):
        # b = g0^t ; coset index I = t (mod m), since b runs over coset reps as g0^t
        S=sum(epv(b*x) for x in elems)
        a=abs(S)
        if a>best: best=a; bestI=t
        b=b*g0%p
    return bestI,m,best,cap

def main():
    print("# Door-IV worst-b multiplicative d-th-power-residue structure of the coset index I in Z_m")
    print("# tests: is I=argmax|S| disproportionately a d-th power residue mod m? (chi_d bias => thin set)")
    print("# flat (~1/d each residue / ~1/2 QR) => worst-b coset index is multiplicatively GENERIC => lever dead")
    print()
    for n in (16,32,64):
        # gather many worst-b coset indices across many primes to get statistics
        idxs=[]
        ms=[]
        primes=find_primes(n,18,beta=4)
        for p in primes:
            I,m,M,cap=worstb_index(n,p,cap=4000)
            idxs.append(I); ms.append(m)
        print(f"n={n}: collected {len(idxs)} worst-b coset indices over {len(primes)} primes (sampled prefix cap=4000 -> SAMPLED argmax, lower bound on M)")
        # d-th power residue test: for each d, is I a d-th power mod m? need gcd(d, ...); use
        # QR-style test: I is a d-th power residue mod m iff I^(phi.../d) ... simplest robust proxy:
        # test I mod d distribution (multiplicative coset of <g0^d> corresponds to I mod d when d | m).
        for d in (2,3,4,5,8):
            # residue of I mod d among primes where d | m (so the d-th-power-coset question is well-posed)
            rs=[I%d for I,m in zip(idxs,ms) if m%d==0]
            if not rs:
                print(f"    d={d}: (no primes with d|m in sample)")
                continue
            c=Counter(rs)
            dist={k:round(c.get(k,0)/len(rs),3) for k in range(d)}
            print(f"    d={d}: I mod d distribution over {len(rs)} primes = {dist}  (flat={round(1/d,3)} each)")
        # genuine d-th-power-RESIDUE character (multiplicative, not additive mod d): chi(I) = is I a
        # square / cube residue mod m. Test the QUADRATIC residue rate of I in Z_m (m may be composite;
        # use Jacobi-like via gcd-coprime part). Simplify: rate that I is a perfect square mod the
        # largest prime factor of m (a clean multiplicative character).
        def largest_prime_factor(x):
            f=2;lp=1
            while f*f<=x:
                while x%f==0: lp=f; x//=f
                f+=1
            if x>1: lp=x
            return lp
        qr=0;tot=0
        for I,m in zip(idxs,ms):
            lp=largest_prime_factor(m)
            if lp<3 or I%lp==0: continue
            tot+=1
            if pow(I%lp,(lp-1)//2,lp)==1: qr+=1
        if tot:
            print(f"    QR-rate of I mod (largest prime factor of m): {qr}/{tot} = {round(qr/tot,3)} (generic=0.5)")
        print()

if __name__=="__main__":
    main()
