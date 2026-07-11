"""
Pin the EXACT excess threshold: for fixed n, sweep p across n^c and count depth-3 excess
(exhaustively, averaged over several primes per c) to find the critical c* where E_3 excess
turns on. Compare measured c* to:
  - naive Poisson:  excess>0 when p < n^6/36  => c* = 6 - log_n(36) -> 6 (large n)
  - floor needs no excess at depth<=ceil(log m) = ceil(3c log2 n)... we just want c*.

The floor delta*=...H(rho)/(beta log n) requires E_r=E_r^C for r<=ceil(log m). Since m~p/n~n^{c-1},
ceil(log m)~(c-1)log n. Floor SURVIVES iff smallest excess depth r*(n,p) > (c-1) log2 n.
We extract r*(n,p) and its scaling.
"""
import sys, itertools, math
sys.path.insert(0,"/tmp/lll407")
from probe_407_excess_lll_setup import is_prime, primitive_nth_root
from probe_407_excess_lll_bruteforce import is_C_trivial
from collections import defaultdict

def pr(*a): print(*a,flush=True)

def primes_at(n,c,count):
    lo=int(n**c);k=max(1,(lo-1)//n);out=[]
    while len(out)<count:
        p=1+k*n
        if is_prime(p):out.append(p)
        k+=1
    return out

def excess_count_r(n,p,h,r):
    pows=[pow(h,c,p) for c in range(n)]
    table=defaultdict(list)
    for combo in itertools.combinations(range(n),r):
        s=0
        for c in combo: s+=pows[c]
        table[s%p].append(combo)
    cnt=0
    for s,combos in table.items():
        L=len(combos)
        if L<2:continue
        for i in range(L):
            for j in range(i+1,L):
                A,B=combos[i],combos[j]
                if set(A).isdisjoint(B):
                    if not is_C_trivial(list(A)+list(B),[1]*r+[-1]*r,n):
                        cnt+=1
    return cnt

if __name__=="__main__":
    pr("=== EXACT E_3 excess threshold: mean #excess over primes vs c (p~n^c) ===")
    pr("Poisson naive lambda_3 = C(n,3)^2/p. Measured = avg over primes.\n")
    pr(f"{'n':>5}{'c':>6}{'p~':>14}{'naive_lam3':>12}{'meas_avg_E3excess':>18}{'fracPrimes>0':>13}")
    for mu in (4,5,6,7,8):
        n=1<<mu
        for c in [3.5,4.0,4.5,5.0,5.5,6.0]:
            cnt_primes = 4 if n<=128 else 3
            ps=primes_at(n,c,cnt_primes)
            tot=0; pos=0
            for p in ps:
                h=primitive_nth_root(p,n)
                e=excess_count_r(n,p,h,3)
                tot+=e; pos+= (e>0)
            avg=tot/len(ps)
            lam=math.comb(n,3)**2/(int(n**c))
            pr(f"{n:>5}{c:>6}{('n^%.1f'%c):>14}{lam:>12.2e}{avg:>18.2f}{pos}/{len(ps):>11}")
        pr("")
