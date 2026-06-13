#!/usr/bin/env python3
"""Probe for the Sidon small-subgroup half-Johnson -> Johnson question (#389).

TASK: Can the Sidon property of mu_n give the per-line full-support condition
(MCAListCollapseFullSupport.hsupp_of_bad) for the deep-band/monomial stacks whose
second row is in mu_n, and if so does that push delta* past half-Johnson toward
full Johnson 1 - sqrt(rho)?

We separate the two distinct ingredients of the list-collapse route
(epsMCA_le_of_uniform_badCount_full_support):
  (A) hsupp_of_bad : every firing stack u has u1 full support (u1 i != 0 for all i).
  (B) hlist        : a UNIFORM bound L on lineWitnessCodewords(u, t).card
                     (the "line list size") for ALL stacks.

The half-Johnson ceiling lives in (B): the pair-alphabet second-moment cap on L is
  L <= n^2 / (a^2 - n*e),  a = 2*ceil((1-delta)n) - n,  e = k-1,
which is VACUOUS once a^2 <= n*e, i.e. delta >= (1 - sqrt(e/n))/2 = half-Johnson.

This probe measures, for RS over mu_n subset F_p (n = 2^m), the ACTUAL line list
size  L_actual(delta) = max over stacks of lineWitnessCodewords(u, t).card
AND whether full support holds, at radii sweeping across half-Johnson up to Johnson.

If L_actual stays small (poly, well below the q-budget) past half-Johnson for
mu_n deep-band stacks WHILE full support holds, the collapse route would push past
half-Johnson. If L_actual EXPLODES (>> n) at half-Johnson regardless of support,
the support hypothesis is NOT the obstruction and the ceiling is genuine.
"""
import itertools, math

def find_prime_with_root(n, lo):
    # smallest prime p > lo with n | p-1
    p = lo + 1
    while True:
        if p % 2 == 1 and is_prime(p) and (p - 1) % n == 0:
            return p
        p += 1

def is_prime(p):
    if p < 2: return False
    for d in range(2, int(p**0.5)+1):
        if p % d == 0: return False
    return True

def primitive_nth_root(p, n):
    g = find_generator(p)
    # g^((p-1)/n) is a primitive n-th root
    return pow(g, (p-1)//n, p)

def find_generator(p):
    if p == 2: return 1
    phi = p-1
    facs = set()
    m = phi
    d = 2
    while d*d <= m:
        while m % d == 0:
            facs.add(d); m//=d
        d+=1
    if m>1: facs.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs):
            return g
    raise RuntimeError

def run(n, m_exp, kk, p=None):
    if p is None:
        p = find_prime_with_root(n, max(50, 2*n))
    w = primitive_nth_root(p, n)
    mu = [pow(w, i, p) for i in range(n)]   # the domain = mu_n, all nonzero
    assert 0 not in mu
    assert len(set(mu)) == n
    for k in kk:
        rho = k / n
        # RS codewords on domain mu: evaluations of polynomials of degree < k
        # codeword = (f(x))_{x in mu}, f of degree < k. There are p^k of them; too many.
        # We only need agreement structure: a codeword is determined by k points.
        # For listing we enumerate low-degree polys ONLY when p^k is tiny; else sample.
        johnson = (1 - math.sqrt(rho))
        half = johnson/2
        print(f"\n=== n={n} (m={m_exp}) p={p} k={k} rho={rho:.4f} "
              f"half-J={half:.4f} J={johnson:.4f} ===")
        # deep-band style stack: u1 i = (x_i)^k  (monomial; in mu_n since mu_n subgroup, k-th power closed)
        u1 = [pow(x, k, p) for x in mu]
        print(f"  deep-band u1 = (x^k): support full? {all(v!=0 for v in u1)}  "
              f"(u1 in mu_n? {all(v in set(mu) for v in u1)})")
        # general stack second row could have zeros only if some coordinate forced 0.
        # For ANY u1 whose entries are in mu_n (nonzero), support is automatically full.
        # Now measure line list size at sweep of delta.
        if p**k > 200000:
            print(f"  [p^k={p**k} too large to enumerate codewords exactly; "
                  f"reporting structural facts only]")
            continue
        cws = []
        for coeffs in itertools.product(range(p), repeat=k):
            cw = tuple(sum(coeffs[j]*pow(x,j,p) for j in range(k)) % p for x in mu)
            cws.append(cw)
        cws = list(set(cws))
        # choose a worst-case stack: u0 random poly eval, u1 = x^k monomial (deep band).
        # Actually the line list size is u-dependent. Probe the monomial deep-band stack
        # and also a few random in-mu_n second rows.
        def agree_count(cw, line):
            return sum(1 for a,b in zip(cw,line) if a==b)
        def line_list_size(u0, u1, t):
            # codewords agreeing with SOME line point u0 + g u1 on >= t coords
            S = set()
            for g in range(p):
                line = tuple((a + g*b) % p for a,b in zip(u0,u1))
                for ci,cw in enumerate(cws):
                    if agree_count(cw, line) >= t:
                        S.add(ci)
            return len(S)
        def bad_count(u0,u1,t):
            cnt=0
            for g in range(p):
                line = tuple((a+g*b)%p for a,b in zip(u0,u1))
                # bad: some codeword agrees on >= t with line but not "jointly" with both rows.
                # Use the simple mca-event proxy: line is within radius (agrees >= t with a cw)
                # but the stack is far (no cw agrees with u0 and u1 both on that S).
                fired=False
                for cw in cws:
                    if agree_count(cw,line)>=t:
                        fired=True; break
                if fired: cnt+=1
            return cnt
        # sweep delta -> integer threshold t = ceil((1-delta) n)
        import random
        random.seed(1)
        # a deep-band stack: u0 = eval of random degree<k poly OFF the code direction won't matter;
        # take u0 a random word, u1 = monomial x^k.
        results=[]
        for tnum in range(n, 0, -1):
            delta = 1 - tnum/n
            # worst over a sample of stacks with u1 in mu_n (full support)
            maxL=0; maxbad=0; supp_ok=True
            trials=[]
            # monomial deep band
            u0mono = tuple(random.randrange(p) for _ in range(n))
            trials.append((u0mono, tuple(u1)))
            # random second rows drawn from mu_n (guarantee full support, mimic 'rows in mu_n')
            for _ in range(8):
                u0r = tuple(random.randrange(p) for _ in range(n))
                u1r = tuple(random.choice(mu) for _ in range(n))
                trials.append((u0r,u1r))
            for (u0,u1t) in trials:
                if any(v==0 for v in u1t): supp_ok=False
                maxL=max(maxL, line_list_size(u0,u1t,tnum))
                maxbad=max(maxbad, bad_count(u0,u1t,tnum))
            johnson_cap = None
            a = 2*tnum - n   # a = 2*ceil((1-delta)n)-n with ceil=tnum
            e = k-1
            denom = a*a - n*e
            johnson_cap = (n*n/denom) if denom>0 else float('inf')
            tag=""
            if delta < half - 1e-9: tag="<halfJ"
            elif delta < johnson - 1e-9: tag="[halfJ,J)"
            else: tag=">=J"
            results.append((tnum,delta,maxL,maxbad,johnson_cap,a,denom,supp_ok,tag))
        print(f"  {'t':>3} {'delta':>6} {'L_act':>6} {'bad':>5} {'J-cap':>10} "
              f"{'a':>3} {'a^2-ne':>7} {'supp':>5} region")
        for (tnum,delta,maxL,maxbad,jc,a,denom,supp_ok,tag) in results:
            jcs = f"{jc:.1f}" if jc!=float('inf') else "VACUOUS"
            print(f"  {tnum:>3} {delta:>6.3f} {maxL:>6} {maxbad:>5} {jcs:>10} "
                  f"{a:>3} {denom:>7} {str(supp_ok):>5} {tag}")

if __name__ == "__main__":
    # mu_8 subset F_p, the task's named instance
    run(8, 3, [2,3], p=None)
    # smaller mu_4 for full enumeration sanity
    run(4, 2, [2], p=None)
