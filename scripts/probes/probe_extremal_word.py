# Decisive test of Conjecture J: is the power word x^t the EXTREMAL (max-list) word
# at sub-Johnson agreement t for smooth RS[F_p, mu_n, k]?
# list(w) = #{P deg<k : #{i: P(alpha_i)=w_i} >= t}.  Compare x^t vs random vs other structured words.
import itertools, random
random.seed(1)

def subgroup(p,n):
    e=(p-1)//n
    for b in range(2,p):
        g=pow(b,e,p)
        if g!=1 and pow(g,n//2,p)!=1:
            G=[]; x=1
            for _ in range(n): G.append(x); x=x*g%p
            if len(set(G))==n: return G
    return None

def list_size(p, dom, k, w, t):
    # enumerate all deg<k polynomials P (coeffs c0..c_{k-1}), count agreements with w
    n=len(dom)
    best=0; cnt=0
    # precompute powers
    pw=[[pow(a,j,p) for j in range(k)] for a in dom]
    for coeffs in itertools.product(range(p),repeat=k):
        agree=0
        for i,a in enumerate(dom):
            v=0
            for j in range(k): v=(v+coeffs[j]*pw[i][j])%p
            if v==w[i]: agree+=1
        if agree>=t: cnt+=1
    return cnt

def word_monomial(dom,p,e):  # x^e evaluated
    return [pow(a,e,p) for a in dom]

p=97; n=16; k=2
dom=subgroup(p,n)
import math
johnson=math.sqrt(n*k)
print(f"p={p} n={n} k={k} rate={k/n} Johnson agreement≈{johnson:.2f}")
for t in [3,4,5]:
    sub = "SUB-Johnson" if t < johnson else "Johnson+"
    # power word x^t
    L_pow = list_size(p,dom,k,word_monomial(dom,p,t),t)
    # other monomials x^e
    L_mon = {e: list_size(p,dom,k,word_monomial(dom,p,e),t) for e in [t-1,t,t+1,k, n-1]}
    # random words
    Lr=[]
    for _ in range(40):
        w=[random.randrange(p) for _ in range(n)]
        Lr.append(list_size(p,dom,k,w,t))
    print(f" t={t} ({sub}): L(x^t)={L_pow}  max_random={max(Lr)}  monomials={L_mon}")
