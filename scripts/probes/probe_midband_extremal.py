# Conjecture J': in the MIDDLE BAND (above Johnson, below capacity) t=k+m+1, is the
# power/coset word the EXTREMAL max-list word? p=17, n=16 (F_17^*), k=4. enumerate all 17^4 polys.
import itertools, random
random.seed(7)
p=17; n=16; k=4
dom=list(range(1,17))  # F_17^* = mu_16 (full group)
import math
johnson=math.sqrt(n*k)  # =8
cap_agree=k              # =4 (radius 1-rho)
print(f"p={p} n={n} k={k} rate={k/n}; capacity agreement={cap_agree}, Johnson agreement={johnson}")
print("middle band = agreement t in (4,8) i.e. t=5,6,7")

pw=[[pow(a,j,p) for j in range(k)] for a in dom]
def list_size(w,t):
    cnt=0
    for coeffs in itertools.product(range(p),repeat=k):
        agree=0
        for i in range(n):
            v=0
            for j in range(k): v=(v+coeffs[j]*pw[i][j])%p
            if v==w[i]: agree+=1
        if agree>=t: cnt+=1
    return cnt

def mono(e): return [pow(a,e,p) for a in dom]

for t in [5,6,7]:
    # power words x^e (e>=k so not a codeword); coset construction lives at x^t
    Lpow = {e: list_size(mono(e),t) for e in [k,k+1,t,k+2, n-1, n-2]}
    Lr=[]
    best_rand_w=None
    for _ in range(60):
        w=[random.randrange(p) for _ in range(n)]
        L=list_size(w,t); Lr.append(L)
    print(f" t={t}: power/monomial lists={Lpow}  | random: max={max(Lr)} mean={sum(Lr)/len(Lr):.1f}")
