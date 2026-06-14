import cmath, math, random
random.seed(1)
TAU=2*math.pi
def lognorm2(n,S):
    tot=0.0
    for j in range(1,n,2):
        z=0+0j
        for i in S: z+=cmath.exp(1j*TAU*((j*i)%n)/n)
        a=abs(z)
        if a<1e-12: return None
        tot+=math.log2(a)
    return tot
def nonantip(n,S):
    half=n//2; Sset=set(S)
    return [i for i in S if ((i+half)%n not in Sset) or (i<(i+half)%n)]
def maxnorm(n,trials):
    half=n//2; best=-1; bestS=None; bestkind=''
    cands=[]
    for L in range(half//2, half+1):       # intervals [0,L)
        cands.append(('int%d'%L, list(range(L))))
    for step in (1,3,5,7,9,11):            # APs
        cands.append(('ap%d'%step,[(step*t)%n for t in range(half)]))
    for _ in range(trials):
        cands.append(('rand',[i for i in range(n) if random.random()<0.55]))
    for kind,S in cands:
        S=nonantip(n,S)
        if not S: continue
        v=lognorm2(n,S)
        if v is not None and v>best: best=v; bestS=S; bestkind=kind
    return best,bestS,bestkind
out=open('/tmp/bind2.txt','w')
for n in (32,64,128):
    b,S,kind=maxnorm(n, 2000 if n<128 else 600)
    amgm=(n/4.0)*math.log2(len(S))
    # prize prime scale: log2 p ~ 128 + log2 n  (q ~ n*2^128)
    logp=128+math.log2(n)
    out.write(f"n={n}: realized max log2|N|~{b:.1f} (|S|={len(S)}, {kind}); AM-GM={amgm:.1f}; gap={amgm-b:.1f}; "
              f"log2 p(prize ~n*2^128)={logp:.1f}; H {'EXCEEDS' if b>logp else 'below'} p by {abs(b-logp):.1f} bits\n")
    out.flush()
out.close()

# RESULT (2026-06-14): realized max log2|N(beta_S)| over non-antipodal S, vs prize prime p~n*2^128:
#   n=32 : 29.9  (p~133, H below p by 103 bits)  -> (BIND) closed, large margin
#   n=64 : 74.3  (p~134, H below p by  60 bits)  -> (BIND) closed
#   n=128: 176.1 (p~135, H EXCEEDS p by 41 bits) -> (BIND) max-norm crosses p here
# So max-norm H(n) crosses the prize prime between n=64 and n=128 (matches issue body "closed <=64,
# open >=112"). Structure gap (AM-GM (n/4)log2|S| minus realized): 1.4, 4.3, 9.8 bits at n=32/64/128
# (~x2.3 per doubling) = the loose-by-structure term a structure-aware bound must capture.
# Random sampling => realized is a LOWER bound on true max => true crossing is at n <= ~96-112.
# Note: H(n)>p does NOT by itself break (BIND) — that needs the COUNTING #relevant-subsets > p
# (the binding-band antipodal-free subsets), which is the actual BGK/Paley wall.
