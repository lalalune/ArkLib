import cmath, math
TAU=2*math.pi
def rs(k):  # Rudin-Shapiro: (-1)^(#'11' pairs in binary k)
    b=bin(k)[2:]; c=sum(1 for i in range(len(b)-1) if b[i]=='1' and b[i+1]=='1'); return (-1)**c
def lognorm2(n,S):
    tot=0.0
    for j in range(1,n,2):
        z=sum(cmath.exp(1j*TAU*((j*i)%n)/n) for i in S)
        if abs(z)<1e-12: return None
        tot+=math.log2(abs(z))
    return tot
for n in (32,64,128):
    # Rudin-Shapiro-based 0/1 set: positions where RS=+1, then make non-antipodal
    S=[k for k in range(n) if rs(k)==1]
    half=n//2; Sset=set(S); S=[i for i in S if ((i+half)%n not in Sset) or i<(i+half)%n]
    v=lognorm2(n,S); amgm=(n/4.0)*math.log2(len(S)) if S else 0
    logp=128+math.log2(n)
    print(f"n={n}: Rudin-Shapiro 0/1 set |S|={len(S)}: log2|N|={v:.1f} | AM-GM={amgm:.1f} (deficit {amgm-v:.1f} bits) | log2 p={logp:.0f} | {'>p' if v and v>logp else '<p'}")
