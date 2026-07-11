import cmath, math
# NON-MOMENT structural probe: the dilation-orbit phase cocycle.
# Recursion f_{i+1}(b) = f_i(b) + f_i(zeta_{i+1} * b),  zeta_{i+1} a primitive 2^{i+1}-th root.
# Question: along the descent path of the WORST frequency b* at the top level mu_n,
# is the per-level alignment angle theta_i = arg(f_i(b)) - arg(f_i(zeta b)) structurally
# constrained so the product of |1+e^{i theta_i}|/2 factors does NOT stay near 1?
# i.e. does the L-infinity actually scale by ~sqrt2 not 2, and is there a CLEAN per-level identity?

def primfind(n, lo):
    q=max(n+1,lo)
    while True:
        if (q-1)%n==0 and all(q%p for p in range(2,int(q**.5)+1)):
            for g in range(2,q):
                if pow(g,q-1,q)==1 and all(pow(g,(q-1)//pp,q)!=1 for pp in set(f for f in range(2,q) if (q-1)%f==0 and all(f%d for d in range(2,int(f**.5)+1)))):
                    return q,g
        q+=1

def eta(b, G, p):
    return sum(cmath.exp(2j*math.pi*((b*x)%p)/p) for x in G)

print("n: top M, then per-level |f_i(b*)|, alignment cos_i along the worst descent path", flush=True)
for n in [16,32,64]:
    p,g = primfind(n, 5000)
    z = pow(g,(p-1)//n,p)             # primitive n-th root, n=2^a
    Gtop = [pow(z,i,p) for i in range(n)]
    # worst freq at top
    M=0; bs=1
    for b in range(1,p):
        v=abs(eta(b,Gtop,p))
        if v>M: M=v; bs=b
    # tower levels: G_i = mu_{2^i}.  zeta_{i+1} = primitive 2^{i+1}-th root = z^{n/2^{i+1}}
    a = int(math.log2(n))
    # build subgroups mu_{2^i}
    levels=[]
    for i in range(a+1):
        m=2**i
        zz=pow(z, n//m, p)
        levels.append([pow(zz,j,p) for j in range(m)])
    # descent of frequency b*: at level i the relevant freq for the union-recursion
    # G_{i+1}=G_i ⊔ ζ_{i+1}·G_i,  f_{i+1}(b)=f_i(b)+f_i(ζ_{i+1} b)
    # so the "path" tracks b through dilations. report |f_i(bs)| and cos of the two children.
    line=f"n={n} M={M:.2f} (M/sqrt(n)={M/math.sqrt(n):.3f}): "
    cosline=""
    for i in range(a):
        m=2**i
        Gi=levels[i]
        zeta=pow(z, n//(2*m), p)   # primitive 2^{i+1}-th root
        fb = eta(bs, Gi, p)
        fzb= eta((bs*zeta)%p, Gi, p)
        # alignment cos between the two children
        if abs(fb)>1e-9 and abs(fzb)>1e-9:
            cosv = (fb*fzb.conjugate()).real/(abs(fb)*abs(fzb))
        else:
            cosv=float('nan')
        cosline+=f"L{i}->{i+1} cos={cosv:+.3f} |fb|={abs(fb):.2f}|fzb|={abs(fzb):.2f}; "
    print(line, flush=True)
    print("   ", cosline, flush=True)
