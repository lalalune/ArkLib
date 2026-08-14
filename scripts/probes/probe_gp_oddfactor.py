import itertools, cmath, math
def largest_odd_prime(N):
    N=abs(int(round(N)))
    if N==0: return 0
    while N%2==0: N//=2
    if N==1: return 1
    best=1; d=3
    M=N
    while d*d<=M:
        while M%d==0: best=d; M//=d
        d+=2
    if M>1: best=M
    return best
def maxoddprime(n, twor):
    h=n//2
    roots=[cmath.exp(2j*math.pi*e/n) for e in range(n)]
    odd=[j for j in range(1,n) if math.gcd(j,n)==1]
    best=1
    # enumerate reduced w in Z^h with sum|w|<=twor, parity, w!=0
    def gen(pos,rem,cur):
        if pos==h:
            if (twor-rem)%2==0 and any(cur): yield tuple(cur)
            return
        for val in range(-rem,rem+1):
            cur.append(val); yield from gen(pos+1,rem-abs(val),cur); cur.pop()
    seen=set()
    for w in gen(0,twor,[]):
        pr=1.0
        for j in odd:
            pr*=abs(sum(w[a]*roots[(a*j)%n] for a in range(h)))
        nm=round(pr)
        lop=largest_odd_prime(nm)
        if lop>best: best=lop
    return best
print("max largest-odd-prime-factor of balanced norms at depth 2r (= largest odd prime p with a genuine relation at depth 2r)",flush=True)
for n in [8,16]:
    row=[]
    kmax=14 if n==8 else 10
    for twor in range(2,kmax+1,2):
        mp=maxoddprime(n,twor)
        row.append((twor, mp, f"n^{math.log(max(mp,2))/math.log(n):.2f}"))
    print(f"n={n}: (2r, maxOddPrime, =n^?): {row}",flush=True)
