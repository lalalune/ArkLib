import math
def is_prime(m):
    if m<2:return False
    i=2
    while i*i<=m:
        if m%i==0:return False
        i+=1
    return True
def find_prime(n,lo):
    p=lo
    while True:
        if (p-1)%n==0 and is_prime(p):return p
        p+=1
def subgroup(p,n):
    for g0 in range(2,p):
        g=pow(g0,(p-1)//n,p)
        if len({pow(g,i,p) for i in range(n)})==n:
            return [pow(g,i,p) for i in range(n)]
def maxperiod(n,p):
    H=subgroup(p,n); tp=2*math.pi
    B=0.0; argb=0
    for b in range(1,p):
        c=sum(math.cos(tp*(b*x%p)/p) for x in H)
        s=sum(math.sin(tp*(b*x%p)/p) for x in H)
        mag=math.hypot(c,s)
        if mag>B: B=mag; argb=b
    return B
print(f"{'n':>3} {'p':>8} {'B=max|eta|':>11} {'sqrt2*sqrtn':>11} {'2sqrt(n-1)':>11} {'sqrt(2n ln p)':>13} {'B/sqrtn':>8} {'B/sqrt(n ln p)':>14}")
for n in [4,8,16,32,64]:
    for mult in [3,5]:
        p=find_prime(n,n**mult)
        if p>200000 and n>=32: continue
        B=maxperiod(n,p)
        sf=math.sqrt(2)*math.sqrt(n); ram=2*math.sqrt(n-1)
        log=math.sqrt(2*n*math.log(p))
        flag=" <-- B>sqrt2*sqrtn (REFUTES Shaw Flatness)" if B>sf else ""
        print(f"{n:>3} {p:>8} {B:>11.3f} {sf:>11.3f} {ram:>11.3f} {log:>13.3f} {B/math.sqrt(n):>8.3f} {B/math.sqrt(n*math.log(p)):>14.3f}{flag}")
