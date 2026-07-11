import math

def H2(x):
    if x<=0 or x>=1: return 0.0
    return -x*math.log2(x)-(1-x)*math.log2(1-x)

def Hq(d, q):
    # q-ary entropy: H_q(d) = d*log_q(q-1) - d log_q d - (1-d) log_q (1-d)
    if d<=0 or d>=1: return 0.0
    lq = math.log(q)
    return (d*math.log(q-1) - d*math.log(d) - (1-d)*math.log(1-d))/lq

def kambire(rho, beta, mu):
    # 1 - rho - H2(rho)/(beta*mu)   (mu = log2 n)
    return 1 - rho - H2(rho)/(beta*mu)

def ldcap_radius(rho, q):
    # solve Hq(d)=1-rho for d in (0, 1-1/q)
    target = 1-rho
    lo, hi = 1e-9, 1-1.0/q
    for _ in range(200):
        mid=(lo+hi)/2
        if Hq(mid,q) < target: lo=mid
        else: hi=mid
    return (lo+hi)/2

print(f"{'mu':>4}{'rho':>7}{'beta':>5}{'Johnson':>10}{'Kambire':>10}{'LDcap':>10}{'|diff|':>11}")
for beta in [4]:
    for rho in [0.5, 0.25, 0.125]:
        for mu in [16,20,24,30,32,48,64]:
            n=2**mu
            q=n**beta  # approx prime
            kam=kambire(rho,beta,mu)
            ld=ldcap_radius(rho,q)
            john=1-math.sqrt(rho)
            print(f"{mu:>4}{rho:>7}{beta:>5}{john:>10.4f}{kam:>10.5f}{ld:>10.5f}{abs(kam-ld):>11.2e}")
