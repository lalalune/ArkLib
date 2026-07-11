import math
# DC-essentiality: at prize (p=n^beta, r ~ ln q), the DC term n^{2r}/q exceeds Wick=(2r-1)!! n^r.
# => raw E_r >= n^{2r}/q > Wick => non-DC GaussianEnergyBound (E_r<=Wick) is FALSE => non-DC sup chain vacuous.
# Find the CLEANEST sufficient condition for n^{2r}/q > Wick that's formalizable.

def dfact(k):
    r=1.0
    while k>1:
        r*=k; k-=2
    return r

def logdfact(k):  # log (2r-1)!!
    s=0.0
    while k>1:
        s+=math.log(k); k-=2
    return s

print("crossover scan: log(DC/Wick) = 2r ln n - ln q - [ln(2r-1)!! + r ln n], r=round(ln q)")
for a in [3,4,6,8,12,20,30]:
    n=2**a
    beta=4.0
    q=n**beta
    lnq=math.log(q)
    r=max(1,round(lnq))
    logDC = 2*r*math.log(n) - math.log(q)
    logWick = logdfact(2*r-1) + r*math.log(n)
    print(f"n=2^{a}={n}: r={r}  log(DC/Wick)={logDC-logWick:+.1f}  (DC>Wick={'YES' if logDC>logWick else 'no'})")

# Clean sufficient condition: DC/Wick = n^{2r}/(q (2r-1)!! n^r) = n^r / (q (2r-1)!!).
# n^r/(2r-1)!! grows like (n/(2r))^r * sqrt stuff -> for n >> r^2, n^r >> (2r-1)!! ~ (2r)^r/2^r e^{-r}...
# (2r-1)!! <= (2r)^r. So DC/Wick >= n^r/(q (2r)^r) = (n/(2r))^r / q.
# (n/(2r))^r > q  <=>  r ln(n/2r) > ln q.  With r~ln q, n=2^a: need ln(n/2r)>1 i.e n>2e r ~ 5.4 ln q.
print("\nClean sufficient lemma: if (n/(2r))^r > q  then DC > Wick (uses (2r-1)!!<=(2r)^r).")
for a in [6,8,12,20,30]:
    n=2**a; q=n**4.0; r=max(1,round(math.log(q)))
    lhs = r*math.log(n/(2*r)); rhs=math.log(q)
    print(f"n=2^{a}: r={r} r*ln(n/2r)={lhs:.1f} vs ln q={rhs:.1f}  => (n/2r)^r>q : {'YES' if lhs>rhs else 'no'}")
