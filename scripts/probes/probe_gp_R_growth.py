import numpy as np, math
def isprime(q):
    if q<2: return False
    if q%2==0: return q==2
    i=3
    while i*i<=q:
        if q%i==0: return False
        i+=2
    return True
def primeat(n,beta):
    q=int(n**beta)
    while not(isprime(q) and (q-1)%n==0): q+=1
    return q
def genmu(p,n):
    e=(p-1)//n
    for a in range(2,p):
        z=pow(a,e,p)
        if pow(z,n//2,p)!=1: return z
def Rval(n,p):
    z=genmu(p,n); G=[pow(z,i,p) for i in range(n)]
    arr=np.zeros(p,dtype=np.float64); 
    for x in G: arr[x]=1.0
    S=np.fft.rfft(arr)          # real FFT; |S_b| for b=0..p//2 (rest are conjugates)
    mag=np.abs(S); mag[0]=0     # drop b=0 (=n)
    mx=float(mag.max())
    m=(p-1)//n
    return mx/math.sqrt(2*n*math.log(m)), m, mx
print("R(n)=max|eta|/sqrt(2n ln m) at fixed beta, growing n",flush=True)
for beta in [3.5, 4.0]:
    row=[]
    for n in [32,64,128,256,512]:
        p=primeat(n,beta)
        if p> 60_000_000: 
            row.append((n,'skip(p too big)')); continue
        R,m,mx=Rval(n,p)
        row.append((n, round(R,4)))
    print(f"beta={beta}: R by n = {row}",flush=True)
