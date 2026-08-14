from sympy import symbols,expand,Poly
n=symbols('n')
g=1240539300*n**7 -20744573850*n**6 +206963306550*n**5 -1327347186165*n**4 +5524263935190*n**3 -14357763632355*n**2 +20957471507115*n -12885585512800
cs=[102304530207880,109272934287660,57933199896000,16343700953580,2754236164680,361823962500,19297278000,1240539300]
u=2*n-7
rhs=sum(cs[k]*u**k for k in range(8))
lhs=expand(128*g)
print("128*g == cert:",expand(lhs-rhs)==0)
# full: 128*deficit = n * rhs
deficit=n*g
print("128*deficit = n*cert:",expand(128*deficit - n*rhs)==0)
