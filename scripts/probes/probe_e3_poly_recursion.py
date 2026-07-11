import sympy as sp
m = sp.symbols('m')
# Closed forms in m:
B2 = 2*m
B4 = sp.expand((3*(2*m)**2 - 3*(2*m)))   # E_2 with n=2m
B6 = sp.expand(15*(2*m)**3 - 45*(2*m)**2 + 40*(2*m))  # E_3 with n=2m
print("B2(m) =", B2)
print("B4(m) =", sp.expand(B4))
print("B6(m) =", sp.expand(B6))

# Recursion to verify (as identities in m, replacing m-1):
# B2(m) = B2(m-1) + C(2,2)C(2,1)*B0  = B2(m-1) + 1*2*1 = B2(m-1)+2
print("\nCheck B2 recursion: B2(m) - B2(m-1) == 2 :", sp.simplify(B2 - B2.subs(m,m-1) - 2)==0)
# B4(m) = B4(m-1) + C(4,2)C(2,1)*B2(m-1) + C(4,4)C(4,2)*B0
#       = B4(m-1) + 6*2*B2(m-1) + 1*6*1 = B4(m-1) + 12*B2(m-1) + 6
rhs4 = B4.subs(m,m-1) + 12*B2.subs(m,m-1) + 6
print("Check B4 recursion:", sp.simplify(B4 - rhs4)==0)
# B6(m) = B6(m-1) + C(6,2)C(2,1)B4(m-1) + C(6,4)C(4,2)B2(m-1) + C(6,6)C(6,3)B0
#       = B6(m-1) + 15*2*B4(m-1) + 15*6*B2(m-1) + 1*20*1
#       = B6(m-1) + 30*B4(m-1) + 90*B2(m-1) + 20
rhs6 = B6.subs(m,m-1) + 30*B4.subs(m,m-1) + 90*B2.subs(m,m-1) + 20
print("Check B6 recursion:", sp.simplify(B6 - rhs6)==0)
# base cases m=0:
print("\nbase B2(0)=",B2.subs(m,0)," B4(0)=",B4.subs(m,0)," B6(0)=",B6.subs(m,0))
