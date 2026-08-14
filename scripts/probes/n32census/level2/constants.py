import math
P = 15*(1<<27)+1
# n=16 probe conventions (order_gen base-3 search)
def order_gen(m):
    x = 3
    while True:
        g = pow(x, (P-1)//m, P)
        if g != 1 and pow(g, m//2, P) != 1:
            return x, g
        x += 1
x16, g16 = order_gen(16)
print("n16 probe: base x =", x16, " g16 =", g16)
z = 5
while pow(z, 16, P) == 1: z += 1
print("n16 z =", z, " w =", pow(z,2,P))

# n=32 O87 convention: g0 = 31, h = g0^((P-1)/32)
h32 = pow(31, (P-1)//32, P)
print("n32 h32 =", h32, " h32^16 =", pow(h32,16,P), "(must be != 1), h32^32 =", pow(h32,32,P))
z = 5
while pow(z, 32, P) == 1: z += 1
print("n32 z =", z, " w =", pow(z,2,P), " 5^32 mod P =", pow(5,32,P))
print("C(32,17) =", math.comb(32,17), "; C(31,16) =", math.comb(31,16))
print("C(16,9) =", math.comb(16,9))
n0_mono = sum(math.comb(8,s)*2**s for s in range(9%2, min(9,16-9)+1, 2))
print("N0(16,9) =", n0_mono)
n0_mono16 = sum(math.comb(4,s)*2**s for s in range(5%2, min(5,8-5)+1, 2))
print("N0(8,5) =", n0_mono16, " C(8,5) =", math.comb(8,5))
