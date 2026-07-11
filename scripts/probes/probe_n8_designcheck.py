from itertools import combinations
from math import comb

sets = list(combinations(range(8), 4))
fam = []
for S in sets:
    if all(len(set(S) & set(T)) <= 2 for T in fam):
        fam.append(S)
print("greedy family (4-subsets of [8], pairwise inter<=2):", len(fam))
print("C(8,4)=", comb(8, 4), " naive n/(a-k)=", 8 // (4 - 2))
