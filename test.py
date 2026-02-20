from sage.all import *
from MacMahon import MacMahonSymmetricFunctions
from vector_partition import VectorPartition
R = QQ
A = MacMahonSymmetricFunctions(R)

P = A.P()
M = A.M()
E = A.E()
H = A.H()

lam = VectorPartition([[1,1]])   

p = P[lam]
m = M[lam]
e = E[lam]
h = H[lam]

# 1) Does Sage think a coercion exists
print("M <- P ?", M.has_coerce_map_from(P))
print("P <- M ?", P.has_coerce_map_from(M))
print("P <- E ?", P.has_coerce_map_from(E))
print("P <- H ?", P.has_coerce_map_from(H))

# 2) What is the actual map object
print("M.coerce_map_from(P):", M.coerce_map_from(P))
print("P.coerce_map_from(M):", P.coerce_map_from(M))
print("P.coerce_map_from(E):", P.coerce_map_from(E))
print("P.coerce_map_from(H):", P.coerce_map_from(H))

# 3) Explicit coercion on elements
print("M(p) =", M(p))     # coercion P -> M
print("P(m) =", P(m))     # coercion M -> P
print("P(e) =", P(e))     # coercion E -> P
print("P(h) =", P(h))     # coercion H -> P
print("H(p) =", H(p))     # coercion P -> H

# 4) Round trip tests 
print("P(M(p)) == p ?", P(M(p)) == p)
print("M(P(m)) == m ?", M(P(m)) == m)

# 5) Mixed arithmetic should auto coerce
print("m + p =", m + p)          
print("p + m =", p + m)          
print("p * m =", p * m)          

# 6) Checking Monomial Multiplication

print("M[1,1] * M[2,2] =", M[1,1] * M[2,2])
