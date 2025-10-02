## JLM 10/2/25
## Compute the coefficient of the MacMahon monomial symmetric function
## M_Mu in the MacMahon power-sum symmetric function P_La

def PtoM(Mu,La):
    co = 0
    ell = len(La)
    m = len(Mu)
    r = len(Mu[0])
    for k in cartesian_product_iterator( [list(range(m)) for i in range(ell)] ):
        vsum = {i:vector(r*[0]) for i in range(m)}
        for j in range(ell):
            vsum[k[j]] += La[j]
        if all(vsum[i] == Mu[i] for i in range(m)):
            co += 1
    return co
