################################################################################
################################################################################
################################################################################
##
##  Numerical functions required for basis-change computations.
##
################################################################################
################################################################################
################################################################################

## Factorial(thing)
## input: a number, a list, or a VectorPartition mu (I am getting tired of distinguishing between them)
## output: the product of factorials of all numbers at the lowest level of thing

def Factorial(thing):
    try:
        return factorial(thing)
    except:
        return prod(Factorial(x) for x in thing)
        
## Bars(mu)
## input: a VectorPartition mu
## output: $|\mu|$ as defined in Rosas (2001), p.330, before Theorem 3

def Bars(mu):
    Mu = list(mu)
    Done = []
    output = 1
    for part in Mu:
        if not part in Done:
            Done.append(part)
            output = output * Factorial(Mu.count(part))
    return output


## SetPToVecP(pi)
## input: a SetPartition pi of the set [n]
## output: the VectorPartition consisting of the indicator vectors of the blocks of pi

def SetPToVecP(pi):
    n = pi.base_set_cardinality()
    return VectorPartition([[1 if i in B else 0 for i in range(1,n+1)] for B in pi])

## Type(u,pi)
## Input: u is an integer vector of weight n; pi is a set partition of [n]
## Output: $\type_u(\pi)$, as defined in Rosas (2001), p.328, bottom

def Type(u,pi):
    r = len(u)
    psum = [sum(u[:k]) for k in range(r+1)]  ## partial sums
    ell = len(pi)
    n = sum(len(B) for B in pi)
    lam = [[len([j for j in B if psum[i]<j<=psum[i+1]]) for i in range(r)] for B in pi]
    return VectorPartition(lam)

## Choose(u,mu)
## Input: u is a vector of weight n and mu is a vector partition of weight n
## Output: $\binom{u}{\lambda}$, as defined in Rosas (2001), p.332, Prop. 5.

Choose = lambda u,mu: Factorial([u])/Factorial(mu)/Bars(mu)

################################################################################
################################################################################
################################################################################
##
##  Compute lifting maps, as defined in Rosas (2001), p.332, Defn. 6.
##
##  The lifting map \hat\rho maps a MacMahon basis element X[\lambda] to a linear combination of
##  *unitary* basis elements of the same kind.
##  TO DO: Extend so that they work on more general linear combinations of basis elements.
##
################################################################################
################################################################################
################################################################################

m = MacMahonSymmetricFunctions(QQ).Monomial()
p = MacMahonSymmetricFunctions(QQ).Powersum()
h = MacMahonSymmetricFunctions(QQ).Homogeneous()
e = MacMahonSymmetricFunctions(QQ).Elementary()
# f = MacMahonSymmetricFunctions(QQ).Forgotten()           # not yet implemented

def LiftM(mu):
    u = sum(mu)
    return 1/Choose(u,mu)/Bars(mu)*sum(m[SetPToVecP(pi)] for pi in SetPartitions(sum(u)) if Type(u,pi)==mu)
def LiftP(mu):
    u = sum(mu)
    return 1/Choose(u,mu)*sum(p[SetPToVecP(pi)] for pi in SetPartitions(sum(u)) if Type(u,pi)==mu)
def LiftH(mu):
    u = sum(mu)
    return 1/Choose(u,mu)/Factorial(mu)*sum(h[SetPToVecP(pi)] for pi in SetPartitions(sum(u)) if Type(u,pi)==mu)
def LiftE(mu):
    u = sum(mu)
    return 1/Choose(u,mu)/Factorial(mu)*sum(e[SetPToVecP(pi)] for pi in SetPartitions(sum(u)) if Type(u,pi)==mu)
def LiftF(mu):
    u = sum(mu)
    return 1/Choose(u,mu)/Bars(mu)*sum(f[SetPToVecP(pi)] for pi in SetPartitions(sum(u)) if Type(u,pi)==mu)


################################################################################
################################################################################
################################################################################
##
##  Compute scalar products of unitary standard basis elements.
##  In general XYProduct(pi, sigma) returns the scalar product <X[pi], Y[sigma]>,
##  where X,Y in {m,p,e,h,f} and pi, sigma are set partitions.
##  These functions implement the formulas in Doubilet 1972, Appendix 2, p. 394.
##
##  NOTE: Buried in Doubilet, and skimmed over in Rosas, is the fact that there
##    is an extra n! in all of Doubilet's formulas.  I have taken these out.
##
##  TO DO: Extend so that they work on more general linear combinations of basis elements.
##
################################################################################
################################################################################
################################################################################

## first some utilities

## given a pair of partitions (sigma, pi) such that pi coarsens sigma, return the integer partition lambda =(lambda_i) such that
## [sigma,pi] \isom \bigprod_i \Pi_{\lambda_i}.
## In other words, each part lambda_i corresponds to a block of pi being separated into lambda_i blocks in sigma.

def SPLambda(sigma, pi):
    L = [0]*len(pi)
    for sblock in sigma:
        for i in range(len(pi)):
            if sblock.issubset(pi[i]):
                L[i] = L[i]+1
    L.sort()
    L.reverse()
    return Partition(L)

## Doubilet formula #1

MHProduct = lambda pi,sigma: 0 if pi != sigma else 1
HMProduct = MHProduct

## Doubilet formula #2

def PPProduct(pi,sigma):
    if pi != sigma:
        return 0
    else:
        n = pi.base_set_cardinality()
        P = posets.SetPartitions(n)
        mu = P.moebius_function
        return 1 / mu(P.bottom(),pi)

## Doubilet formula #3

HPProduct = lambda pi,sigma: 1 if pi in sigma.coarsenings() else 0
PHProduct = lambda pi,sigma: EPProduct(sigma, pi)

## Doubilet formula #4

EPProduct = lambda pi,sigma: sigma.to_partition().sign() if pi in sigma.coarsenings() else 0
PEProduct = lambda pi,sigma: EPProduct(sigma, pi)

## Doubilet formula #5

def EEProduct(pi, sigma):
    n = pi.base_set_cardinality()
    if not n == sigma.base_set_cardinality():
        return 0
    else:
        xi = posets.SetPartitions(n).meet(sigma, pi)
        return product(Factorial(j) for j in xi.to_partition())

## Doubilet formula #6

def EHProduct(pi, sigma):
    n = pi.base_set_cardinality()
    if not n == sigma.base_set_cardinality():
        return 0
    else:
        P = SetPartitions(n)
        return 1 if P.meet(sigma, pi) == P.bottom() else 0
HEProduct = EHProduct

## Doubilet formula #7

def MMProduct(pi, sigma):
    n = pi.base_set_cardinality()
    if not n == sigma.base_set_cardinality():
        return 0
    else:
        P = posets.SetPartitions(n)
        mu = posets.SetPartitions(n).moebius_function
        return sum( mu(pi,tau) * mu(sigma,tau) / abs(mu(P.bottom(),tau)) for tau in pi.coarsenings() if tau in sigma.coarsenings())

## Doubilet formula #8

def EMProduct(pi, sigma):
    n = pi.base_set_cardinality()
    if not n == sigma.base_set_cardinality():
        return 0
    elif not pi in sigma.coarsenings():
        return 0
    else:
        return sigma.to_partition().sign() * prod(Factorial(i) for i in SPLambda(sigma, pi))

## Doubilet formula #9

HHProduct = EEProduct

## Doubilet formula #10

def MPProduct(pi, sigma):
    if not sigma in pi.coarsenings():  ## i.e., if zeta(pi, sigma) = 0
        return 0
    else:
        n = pi.base_set_cardinality()
        mu = posets.SetPartitions(n).moebius_function
        return mu(pi,sigma) / abs(mu(P.bottom(),sigma))
PMProduct = lambda sigma, pi: MPProduct(pi, sigma)

## Doubilet formula #11

def FMProduct(pi, sigma):
    n = pi.base_set_cardinality()
    if not n == sigma.base_set_cardinality():
        return 0
    else:
        P = posets.SetPartitions(n)
        mu = P.moebius_function
        return sum(abs(mu(pi,tau))*mu(sigma, tau)/abs(mu(P.bottom(),tau)) \
          for tau in P.join(pi, sigma).coarsenings())

MFProduct = lambda pi, sigma: FMProduct(sigma, pi)

## Doubilet formula #12

def FFProduct(pi, sigma):
    n = pi.base_set_cardinality()
    if not n == sigma.base_set_cardinality():
        return 0
    else:
        P = posets.SetPartitions(n)
        mu = P.moebius_function
        return pi.to_partition().sign() * sigma.to_partition().sign() * \
          sum(mu(pi,tau)*mu(sigma, tau)/abs(mu(P.bottom(),tau)) for tau in P.join(pi, sigma).coarsenings())

## Doubilet formula #13

def FHProduct(pi, sigma):
    n = pi.base_set_cardinality()
    if not n == sigma.base_set_cardinality():
        return 0
    elif not sigma in pi.coarsenings():
        return 0
    else:
        return prod(Factorial(j) for j in SPLambda(pi, sigma))

HFProduct = lambda pi, sigma: FHProduct(sigma, pi)

## Doubilet formula #14

def FPProduct(pi, sigma):
    n = pi.base_set_cardinality()
    if not n == sigma.base_set_cardinality():
        return 0
    elif not sigma in pi.coarsenings():
        return 0
    else:
        return pi.to_partition().sign() * sigma.to_partition().sign() * mu(pi, sigma) / abs(mu(P.bottom(),sigma))
PFProduct = lambda pi, sigma: FPProduct(sigma, pi)

## Doubilet formula #15

FEProduct = lambda pi, sigma: 0 if pi != sigma else pi.to_partition().sign() 
EFProduct = lambda pi, sigma: FEProduct(sigma, pi)

################################################################################
################################################################################
################################################################################
##
##  Actual basis change formulas
##
################################################################################
################################################################################
################################################################################

## Given a vector partition mu, expand p[mu] in the monomial basis

def PtoM(mu):
    u = sum(mu)
    n = sum(u)
    P = posets.SetPartitions(n)
    return Factorial(u) / Choose(u,mu) * \
      sum( 1 / Choose(u, la) / Factorial(la) * len([(pi,sigma) for pi in P for sigma in P if \
      Type(u,pi) == la and Type(u,sigma) == mu and pi in sigma.coarsenings()]) * m[la] \
      for la in VectorPartitions(u))

## Given a vector partition mu, expand h[mu] in the monomial basis

def HtoM(mu):
    u = sum(mu)
    n = sum(u)
    P = posets.SetPartitions(n)
    return Factorial(u) / Choose(u,mu) / Factorial(mu) * \
      sum( 1 / Choose(u, la) / Factorial(la) * sum(Factorial(P.meet(sigma,pi).to_partition()) \
      for sigma in P for pi in P if Type(u,pi) == la and Type(u,sigma) == mu) * m[la] \
      for la in VectorPartitions(u))

## Given a vector partition mu, expand e[mu] in the monomial basis

def EtoM(mu):
    u = sum(mu)
    n = sum(u)
    P = posets.SetPartitions(n)
    return Factorial(u) / Choose(u,mu) / Factorial(mu) * \
      sum( 1 / Choose(u, la) / Factorial(la) * len( [ (pi,sigma) for pi in P for sigma in P if \
      Type(u,pi) == la and Type(u,sigma) == mu and P.meet(pi, sigma) == P.bottom() ] ) * m[la] \
      for la in VectorPartitions(u))

## Given a vector partition mu, expand f[mu] in the monomial basis

def FtoM(mu):
    u = sum(mu)
    n = sum(u)
    P = posets.SetPartitions(n)
    return Factorial(u) / Choose(u,mu) / Bar(mu) * \
      sum( 1 / Choose(u, la) / Factorial(la) * \
        sum(Factorial(SPLambda(sigma, pi)) for pi in P for sigma in P if \
          Type(u,pi) == la and Type(u,sigma) == mu and pi in sigma.coarsenings()) \
        * m[la] for la in VectorPartitions(u))

