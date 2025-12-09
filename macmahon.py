from sage.all import vector, cartesian_product_iterator
from sage.misc.bindable_class import BindableClass
from sage.combinat import vector_partition
from sage.combinat.vector_partition import VectorPartition, VectorPartitions
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.global_options import GlobalOptions
from sage.categories.hopf_algebras import HopfAlgebras
from sage.categories.realizations import Category_realization_of_parent
from sage.combinat.free_module import CombinatorialFreeModule
from itertools import product
from itertools import product as cartesian_product
from functools import reduce
from operator import mul
from collections import defaultdict
from sage.all import factorial, prod, SetPartitions, QQ, Partition, posets


class MacMahonSymBasis_abstract(CombinatorialFreeModule, BindableClass):


    def __init__(self, alg, graded=True):

        self._alg = alg


        
        def sorting_key(vector):
            vec = tuple(vector)
            total = sum(vec)
            return (total, tuple(p for p in vec))

        empty_key = VectorPartition([[0]])

        CombinatorialFreeModule.__init__(
            self, alg.base_ring(),
            [empty_key],
            category=MSymBases(alg, graded),
            sorting_key=sorting_key,
            bracket='', prefix=self._prefix
        )

        
    def Factorial(self, thing):
        return self._alg.Factorial(thing)

    def Bars(self, mu):
        return self._alg.Bars(mu)

    def Choose(self, u, mu):
        return self._alg.Choose(u, mu)

    def Type(self, u, pi):
        return self._alg.Type(u, pi)

    def SPLambda(self, sigma, pi):
        return self._alg.SPLambda(sigma, pi)

       
    def _repr_term(self, vp):

        return "{}{}".format(self._prefix, vp)
    
    
class MacMahonSymmetricFunctions(UniqueRepresentation, Parent):
    def __init__(self, R):

        category = HopfAlgebras(R).Graded().Connected().Commutative()
        if R.is_zero():
            category = category.Commutative() #is it connected?

        Parent.__init__(self, base=R, category=category.WithRealizations())

    def _repr_(self):
        return "MacMahon symmetric functions over {}".format(self.base_ring())
    
    def Factorial(self, thing):
        try:
            return factorial(thing)
        except:
            return prod(self.Factorial(x) for x in thing)

        
    def Bars(self, mu):
        Mu = list(mu)
        Done = []
        output = 1
        for part in Mu:
            if not part in Done:
                Done.append(part)
                output = output * self.Factorial(Mu.count(part))
        return output
    
    def SetPToVecP(self, pi):
        n = pi.base_set_cardinality()
        return VectorPartition([[1 if i in B else 0 for i in range(1,n+1)] for B in pi])
    
    def Type(self, u, pi):
        # Allow u to be either an integer (total size) or an iterable of block sizes
        if hasattr(u, "__iter__"):
            u_list = list(u)
            r = len(u_list)
            psum = [0]
            for k in range(r):
                psum.append(psum[-1] + u_list[k])
        else:
            # treat u as a single block of size u
            r = 1
            psum = [0, u]

        ell = len(pi)
        n = sum(len(B) for B in pi)
        lam = [
            [
                len([j for j in B if psum[i] < j <= psum[i + 1]])
                for i in range(r)
            ]
            for B in pi
        ]
        return VectorPartition(lam)

    
    def Choose(self, u, mu):
        return self.Factorial([u]) / self.Factorial(mu) / self.Bars(mu)
    
    def LiftM(self, mu):
        m = MacMahonSymmetricFunctions(QQ).Monomial()
        u = sum(mu)
        return 1/self.Choose(u,mu)/self.Bars(mu)*sum(m[self.SetPToVecP(pi)] for pi in SetPartitions(sum(u)) if self.Type(u,pi)==mu)
    def LiftP(self, mu):
        p = MacMahonSymmetricFunctions(QQ).Powersum()
        u = sum(mu)
        return 1/self.Choose(u,mu)*sum(p[self.SetPToVecP(pi)] for pi in SetPartitions(sum(u)) if self.Type(u,pi)==mu)
    def LiftH(self, mu):
        h = MacMahonSymmetricFunctions(QQ).Homogeneous()
        u = sum(mu)
        return 1/self.Choose(u,mu)/self.Factorial(mu)*sum(h[self.SetPToVecP(pi)] for pi in SetPartitions(sum(u)) if self.Type(u,pi)==mu)
    def LiftE(self, mu):
        e = MacMahonSymmetricFunctions(QQ).Elementary()
        u = sum(mu)
        return 1/self.Choose(u,mu)/self.Factorial(mu)*sum(e[self.SetPToVecP(pi)] for pi in SetPartitions(sum(u)) if self.Type(u,pi)==mu)
    
    def SPLambda(self, sigma, pi):
        L = [0]*len(pi)
        for sblock in sigma:
            for i in range(len(pi)):
                if sblock.issubset(pi[i]):
                    L[i] = L[i]+1
        L.sort()
        L.reverse()
        return Partition(L)
    
    def MHProduct(self, pi, sigma):
        return 0 if pi != sigma else 1


    def HMProduct(self, pi, sigma):
        return self.MHProduct(pi, sigma)


    def PPProduct(self, pi,sigma):
        if pi != sigma:
            return 0
        else:
            n = pi.base_set_cardinality()
            P = posets.SetPartitions(n)
            mu = P.moebius_function
            return 1 / mu(P.bottom(),pi)
        
    def EPProduct(self, pi, sigma):
        return sigma.to_partition().sign() if pi in sigma.coarsenings() else 0

    def PEProduct(self, pi, sigma):
        return self.EPProduct(sigma, pi)

    def HPProduct(self, pi, sigma):
        return 1 if pi in sigma.coarsenings() else 0

    def PHProduct(self, pi, sigma):
        return self.HPProduct(sigma, pi)     
    
    def EEProduct(self, pi, sigma):
        n = pi.base_set_cardinality()
        if not n == sigma.base_set_cardinality():
            return 0
        else:
            xi = posets.SetPartitions(n).meet(sigma, pi)
            return prod(self.Factorial(j) for j in xi.to_partition())
        
    def EHProduct(self, pi, sigma):
        n = pi.base_set_cardinality()
        if not n == sigma.base_set_cardinality():
            return 0
        else:
            P = SetPartitions(n)
            return 1 if P.meet(sigma, pi) == P.bottom() else 0
        
    HEProduct = EHProduct

    def MMProduct(self, pi, sigma):
        n = pi.base_set_cardinality()
        if not n == sigma.base_set_cardinality():
            return 0
        else:
            P = posets.SetPartitions(n)
            mu = posets.SetPartitions(n).moebius_function
            return sum( mu(pi,tau) * mu(sigma,tau) / abs(mu(P.bottom(),tau)) for tau in pi.coarsenings() if tau in sigma.coarsenings())

    def EMProduct(self, pi, sigma):
        n = pi.base_set_cardinality()
        if not n == sigma.base_set_cardinality():
            return 0
        elif not pi in sigma.coarsenings():
            return 0
        else:
            return sigma.to_partition().sign() * prod(self.Factorial(i) for i in self.SPLambda(sigma, pi))
        
    HHProduct = EEProduct

    def MPProduct(self, pi, sigma):
        if not sigma in pi.coarsenings():  ## i.e., if zeta(pi, sigma) = 0
            return 0
        else:
            n = pi.base_set_cardinality()
            mu = posets.SetPartitions(n).moebius_function
            P = posets.SetPartitions(n)
            return mu(pi,sigma) / abs(mu(P.bottom(),sigma))


    def PMProduct(self, sigma, pi):
        return self.MPProduct(pi, sigma)
    
    def FMProduct(self, pi, sigma):
        n = pi.base_set_cardinality()
        if not n == sigma.base_set_cardinality():
            return 0
        else:
            P = posets.SetPartitions(n)
            mu = P.moebius_function
            return sum(abs(mu(pi,tau))*mu(sigma, tau)/abs(mu(P.bottom(),tau)) \
            for tau in P.join(pi, sigma).coarsenings())
        
    def MFProduct(self, pi, sigma):
        return self.FMProduct(sigma, pi)
    
    def FFProduct(self, pi, sigma):
        n = pi.base_set_cardinality()
        if not n == sigma.base_set_cardinality():
            return 0
        else:
            P = posets.SetPartitions(n)
            mu = P.moebius_function
            return pi.to_partition().sign() * sigma.to_partition().sign() * \
            sum(mu(pi,tau)*mu(sigma, tau)/abs(mu(P.bottom(),tau)) for tau in P.join(pi, sigma).coarsenings())


    def FHProduct(self, pi, sigma):
        n = pi.base_set_cardinality()
        if not n == sigma.base_set_cardinality():
            return 0
        elif not sigma in pi.coarsenings():
            return 0
        else:
            return prod(self.Factorial(j) for j in self.SPLambda(pi, sigma))
        
    def HFProduct(self, pi, sigma):
        return self.FHProduct(sigma, pi)
    
    def FPProduct(self, pi, sigma):
        n = pi.base_set_cardinality()
        if not n == sigma.base_set_cardinality():
            return 0
        elif not sigma in pi.coarsenings():
            return 0
        else:
            P = posets.SetPartitions(n)
            mu = P.moebius_function
            return pi.to_partition().sign() * sigma.to_partition().sign() * mu(pi, sigma) / abs(mu(P.bottom(),sigma))
        
    def PFProduct(self, pi, sigma):
        return self.FPProduct(sigma, pi)
    
    def FEProduct(self, pi, sigma):
        if pi != sigma:
            return 0
        return pi.to_partition().sign()


    def EFProduct(self, pi, sigma):
        return self.FEProduct(sigma, pi)


    class Powersum(MacMahonSymBasis_abstract):

        _prefix = 'P'
        _basis_name = 'Powersum'


        def __init__(self, alg, graded=True):
            MacMahonSymBasis_abstract.__init__(self, alg, graded)

        def _PtoM(self, mu):
            parent = self.realization_of()
            m = parent.Monomial()
            u = sum(mu)
            n = u
            P = posets.SetPartitions(n)
            return self.Factorial(u) / self.Choose(u,mu) * \
            sum( 1 / self.Choose(u, la) / self.Factorial(la) * len([(pi,sigma) for pi in P for sigma in P if \
            self.Type(u,pi) == la and self.Type(u,sigma) == mu and pi in sigma.coarsenings()]) * m[la] \
            for la in VectorPartitions([u]))
        
        def _PtoH(self, mu):
            parent = self.realization_of()
            h = parent.Homogeneous()
            u = sum(mu)
            n = sum(u)
            P = posets.SetPartitions(n)
            Mu = P.moebius_function
            Ze = P.bottom()
            return self.Factorial(u) / self.Choose(u,mu) * \
            sum( 1 / self.Choose(u, la) / self.Bars(la) * \
                sum( Mu(pi,sigma) / abs(Mu(Ze,sigma)) \
                for pi in P for sigma in P if self.Type(u,pi) == la and self.Type(u,sigma) == mu and sigma in pi.coarsenings() ) \
            * h[la] for la in VectorPartitions([u]))
        
        
        def product_on_basis(self, x, y):
            # Turn VectorPartition into list of components
            lam_list = list(x)
            mu_list  = list(y)

            # Componentwise multiset union of parts
            merged = []
            for part_lam, part_mu in zip(lam_list, mu_list):
                merged_part = tuple(sorted(part_lam + part_mu, reverse=True))
                merged.append(merged_part)

            nu = VectorPartition(merged)

            
            return self.monomial(nu)
        
    P = Powersum



    class Monomial(MacMahonSymBasis_abstract):

        _prefix = "M"
        _basis_name = "Monomial"

        def __init__(self, alg, graded=True):
            MacMahonSymBasis_abstract.__init__(self, alg, graded)

        def _MtoH(self, mu):
            parent = self.realization_of()
            h = parent.Homogeneous()
            u = sum(mu)
            n = sum(u)
            P = posets.SetPartitions(n)
            Mu = P.moebius_function
            Ze = P.bottom()
            return self.Factorial(u) / self.Choose(u,mu) / self.Bars(mu) * \
            sum( 1 / self.Choose(u, la) / self.Bars(la) * \
                sum( \
                    sum( Mu(pi,tau)*Mu(sigma,tau)/Mu(Ze,tau) \
                    for tau in P.join(pi, sigma).coarsenings() ) \
                for pi in P for sigma in P if self.Type(u,pi) == la and self.Type(u,sigma) == mu) \
            * h[la] for la in VectorPartitions(u))
        
        def product_on_basis(self, x, y):
            return

    M = Monomial

    class Elementary(MacMahonSymBasis_abstract):

        _prefix = "E"
        _basis_name = "Elementary"

        def __init__(self, alg, graded=True):
            MacMahonSymBasis_abstract.__init__(self, alg, graded)

        def _EtoM(self, mu):
            parent = self.realization_of()
            m = parent.Monomial()
            u = sum(mu)
            n = sum(u)
            P = posets.SetPartitions(n)
            return self.Factorial(u) / self.Choose(u,mu) / self.Factorial(mu) * \
            sum( 1 / self.Choose(u, la) / self.Factorial(la) * len( [ (pi,sigma) for pi in P for sigma in P if \
            self.Type(u,pi) == la and self.Type(u,sigma) == mu and P.meet(pi, sigma) == P.bottom() ] ) * m[la] \
            for la in VectorPartitions(u))
        def _EtoH(self, mu):
            parent = self.realization_of()
            h = parent.Homogeneous()
            u = sum(mu)
            n = sum(u)
            P = posets.SetPartitions(n)
            Mu = P.moebius_function
            Ze = P.bottom()
            return self.Factorial(u) / self.Choose(u,mu) / self.Factorial(mu) * \
            sum( 1 / self.Choose(u, la) / self.Bars(la) * \
                sum( pi.to_partition().sign() * self.SPLambda(pi, sigma) \
                for pi in P for sigma in P if self.Type(u,pi) == la and self.Type(u,sigma) == mu and sigma in pi.coarsenings() ) \
            * h[la] for la in VectorPartitions(u))

        def product_on_basis(self, x, y):
            # Turn VectorPartition into list of components
            lam_list = list(x)
            mu_list  = list(y)

            # Componentwise multiset union of parts
            merged = []
            for part_lam, part_mu in zip(lam_list, mu_list):
                merged_part = tuple(sorted(part_lam + part_mu, reverse=True))
                merged.append(merged_part)

            nu = VectorPartition(merged)

            
            return self.monomial(nu)
        
    E = Elementary

    class Homogeneous(MacMahonSymBasis_abstract):

        _prefix = "H"
        _basis_name = "Homogeneous"

        def __init__(self, alg, graded=True):
            MacMahonSymBasis_abstract.__init__(self, alg, graded)

        def _HtoM(self, mu):
            parent = self.realization_of()
            m = parent.Monomial()
            u = sum(mu)
            n = sum(u)
            P = posets.SetPartitions(n)
            return self.Factorial(u) / self.Choose(u,mu) / self.Factorial(mu) * \
            sum( 1 / self.Choose(u, la) / self.Factorial(la) * sum(self.Factorial(P.meet(sigma,pi).to_partition()) \
            for sigma in P for pi in P if self.Type(u,pi) == la and self.Type(u,sigma) == mu) * m[la] \
            for la in VectorPartitions(u))
        
        def product_on_basis(self, x, y):
            # Turn VectorPartition into list of components
            lam_list = list(x)
            mu_list  = list(y)

            # Componentwise multiset union of parts
            merged = []
            for part_lam, part_mu in zip(lam_list, mu_list):
                merged_part = tuple(sorted(part_lam + part_mu, reverse=True))
                merged.append(merged_part)

            nu = VectorPartition(merged)

            
            return self.monomial(nu)
    H = Homogeneous

        
    


class MSymBases(Category_realization_of_parent):

    def __init__(self, base, graded):
        self._graded = graded
        Category_realization_of_parent.__init__(self, base)

    def _repr_(self):
        if self._graded:
            type_str = "graded"
        else:
            type_str = "filtered"
        return "Category of {} bases of {}".format(type_str, self.base())
    
    def super_categories(self):
        R = self.base().base_ring()
        cat = HopfAlgebras(R).Graded().WithBasis()
        if self._graded:
            cat = cat.Graded()
        else:
            cat = cat.Filtered()

        return [self.base().Realizations(),
                HopfAlgebras(R).Graded().Realizations(),
                cat.Connected()]
    
    class ParentMethods:
        def _repr_(self):
            return "{} in the {} basis".format(self.realization_of(), self._basis_name)

        def __getitem__(self, p):

            VP = vector_partition.VectorPartition

            
            if isinstance(p, VP):
                return self.monomial(p)

            
            if p == [] or p == ():
                raise ValueError("Empty vector partition index is not supported")

           
            if hasattr(p, "__iter__") and all(hasattr(v, "__iter__") for v in p):
                try:
                    vp = VP(list(p))
                    return self.monomial(vp)
                except Exception:
                    pass

            
            try:
                vp = VP([p])
                return self.monomial(vp)
            except Exception:
                raise ValueError(f"Cannot convert {p} into a vector partition index")
