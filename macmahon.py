from sage.misc.bindable_class import BindableClass
from vector_partition import VectorPartition, VectorPartitions
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.categories.hopf_algebras import HopfAlgebras
from sage.categories.realizations import Category_realization_of_parent
from sage.combinat.free_module import CombinatorialFreeModule
from sage.all import factorial, prod, SetPartitions, QQ, Partition, posets
from sage.rings.integer_ring import ZZ


class MacMahonSymBasis_abstract(CombinatorialFreeModule, BindableClass):


    def __init__(self, alg, graded=True):

        def sorting_key(X):
            return(sum(sum(X)), X) #Idea is to sort lexicographically, first by weight of VP, if weight is equal, then by each individual entry in the VP

        CombinatorialFreeModule.__init__(
            self, alg.base_ring(),
            VectorPartitions(),
            category=MSymBases(alg, graded),
            sorting_key=sorting_key,
            bracket='', prefix=self._prefix
        )

    
    
       
    def _repr_term(self, vp):

        return "{}{}".format(self._prefix, vp)
    
    def _an_element_(self):
        return self([[1]]) + 2 * self([[1,2]])
    
    def some_elements(self):
        
        u = self.one()
        o = self([[1]])
        s = self.base_ring().an_element()
        return [u, o, self([[1, 2]]), o + self([[1], [2]]), u + s * o]
    
    def _coerce_map_from_(self, R):
        if isinstance(R, MacMahonSymBasis_abstract):
            if R.realization_of() == self.realization_of():
                return True
            if not self.base_ring().has_coerce_map_from(R.base_ring()):
                return False
            if self._basis_name == R._basis_name:  # The same basis
                def coerce_base_ring(self, x):
                    return self._from_dict(x.monomial_coefficients())
                return coerce_base_ring
            # Otherwise lift that basis up and then coerce over
            target = getattr(self.realization_of(), R._basis_name)()
            return self._coerce_map_via([target], R)
        return super()._coerce_map_from_(R)
    
    
class MacMahonSymmetricFunctions(UniqueRepresentation, Parent):
    
    def __init__(self, R):

        category = HopfAlgebras(R).Graded().Connected().Commutative()
        Parent.__init__(self, base=R, category=category.WithRealizations())

    def _repr_(self):

        return "MacMahon symmetric functions over {}".format(self.base_ring())

    
    def a_realization(self):

        return self.P()
        
    _shorthands = ('P', 'M', 'E', 'H')

    class Powersum(MacMahonSymBasis_abstract):

        _prefix = "P"
        _basis_name = "Powersum"

        def product_on_basis(self, x, y):
            z = VectorPartition(list(x) + list(y))

            return self[z]
        
    P = Powersum

    class Monomial(MacMahonSymBasis_abstract):

        _prefix = "M"
        _basis_name = "Monomial"

        def __init__(self, alg):
            MacMahonSymBasis_abstract.__init__(self, alg)
            
            p = self.realization_of().P()
            phi = self.module_morphism(self._M_to_P, codomain=p)
            phi.register_as_coercion()
            phi_inv = p.module_morphism(self._P_to_M, codomain=self)
            phi_inv.register_as_coercion()


        def _M_to_P(self, mu): ##error
            p = self.realization_of().P()
            u = self.sum_vp(mu)
            n = sum(u)
            P = posets.SetPartitions(n)
            Mu = P.moebius_function
            Ze = P.bottom()
            return 1 / self.Choose(u,mu) / self.Bars(mu) * \
            sum( abs(self.mobius_bottom_from_type(la)) * \
                sum( Mu(pi,sigma) / abs(Mu(Ze,sigma)) \
                for pi in P for sigma in P if self.Type(u,sigma) == la and self.Type(u,pi) == mu and sigma in pi.coarsenings()) \
            * p[la] for la in VectorPartitions(u))
        
        def _P_to_M(self, mu):
            m = self
            u = self.sum_vp(mu)
            n = sum(u)
            P = posets.SetPartitions(n)
            return self.Factorial(u) / self.Choose(u,mu) * \
            sum( 1 / self.Choose(u, la) / self.Factorial(la) * len([(pi,sigma) for pi in P for sigma in P if \
            self.Type(u,pi) == la and self.Type(u,sigma) == mu and pi in sigma.coarsenings()]) * m[la] \
            for la in VectorPartitions(u))

        def product_on_basis(self, x, y):
            p = self.realization_of().P()
            return self(p[x] * p[y])

    M = Monomial


    class Elementary(MacMahonSymBasis_abstract):

        _prefix = "E"
        _basis_name = "Elementary"

        def __init__(self, alg, graded=True):
            MacMahonSymBasis_abstract.__init__(self, alg)

            p = self.realization_of().P()
            phi = self.module_morphism(self._E_to_P, codomain=p)
            phi.register_as_coercion()



        def _E_to_P(self, mu): #erro
            p = self.realization_of().P()
            u = self.sum_vp(mu)
            n = sum(u)
            P = posets.SetPartitions(n)
            Mu = P.moebius_function
            Ze = P.bottom()
            return 1 / self.Choose(u,mu) / self.Factorial(mu) * \
            sum( abs(self.mobius_bottom_from_type(la)) * \
                sum( sigma.to_partition().sign() for pi in P for sigma in P if self.Type(u,sigma) == la and self.Type(u,pi) == mu and pi in sigma.coarsenings()) \
            * p[la] for la in VectorPartitions(u))
        


       
        def product_on_basis(self, x, y):
            z = VectorPartition(list(x) + list(y))
            return self[z]
        
        
    E = Elementary

    class Homogeneous(MacMahonSymBasis_abstract):

        _prefix = "H"
        _basis_name = "Homogeneous"

        def __init__(self, alg, graded=True):
            MacMahonSymBasis_abstract.__init__(self, alg, graded)

            p = self.realization_of().P()
            phi = self.module_morphism(self._H_to_P, codomain=p)
            phi.register_as_coercion()
            phi_inv = p.module_morphism(self._P_to_H, codomain=self)
            phi_inv.register_as_coercion()

        def _H_to_P(self, mu): #error
            p = self.realization_of().P()
            u = self.sum_vp(mu)
            n = sum(u)
            P = posets.SetPartitions(n)
            Mu = P.moebius_function
            Ze = P.bottom()
            return 1 / self.Choose(u,mu) / self.Factorial(mu) * \
            sum( abs(self.mobius_bottom_from_type(la)) * \
                len([(sigma, pi) for pi in P for sigma in P if self.Type(u,sigma) == la and self.Type(u,pi) == mu and pi in sigma.coarsenings()]) \
            * p[la] for la in VectorPartitions(u))
        
        def _P_to_H(self, mu):
            h = self
            u = self.sum_vp(mu)
            n = sum(u)
            P = posets.SetPartitions(n)
            Mu = P.moebius_function
            Ze = P.bottom()
            return self.Factorial(u) / self.Choose(u,mu) * \
            sum( 1 / self.Choose(u, la) / self.Bars(la) * \
                sum( Mu(pi,sigma) / abs(Mu(Ze, sigma)) \
                for pi in P for sigma in P if self.Type(u,pi) == la and self.Type(u,sigma) == mu and sigma in pi.coarsenings() ) \
            * h[la] for la in VectorPartitions(u))
 
        def product_on_basis(self, x, y):
            z = VectorPartition(list(x) + list(y))
            return self[z]
        
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
            '''
            Need a way to return M/P/E/H[something], 
            p must be a VectorPartition()


            '''
            #Case 1: p is already a vector partition
            if isinstance(p, VectorPartition):
                return self.monomial(p)
            
            #Case 2: p is not a vector partition, in which case we try and coerce into one, if cant then we raise an error
            try:
                vp = self._indices(p)
                
            except:
                raise ValueError("cannot convert {} into an index for {}".format(p, self))
            
            return self.monomial(vp)
        
        def one_basis(self):
            vp = self.basis().keys()
            return vp([])
        
        def degree_on_basis(self, vp):

            return sum(sum(vp))
        
        def is_field(self, proof=True):
  
            return False
        
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
            return VectorPartition([[1 if i in B else 0 for i in range(1, n+1)] for B in pi])

        def Type(self, u, pi):
            r = len(u)
            psum = [sum(u[:k]) for k in range(r+1)]
            lam = [[len([j for j in B if psum[i] < j <= psum[i+1]]) for i in range(r)]
                   for B in pi]
            return VectorPartition(lam)

        def Choose(self, u, mu):
            return self.Factorial([u]) / self.Factorial(mu) / self.Bars(mu)
        
        def sum_vp(self, mu):
   
            parts = list(mu)
            if not parts:
                return tuple()
            r = len(parts[0])
            return tuple(sum(part[i] for part in parts) for i in range(r))
        
        def mobius_bottom_from_type(self, la):
        
            out = ZZ(1)
            for v in la:
                k = sum(v)
                out *= (-1)**(k - 1) * factorial(k - 1)
            return out


        



            
