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


class MacMahonSymBasis_abstract(CombinatorialFreeModule, BindableClass):


    def __init__(self, alg, graded=True):

        
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
    


    class Powersum(MacMahonSymBasis_abstract):

        _prefix = 'P'
        _basis_name = 'Powersum'

        def _P_to_M(self, Mu, La):
            co = 0
            ell = len(La)
            m = len(Mu)
            r = len(Mu[0])
            for k in cartesian_product_iterator( [list(range(m)) for i in range(ell)] ):
                vsum = {i:vector(r*[0]) for i in range(m)}
                for j in range(ell):
                    vsum[k[j]] += vector(La[j])
                if all(vsum[i] == vector(Mu[i]) for i in range(m)):
                    co += 1
            return co
        
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

            # Return a single monomial p_nu
            return self.monomial(nu)
            
        
        def coproduct_on_basis(self, x):
            return
        
    P = Powersum



    class Monomial(MacMahonSymBasis_abstract):

        _prefix = "M"
        _basis_name = "Monomial"

        def product_on_basis(self, x, y):
            return
    M = Monomial

    class Elementary(MacMahonSymBasis_abstract):

        _prefix = "E"
        _basis_name = "Elementary"

        def product_on_basis(self, x, y):
            return
        
    E = Elementary

    class Homogeneous(MacMahonSymBasis_abstract):

        _prefix = "H"
        _basis_name = "Homogeneous"

        def product_on_basis(self, x, y):
            return
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
