from sage.misc.bindable_class import BindableClass
from sage.combinat import vector_partition
from sage.combinat.vector_partition import VectorPartition, VectorPartitions
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.global_options import GlobalOptions
from sage.categories.hopf_algebras import HopfAlgebras
from sage.categories.realizations import Category_realization_of_parent
from sage.combinat.free_module import CombinatorialFreeModule


class MacMahonSymBasis_abstract(CombinatorialFreeModule, BindableClass):


    def __init__(self, alg, graded=True):

        
        def sorting_key(vector):
            vec = tuple(vector)
            total = sum(vec)
            return (total, tuple(p for p in vec))

        # Add category once implemented
        CombinatorialFreeModule.__init__(
            self, alg.base_ring(),
            VectorPartitions([0]),
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
    
    def a_realization(self):
        return self.M()
    _shorthands = ('M', 'P') #more to be added later

    class Powersum(MacMahonSymBasis_abstract):

        _prefix = 'P'
        _basis_name = 'Powersum'
        
        def product_on_basis(self, x, y):

            if not x:
                return self.monomial(y)
            if not y:
                return self.monomial(x)
            
            index = vector_partition
            z = index.VectorPartition(list(x) + list(y))

            return self.monomial(z)
        
        def coproduct_on_basis(self, x):
            return
        
    P = Powersum


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

            # Case 1: Already a vector partition
            if isinstance(p, VP):
                return self.monomial(p)

            # Case 2: Empty input is not supported yet
            if p == [] or p == ():
                raise ValueError("Empty vector partition index is not supported")

            # Case 3: User passed something like [[1,0],[0,1]]
            if hasattr(p, "__iter__") and all(hasattr(v, "__iter__") for v in p):
                try:
                    vp = VP(list(p))
                    return self.monomial(vp)
                except Exception:
                    pass

            # Case 4: Last attempt: try coercing p as a single vector
            try:
                vp = VP([p])
                return self.monomial(vp)
            except Exception:
                raise ValueError(f"Cannot convert {p} into a vector partition index")
