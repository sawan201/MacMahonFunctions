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
    
    def a_realization(self):
        return self.M()
    _shorthands = ('M', 'P') #more to be added later

    class Powersum(MacMahonSymBasis_abstract):

        _prefix = 'P'
        _basis_name = 'Powersum'
        
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

        def __mul__(self, other):
            """
            Multiplication of two *elements* in the monomial MacMahon basis
            is handled by CombinatorialFreeModule via product_on_basis.

            You almost never want to multiply the *parent* objects themselves,
            so we just delegate back to the generic machinery.

            This lets expressions like
                Msym.M()([vp1]) * Msym.M()([vp2])
            work as expected.
            """
            return MacMahonSymBasis_abstract.__mul__(self, other)

        # ---------- helper utilities ----------

        def _parts_from_vector_partition(self, vp):
            """
            Turn a VectorPartition into a list of nonzero integer tuples.
            The zero vector [[0,...,0]] is treated as the empty partition (the unit).
            """
            parts = [tuple(v) for v in vp]
            if not parts:
                return []

            # detect ambient dimension from first part
            k = len(parts[0])

            zero = (0,) * k
            # drop zero parts entirely (unit element)
            parts = [p for p in parts if p != zero]
            return parts

        def _make_key(self, parts):
            """
            Build a VectorPartition basis key from a list of integer tuples.
            If parts is empty, return the 'unit' key [[0,...,0]].
            """
            if not parts:
                # unit in degree zero: one copy of the zero vector in the right dimension
                # infer k from the ambient algebra (self.realization_of()._k if you have it)
                # here we guess k from the realization; if that is not available,
                # you can hard code or pass k in some other way.
                alg = self.realization_of()
                k = alg._k  # this is the usual attribute you were asking about earlier
                return VectorPartition([[0] * k])

            # VectorPartition will internally put the parts in its canonical order
            return VectorPartition(list(parts))

        # ---------- actual structural constants ----------

        def product_on_basis(self, x, y):
            

            

            parts_x = self._parts_from_vector_partition(x)
            parts_y = self._parts_from_vector_partition(y)

            Lx = len(parts_x)
            Ly = len(parts_y)

            # trivial cases
            if Lx == 0:
                # x is the unit: 1 * M[y] = M[y]
                return {y: self.base_ring().one()}
            if Ly == 0:
                # y is the unit: M[x] * 1 = M[x]
                return {x: self.base_ring().one()}

            result = defaultdict(self.base_ring().zero)

            # We encode which parts of y have been used in a bitmask.
            # parts_acc is a list of vector parts (tuples) we have built so far.
            def rec(ix, used_mask, parts_acc):
                if ix == Lx:
                    # all x parts processed; add in all unused y parts as they are
                    full_parts = list(parts_acc)
                    for j in range(Ly):
                        if not (used_mask & (1 << j)):
                            full_parts.append(parts_y[j])

                    key = self._make_key(full_parts)
                    result[key] += self.base_ring().one()
                    return

                # option 1: leave parts_x[ix] unmatched
                v = parts_x[ix]
                parts_acc.append(v)
                rec(ix + 1, used_mask, parts_acc)
                parts_acc.pop()

                # option 2: match parts_x[ix] with any currently unused part of y
                vx = parts_x[ix]
                for j in range(Ly):
                    if not (used_mask & (1 << j)):
                        vy = parts_y[j]
                        # coordinatewise sum in N^k
                        vsum = tuple(a + b for a, b in zip(vx, vy))
                        parts_acc.append(vsum)
                        rec(ix + 1, used_mask | (1 << j), parts_acc)
                        parts_acc.pop()

            rec(0, 0, [])

            return dict(result)


        
    


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
