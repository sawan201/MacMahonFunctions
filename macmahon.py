
from sage.all import *

class MacMahonAlgebra:
    """
    A minimal MacMahon algebra with k alphabets, each labeled by a chosen basis name.

    Parameters
    ----------
    Sym : SymmetricFunctions(R) instance (only used to extract the base ring)
    k   : positive int, number of alphabets
    basis : str or sequence of str; 
    """
    def __init__(self, Sym, k=2, basis='powersum'):
        if not isinstance(k, int) or k <= 0:
            raise ValueError("k must be a positive integer")
        self._Sym = Sym
        self._k = k

        if isinstance(basis, (list, tuple)):
            if len(basis) != k:
                raise ValueError("if basis is a list/tuple it must have length k")
            self._bases = list(basis)
        else:
            self._bases = [str(basis)] * k

        self._prefix = f"Mac{k}"

    def base_ring(self):
        return self._Sym.base_ring()

    def k(self):
        return self._k

    def bases(self):
        return tuple(self._bases)

    def monomial(self, tuple_of_parts):

        key = self._canonical_key(tuple_of_parts)
        return MacMahonElement(self, {key: self.base_ring().one()})

    def _from_dict(self, d):

        new_d = {}
        R = self.base_ring()
        for key, c in d.items():
            ckey = self._canonical_key(key)
            coeff = R(c)
            if coeff != R.zero():
                new_d[ckey] = new_d.get(ckey, R.zero()) + coeff
        return MacMahonElement(self, new_d)

    def _canonical_key(self, tuple_of_parts):
        """
        Validate and canonicalize a k-tuple of partitions to a tuple of Partition objects.
        """
        if not isinstance(tuple_of_parts, (list, tuple)) or len(tuple_of_parts) != self._k:
            raise ValueError(f"key must be a tuple/list of length k={self._k}")
        parts = []
        for p in tuple_of_parts:
            parts.append(Partition(list(p)))  # Partition validates nonnegative, weakly decreasing etc.
        return tuple(parts)


class MacMahonElement:
    """
    Minimal element for the MacMahon algebra.

    Internal representation:
        _coeffs: dict { (Partition, ..., Partition) : coeff in base ring }
    """
    def __init__(self, parent, d=None):
        self._parent = parent
        self._coeffs = {}
        if d:
            R = self.parent().base_ring()
            for key, c in d.items():
                ckey = self.parent()._canonical_key(key)
                coeff = R(c)
                if coeff != R.zero():
                    self._coeffs[ckey] = self._coeffs.get(ckey, R.zero()) + coeff

    def parent(self):
        return self._parent

    # ----- arithmetic: +, -, *  -----

    def __add__(self, other):
        if not isinstance(other, MacMahonElement) or other.parent() is not self.parent():
            raise TypeError("addition requires elements from the same MacMahonAlgebra parent")
        R = self.parent().base_ring()
        res = dict(self._coeffs)
        for k, c in other._coeffs.items():
            newc = res.get(k, R.zero()) + c
            if newc != R.zero():
                res[k] = newc
            elif k in res:
                del res[k]
        return MacMahonElement(self.parent(), res)

    __radd__ = __add__

    def __neg__(self):
        R = self.parent().base_ring()
        return MacMahonElement(self.parent(), {k: -c for k, c in self._coeffs.items()})

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):

        R = self.parent().base_ring()
        try:
            s = R(other)
        except Exception as e:
            raise TypeError("only scalar multiplication by elements of the base ring is supported") from e
        if s == R.zero():
            return MacMahonElement(self.parent(), {})
        if s == R.one():
            return MacMahonElement(self.parent(), dict(self._coeffs))
        return MacMahonElement(self.parent(), {k: s * c for k, c in self._coeffs.items()})

    def __rmul__(self, other):
        return self.__mul__(other)



    def expand(self, *args, **kwargs):
        raise NotImplementedError("expand is not implemented yet")



    def __repr__(self):
        if not self._coeffs:
            return "0"
        terms = []
        # deterministic order by key
        for k in sorted(self._coeffs.keys()):
            terms.append(f"{self._coeffs[k]}*M{list(k)}")
        return " + ".join(terms)
