from sage.all import *
from sage.combinat.vector_partition import VectorPartition
from MacMahon import MacMahonSymmetricFunctions

def _make_P():
    """
    Helper to construct the MacMahon powersum realization.
    
    """
    MSym = MacMahonSymmetricFunctions(QQ)
    # Directly construct the Powersum realization
    P = MacMahonSymmetricFunctions.Powersum(MSym)
    return P


def test_getitem_and_product():
    P = _make_P()
    VP = VectorPartition

    # Basic vector partitions (dim 2)
    vp_x = VP([[1, 0], [0, 1]])
    vp_y = VP([[2, 0]])
    vp_z = VP([[0, 1]])
    vp_xy_concat = VP([[1, 0], [0, 1], [2, 0]])

    # __getitem__ tests

    # Case 1: already a VectorPartition
    assert P[vp_x] == P.monomial(vp_x)

    # Case 3: list of vectors
    assert P[[[1, 0], [0, 1]]] == P.monomial(vp_x)
    assert P[[[2, 0]]] == P.monomial(vp_y)

    # Case 4: single vector, coerced as one part
    vp_single = VP([(1, 0)])          # match the way __getitem__ builds it
    assert P[(1, 0)] == P.monomial(vp_single)


    # Case 5: list of two vectors as separate parts
    vp_two = VP([[1, 0], [2, 3]])
    assert P[[[1, 0], [2, 3]]] == P.monomial(vp_two)

    # Case 6: something invalid should raise ValueError
    try:
        P[object()]
    except ValueError:
        pass
    else:
        raise AssertionError("Expected ValueError from P[object()]")

    # product_on_basis tests

    # Product on basis indices is concatenation of parts
    prod_xy = P.product_on_basis(vp_x, vp_y)
    assert prod_xy == P.monomial(vp_xy_concat)

    # Symmetry of product_on_basis (P basis is commutative)
    prod_yx = P.product_on_basis(vp_y, vp_x)
    assert prod_xy == prod_yx

    # Tests on algebra elements

    Ex = P.monomial(vp_x)
    Ey = P.monomial(vp_y)
    Ez = P.monomial(vp_z)

    # Multiplication should agree with product_on_basis
    assert Ex * Ey == P.monomial(vp_xy_concat)

    # Associativity on elements
    left = (Ex * Ey) * Ez
    right = Ex * (Ey * Ez)
    assert left == right

    print("All MacMahonSymmetricFunctions tests passed")



if __name__ == "__main__":
    test_getitem_and_product()
