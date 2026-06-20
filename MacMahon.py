r"""
MacMahon symmetric functions


This file implements MacMahon symmetric functions over a commutative base
ring.  The basis elements are indexed by vector partitions.

The implemented bases are:

- ``P`` -- powersum basis;
- ``M`` -- monomial basis;
- ``E`` -- elementary basis;
- ``H`` -- homogeneous basis;
- ``F`` -- forgotten basis.

The implementation includes:

- change-of-basis maps between ``P``, ``M``, ``E``, ``H``, and ``F``;
- multiplication in each basis;
- coproduct;
- antipode;
- counit;
- Hall inner product.

The transition maps are computed degree-by-degree using one cached pass over
comparable pairs in the set-partition lattice.  For a fixed multidegree ``u``,
set partitions ``f`` and ``c`` with ``f`` refining ``c`` are bucketed by their
Young-subgroup type.  This avoids repeatedly constructing
``posets.SetPartitions(n)`` and repeatedly calling Sage's Möbius-function
routine.

The powersum basis is the native basis for the Hopf structure:

.. MATH::

    \Delta(P_\Lambda)
    =
    \sum_{J \subseteq [\ell(\Lambda)]}
    P_{\Lambda|J} \otimes P_{\Lambda|J^c},

and

.. MATH::

    S(P_\Lambda) = (-1)^{\ell(\Lambda)}P_\Lambda.

The other bases obtain coproducts and antipodes by coercion through the
powersum basis.

The Hall inner product is defined by declaring the homogeneous and monomial
bases to be dual:

.. MATH::

    \langle H_\lambda, M_\mu \rangle = \delta_{\lambda,\mu}.

Equivalently, the powersum basis is orthogonal and satisfies

.. MATH::

    \langle P_\lambda, P_\lambda \rangle
    =
    \frac{\operatorname{Bars}(\lambda)\operatorname{Factorial}(\lambda)}
         {|\mu(\hat{0},\lambda)|}.

At one alphabet, this reduces to the usual classical value ``z_lambda``.

REFERENCES:

- M. Rosas, *MacMahon symmetric functions, the partition lattice,
  and Young subgroups*, Journal of Combinatorial Theory, Series A 96,
  326--340, 2001.
- M. Rosas, G.-C. Rota, and J. Stein, *A combinatorial overview of the
  Hopf algebra of MacMahon symmetric functions*, Annals of Combinatorics 6,
  195--207, 2002.
- R. Stanley, *A symmetric function generalization of the chromatic polynomial
  of a graph*, Advances in Mathematics 111, 166--194, 1995.

EXAMPLES:

Construct the algebra and its bases::


    sage: A = MacMahonSymmetricFunctions(QQ)
    sage: P = A.P()
    sage: M = A.M()
    sage: E = A.E()
    sage: H = A.H()
    sage: F = A.F()
    sage: A
    MacMahon symmetric functions over the Rational Field

Construct basis elements::

    sage: lam = VectorPartition([[1,1]])
    sage: P[lam]
    P[[1, 1]]
    sage: M[lam]
    M[[1, 1]]

Check coercions between the monomial and powersum bases::

    sage: M(P(M[lam])) == M[lam]
    True
    sage: P(M(P[lam])) == P[lam]
    True

Check the Hall inner product::

    sage: lam2 = VectorPartition([[2]])
    sage: lam11 = VectorPartition([[1], [1]])
    sage: H[lam2].scalar(M[lam2])
    1
    sage: H[lam2].scalar(M[lam11])
    0
    sage: E[lam2].scalar(F[lam2])
    1
    sage: E[lam2].scalar(F[lam11])
    0

Check the powersum coproduct::

    sage: lam = VectorPartition([[1,1]])
    sage: P[lam].coproduct()
    P[] # P[[1, 1]] + P[[1, 1]] # P[]

Check the antipode::

    sage: P[VectorPartition([[1,1]])].antipode()
    -P[[1, 1]]
    sage: P[VectorPartition([[1,0], [0,1]])].antipode()
    P[[0, 1], [1, 0]]

TESTS:

Basic round-trip tests::

    sage: A = MacMahonSymmetricFunctions(QQ)
    sage: P, M, E, H, F = A.P(), A.M(), A.E(), A.H(), A.F()
    sage: for u in [(1,), (2,), (1,1), (2,1)]:
    ....:     for lam in VectorPartitions(list(u)):
    ....:         assert M(P(M[lam])) == M[lam]
    ....:         assert P(M(P[lam])) == P[lam]
    ....:         assert E(P(E[lam])) == E[lam]
    ....:         assert P(E(P[lam])) == P[lam]
    ....:         assert H(P(H[lam])) == H[lam]
    ....:         assert P(H(P[lam])) == P[lam]
    ....:         assert F(M(F[lam])) == F[lam]
    ....:         assert M(F(M[lam])) == M[lam]

Hall inner product tests::

    sage: A = MacMahonSymmetricFunctions(QQ)
    sage: P, M, E, H, F = A.P(), A.M(), A.E(), A.H(), A.F()
    sage: lam2 = VectorPartition([[2]])
    sage: lam11 = VectorPartition([[1], [1]])
    sage: H[lam2].scalar(M[lam2]) == 1
    True
    sage: H[lam2].scalar(M[lam11]) == 0
    True
    sage: E[lam2].scalar(F[lam2]) == 1
    True
    sage: E[lam2].scalar(F[lam11]) == 0
    True
    sage: P[lam2].scalar(P[lam2]) == 2
    True
    sage: P[lam11].scalar(P[lam11]) == 2
    True

Hopf-structure tests::

    sage: A = MacMahonSymmetricFunctions(QQ)
    sage: P, M, E, H, F = A.P(), A.M(), A.E(), A.H(), A.F()
    sage: lam = VectorPartition([[1,1]])
    sage: empty = VectorPartition([])
    sage: P[lam].coproduct() == tensor([P[empty], P[lam]]) + tensor([P[lam], P[empty]])
    True
    sage: for B in [P, M, E, H, F]:
    ....:     x = B[VectorPartition([[2,1]])]
    ....:     assert x.antipode().antipode() == x
    ....:     _ = x.coproduct()

Coercion-route tests modeled on Sage's basis-conversion doctests::

    sage: A = MacMahonSymmetricFunctions(QQ)
    sage: P, M, E, H, F = A.P(), A.M(), A.E(), A.H(), A.F()
    sage: lam = VectorPartition([[1,1]])
    sage: M.has_coerce_map_from(P)
    True
    sage: P.has_coerce_map_from(M)
    True
    sage: P.has_coerce_map_from(E)
    True
    sage: P.has_coerce_map_from(H)
    True
    sage: F.has_coerce_map_from(M)
    True
    sage: M.has_coerce_map_from(F)
    True
    sage: M(E[lam]) == M(P(E[lam]))
    True
    sage: H(P(H[lam])) == H[lam]
    True
    sage: F(M(P[lam])) == F(M[lam])
    True

Multiplicative sanity checks::

    sage: A = MacMahonSymmetricFunctions(QQ)
    sage: P, M, E, H, F = A.P(), A.M(), A.E(), A.H(), A.F()
    sage: a = VectorPartition([[1,1]])
    sage: b = VectorPartition([[1,2]])
    sage: P[a] * P[b] == P[VectorPartition([[1,1], [1,2]])]
    True
    sage: E[a] * E[b] == E[VectorPartition([[1,1], [1,2]])]
    True
    sage: H[a] * H[b] == H[VectorPartition([[1,1], [1,2]])]
    True
    sage: P(M[a] * M[b]) == P(M[b] * M[a])
    True
    sage: M(F[a] * F[b]) == M(F[b] * F[a])
    True
"""

from sage.misc.bindable_class import BindableClass
from vector_partition_ahmad import VectorPartition, VectorPartitions
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.categories.hopf_algebras import HopfAlgebras
from sage.categories.realizations import Category_realization_of_parent
from sage.categories.tensor import tensor
from sage.combinat.free_module import CombinatorialFreeModule
from sage.all import factorial, prod, SetPartition, QQ, Partition
from sage.rings.integer_ring import ZZ

# The transition engine does its linear algebra in ``fractions.Fraction``
# (exact and lightweight) and only coerces into Sage's ``QQ`` when the final
# module element is built; ``lru_cache`` memoizes the per-degree work.
from fractions import Fraction as _Fr
from functools import lru_cache
from itertools import combinations




@lru_cache(maxsize=None)
def _set_partitions(n):
    r"""
    Return all set partitions of `\{1, 2, \ldots, n\}`.

    Each set partition is canonicalized as a sorted tuple of sorted
    tuples, so that the result is hashable and can serve as a cache key.
    The case ``n == 0`` returns the single partition of the empty set.

    This is the ground set over which the transition engine walks the
    partition lattice; see :func:`_degree_engine`.  The result is cached,
    so the (expensive) enumeration happens at most once per ``n``.

    INPUT:

    - ``n`` -- a nonnegative integer

    EXAMPLES::

        sage: _set_partitions(0)
        ((),)
        sage: _set_partitions(2)
        (((1, 2),), ((1,), (2,)))

    The number of set partitions of an ``n``-element set is the ``n``-th
    Bell number::

        sage: len(_set_partitions(3))
        5
        sage: len(_set_partitions(4))
        15
    """
    if n == 0:
        return (tuple(),)
    elts = list(range(1, n + 1))
    out = []

    def helper(i, blocks):
        # Backtracking enumeration: place each element ``elts[i]`` into
        # every existing block in turn, and also into a fresh singleton
        # block, recursing on the remaining elements.  Every set partition
        # is produced exactly once.
        if i == len(elts):
            # All elements placed: store the partition in canonical form
            # (each block sorted, then the list of blocks sorted).
            out.append(tuple(sorted(tuple(sorted(b)) for b in blocks)))
            return
        x = elts[i]
        for k in range(len(blocks)):
            blocks[k].append(x)            # add x to the existing block k
            helper(i + 1, blocks)
            blocks[k].pop()                # undo, to try the next choice
        blocks.append([x])                 # start a new block {x}
        helper(i + 1, blocks)
        blocks.pop()                       # undo

    helper(0, [])
    return tuple(out)


@lru_cache(maxsize=None)
def _is_refinement(a, b):
    r"""
    Return whether the set partition ``a`` refines the set partition ``b``.

    ``a`` refines ``b`` (written `a \leq b` in the partition lattice) when
    every block of ``a`` is contained in some block of ``b``.

    INPUT:

    - ``a``, ``b`` -- set partitions in the canonical form produced by
      :func:`_set_partitions`

    EXAMPLES::

        sage: _is_refinement(((1,), (2,)), ((1, 2),))
        True
        sage: _is_refinement(((1, 2),), ((1,), (2,)))
        False
    """
    bsets = [frozenset(B) for B in b]
    for A in a:
        Aset = frozenset(A)
        # ``a`` fails to refine ``b`` as soon as one of its blocks is not
        # contained in any single block of ``b``.
        if not any(Aset <= B for B in bsets):
            return False
    return True


@lru_cache(maxsize=None)
def _refinements(c):
    r"""
    Return every set partition ``f`` that refines ``c``.

    These are exactly the partitions ``f`` with `f \leq c` in the partition
    lattice, i.e. the elements of the lower interval `[\hat{0}, c]`.  The
    transition engine iterates over these when accumulating the Mobius and
    counting data for the lower interval below each ``c``.

    INPUT:

    - ``c`` -- a set partition in canonical form

    EXAMPLES::

        sage: _refinements(((1, 2),))
        (((1, 2),), ((1,), (2,)))
        sage: _refinements(((1,), (2,)))
        (((1,), (2,)),)
    """
    n = sum(len(b) for b in c)
    return tuple(p for p in _set_partitions(n) if _is_refinement(p, c))


def _moebius_interval(f, c):
    r"""
    Return the partition-lattice Mobius value `\mu(f, c)`.

    Here ``f`` refines ``c``, so the pair spans an interval of the partition
    lattice.  Such an interval factors as a product of smaller partition
    lattices -- one factor `\Pi_k` for each block `B` of ``c``, where ``k``
    is the number of blocks of ``f`` landing inside `B`.  On `\Pi_k` one has
    `\mu(\hat{0}, \hat{1}) = (-1)^{k-1} (k-1)!`, and Mobius values multiply
    across a product, which yields the closed form computed here (avoiding a
    call to Sage's generic lattice Mobius routine).

    INPUT:

    - ``f``, ``c`` -- set partitions in canonical form with ``f`` refining
      ``c``

    EXAMPLES:

    On a rank-one interval the value is `-1`::

        sage: _moebius_interval(((1,), (2,)), ((1, 2),))
        -1

    From the bottom to the top of `\Pi_3` the value is
    `(-1)^{2} \cdot 2! = 2`, and on a trivial interval it is `1`::

        sage: _moebius_interval(((1,), (2,), (3,)), ((1, 2, 3),))
        2
        sage: _moebius_interval(((1, 2),), ((1, 2),))
        1
    """
    if f == c:
        return 1
    fsets = [frozenset(A) for A in f]
    val = 1
    for B in c:
        Bset = frozenset(B)
        # ``k`` = number of blocks of ``f`` sitting inside this block ``B``
        # of ``c``.  That sub-interval is isomorphic to Pi_k, contributing a
        # factor (-1)^(k-1) (k-1)! to the Mobius value.
        k = sum(1 for A in fsets if A <= Bset)
        val *= (-1) ** (k - 1) * factorial(k - 1)
    return val


def _type_key(u, pi):
    r"""
    Return the *type* of the set partition ``pi`` with respect to ``u``.

    Fix the composition ``u = (u_0, u_1, \ldots, u_{r-1})`` and split the
    ground set `[n]` (with `n = \sum u`) into ``r`` consecutive intervals of
    sizes `u_0, u_1, \ldots`; think of interval ``i`` as the elements of
    color (alphabet) ``i``.  For each block `B` of ``pi`` the *profile* is
    the vector counting how many elements of `B` carry each color.  The type
    is the multiset of these profiles, which is exactly a vector partition
    of ``u``.

    This is the Doubilet--Rosas type map from set partitions to vector
    partitions; it is the bucketing used to fold the lattice walk in
    :func:`_degree_engine` down to a per-type transition matrix.  The result
    is returned as a canonical key (the sorted tuple of profile tuples).

    INPUT:

    - ``u`` -- a composition (tuple of nonnegative integers)
    - ``pi`` -- a set partition of `[\sum u]` in canonical form

    EXAMPLES:

    With ``u = (2, 1)`` the ground set `[3]` splits into the color intervals
    `\{1, 2\}` and `\{3\}`.  The single block `\{1, 2, 3\}` has two elements
    of the first color and one of the second, so its profile is `(2, 1)`::

        sage: _type_key((2, 1), ((1, 2, 3),))
        ((2, 1),)

    Two singleton blocks of `[2]`, colored by ``u = (1, 1)``, give the two
    unit profiles; merging them into one block gives the profile `(1, 1)`::

        sage: _type_key((1, 1), ((1,), (2,)))
        ((0, 1), (1, 0))
        sage: _type_key((1, 1), ((1, 2),))
        ((1, 1),)
    """
    r = len(u)
    # psum[i] = u_0 + ... + u_{i-1}; the color-i interval is the set of
    # ground-set elements j with psum[i] < j <= psum[i+1].
    psum = [sum(u[:k]) for k in range(r + 1)]
    # For each block B, count how many of its elements land in each color
    # interval -- that count vector is the block's profile.
    prof = [tuple(sum(1 for j in B if psum[i] < j <= psum[i + 1]) for i in range(r))
            for B in pi]
    # The type is the multiset of profiles; sort for a canonical key.
    return tuple(sorted(prof))


# ---- elementary quantities on a vector-partition key (tuple of tuples) ----
#
# Throughout, a vector partition ``Lambda`` is represented by its canonical
# key: a tuple of integer tuples (its parts).  The "weight" of a part is the
# sum of its coordinates.  These small multiplicative quantities are the
# building blocks of the change-of-basis prefactors and the Hall norm.

def _factorial_key(key):
    r"""
    Return `\operatorname{Factorial}(\Lambda)
    = \prod_{v \in \Lambda} \prod_i v_i!`.

    The product runs over every part ``v`` of the vector partition and every
    coordinate of each part.  At one alphabet it reduces to the classical
    `\prod_i \lambda_i!`.

    INPUT:

    - ``key`` -- a vector partition as a tuple of tuples

    EXAMPLES::

        sage: _factorial_key(((2, 1),))
        2
        sage: _factorial_key(((3,),))
        6
        sage: _factorial_key(((1,), (1,)))
        1
    """
    out = 1
    for v in key:
        for x in v:
            out *= factorial(x)
    return out


def _bars_key(key):
    r"""
    Return `\operatorname{Bars}(\Lambda) = \prod_w m_w(\Lambda)!`.

    The product is over the distinct parts ``w`` of the vector partition,
    where `m_w(\Lambda)` is the multiplicity of ``w``.  This is the order of
    the subgroup permuting equal parts; it appears in the change-of-basis
    prefactors and in the power-sum Hall norm.  At one alphabet it is the
    `\prod_i m_i(\lambda)!` factor of `z_\lambda`.

    INPUT:

    - ``key`` -- a vector partition as a tuple of tuples

    EXAMPLES::

        sage: _bars_key(((1,), (2,)))
        1
        sage: _bars_key(((1,), (1,)))
        2
        sage: _bars_key(((1,), (1,), (1,)))
        6
    """
    out = 1
    seen = []
    for part in key:
        # Multiply in (multiplicity of this part)! exactly once per distinct
        # part, so equal parts are not double-counted.
        if part not in seen:
            seen.append(part)
            out *= factorial(key.count(part))
    return out


def _choose(u, key):
    r"""
    Return `\operatorname{Factorial}(u) / \operatorname{Factorial}(\Lambda)
    / \operatorname{Bars}(\Lambda)` as an exact fraction.

    This multinomial-type quantity is the number of set partitions whose
    type is ``Lambda`` (equivalently, of colored arrangements of weight
    ``u`` collapsing to ``Lambda``).  It is the common normalizing prefactor
    in the monomial and homogeneous transition matrices; see
    :func:`_degree_engine`.

    INPUT:

    - ``u`` -- the ambient multidegree (tuple of nonnegative integers)
    - ``key`` -- a vector partition of ``u`` as a tuple of tuples

    EXAMPLES::

        sage: _choose((1, 1), ((1, 1),)) == 1
        True
        sage: _choose((3,), ((2,), (1,))) == 3
        True
    """
    num = 1
    for x in u:
        num *= factorial(x)
    return _Fr(num, 1) / _factorial_key(key) / _bars_key(key)


def _abs_mu_bottom_key(key):
    r"""
    Return `|\mu(\hat{0}, \sigma)|` for any set partition `\sigma` of this type.

    For a set partition with block sizes `b_1, b_2, \ldots`, the partition
    lattice gives `\mu(\hat{0}, \sigma) = \prod_j (-1)^{b_j - 1} (b_j - 1)!`,
    so its absolute value is `\prod_j (b_j - 1)!`.  This depends only on the
    multiset of block sizes, hence only on the type ``key`` (a part's block
    size being its coordinate sum).  It is the denominator that turns the
    Mobius sum into the monomial-to-powersum coefficients.

    INPUT:

    - ``key`` -- a vector partition as a tuple of tuples

    EXAMPLES::

        sage: _abs_mu_bottom_key(((2,),))
        1
        sage: _abs_mu_bottom_key(((3,),))
        2
        sage: _abs_mu_bottom_key(((1,), (1,)))
        1
    """
    out = 1
    for v in key:
        out *= factorial(sum(v) - 1)
    return out


def _sign_key(key):
    r"""
    Return the `\omega`-involution sign of a vector partition.

    The sign is `(-1)^{(\#\text{parts of even coordinate-sum})}`,
    equivalently `(-1)^{n - \ell(\Lambda)}` where `n` is the total weight and
    `\ell(\Lambda)` is the number of parts.  It implements the twist relating
    the elementary and homogeneous bases (and likewise the forgotten and
    monomial bases); at one alphabet it is the classical `\omega` sign on
    power sums.

    INPUT:

    - ``key`` -- a vector partition as a tuple of tuples

    EXAMPLES::

        sage: _sign_key(((2,),))
        -1
        sage: _sign_key(((1,),))
        1
        sage: _sign_key(((1,), (1,)))
        1
    """
    num = sum(1 for v in key if sum(v) % 2 == 0)
    return -1 if (num % 2) else 1



# ----------------------------- linear algebra ------------------------------

def _frac_inverse(M):
    r"""
    Return the exact inverse of a square matrix over the rationals.

    The inverse is computed by Gauss--Jordan elimination on the augmented
    matrix ``[M | I]`` using :class:`fractions.Fraction` arithmetic, so the
    result is exact.  The transition engine uses this to invert each "to
    powersum" matrix and read off the corresponding "from powersum" map.

    INPUT:

    - ``M`` -- an invertible square matrix (list of lists) with rational
      entries

    EXAMPLES::

        sage: from fractions import Fraction
        sage: I2 = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)]]
        sage: Mf = [[Fraction(1), Fraction(2)], [Fraction(3), Fraction(4)]]
        sage: _matmul(Mf, _frac_inverse(Mf)) == I2
        True
    """
    n = len(M)
    # Build the augmented matrix A = [ M | I ] with exact entries.
    A = [[_Fr(M[i][j]) for j in range(n)] +
         [_Fr(1 if k == i else 0) for k in range(n)] for i in range(n)]
    for col in range(n):
        # Pick a nonzero pivot in this column and bring it onto the diagonal.
        piv = next(r for r in range(col, n) if A[r][col] != 0)
        A[col], A[piv] = A[piv], A[col]
        # Normalize the pivot row so the pivot entry becomes 1.
        pv = A[col][col]
        A[col] = [x / pv for x in A[col]]
        # Clear this column out of every other row.
        for r in range(n):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                A[r] = [A[r][k] - f * A[col][k] for k in range(2 * n)]
    # After full reduction the left half is I and the right half is M^{-1}.
    return [[A[i][j + n] for j in range(n)] for i in range(n)]


def _matmul(A, B):
    r"""
    Return the exact matrix product ``A * B``.

    The matrices used in the transition engine have entries in
    :class:`fractions.Fraction`.  Keeping this helper separate makes the
    degree engine easier to read and avoids coercing through Sage rings
    until the final module element is constructed.

    INPUT:

    - ``A``, ``B`` -- matrices (lists of lists) of compatible shapes

    EXAMPLES::

        sage: _matmul([[1, 2], [3, 4]], [[0, 1], [1, 0]])
        [[2, 1], [4, 3]]
    """
    n, k, m = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(m)]
            for i in range(n)]


# ------------------------- the cached degree engine ------------------------

@lru_cache(maxsize=None)
def _degree_engine(u):
    r"""
    Build every change-of-basis matrix in a fixed multidegree ``u``.

    For a degree ``u`` (a tuple of nonnegative integers), return a pair
    ``(order, T)`` where:

    - ``order`` is the tuple of vector-partition keys indexing this degree,
      in a fixed, sorted order;
    - ``T`` is a dictionary sending a pair of basis letters ``(X, Y)`` to the
      exact transition matrix expressing the ``X`` basis in terms of the
      ``Y`` basis.  Rows are indexed by the source key in ``order`` and
      columns by the target key, so ``T[(X, Y)][i][j]`` is the coefficient of
      ``Y[order[j]]`` in the expansion of ``X[order[i]]``.

    The whole table is produced from a single pass over the partition lattice
    of `[n]`, `n = \sum u`.  Walking the lattice once and bucketing every
    comparable pair ``f <= c`` by the *types* (vector partitions) of ``f``
    and ``c`` collapses the lattice computation down to the ``N \times N``
    arrays ``mob`` and ``cnt`` indexed by types.  The four forward maps to the
    powersum basis are read off these two arrays, and the reverse maps are
    obtained by exact matrix inversion.  The result is cached, so the lattice
    walk happens at most once per degree.

    The two fundamental forward maps are the monomial-to-powersum map

    .. MATH::

        M_\Lambda
        = \frac{1}{\binom{u}{\Lambda} \operatorname{Bars}(\Lambda)}
          \sum_{\sigma} |\mu(\hat 0, \sigma)| \,
          \mu(\tau, \sigma) \, P_{\operatorname{type}(\sigma)} ,

    summed over the lattice (with ``tau`` of type ``Lambda``), and the
    homogeneous-to-powersum map, which uses a plain count of refinements in
    place of the Mobius weight.  The remaining bases are twists or composites:
    ``E`` is the sign twist of ``H``, and ``F`` is the sign twist of ``M``
    (applied in the powersum basis).

    INPUT:

    - ``u`` -- a tuple of nonnegative integers (the multidegree)

    EXAMPLES:

    A degree with a single vector partition gives ``1 \times 1`` matrices::

        sage: from fractions import Fraction
        sage: order, T = _degree_engine((1,))
        sage: len(order)
        1
        sage: T[('M', 'M')] == [[Fraction(1)]]
        True

    In degree ``(2,)`` there are two vector partitions, and the
    monomial-to-powersum matrix is upper triangular -- matching the classical
    identities `M_{(1,1)} = \tfrac12 P_{(1,1)} - \tfrac12 P_{(2)}` and
    `M_{(2)} = P_{(2)}`::

        sage: order, T = _degree_engine((2,))
        sage: len(order)
        2
        sage: T[('M', 'P')] == [[Fraction(1, 2), Fraction(-1, 2)],
        ....:                   [Fraction(0), Fraction(1)]]
        True
    """
    n = sum(u)

    # Index set for this degree: the vector partitions of u, each turned into
    # its canonical tuple-of-tuples key, sorted into a fixed order so that the
    # rows/columns of every matrix below agree.
    order = tuple(sorted(
        tuple(sorted(tuple(int(x) for x in part) for part in vp))
        for vp in VectorPartitions(list(u))
    ))
    pos = {k: i for i, k in enumerate(order)}   # key -> its row/column index
    N = len(order)

    # Precompute the type (a vector-partition key) of every set partition of
    # [n]; this is the only place the colored structure of [n] enters.
    typ = {p: _type_key(u, p) for p in _set_partitions(n)}

    # A single walk over the partition lattice.  For each comparable pair
    # f <= c we add to two N x N arrays, indexed by (type of f, type of c):
    #   mob -- the Mobius value mu(f, c), pre-divided by |mu(0, c)|; this
    #          feeds the monomial -> powersum map.
    #   cnt -- a plain count of such f; this feeds the homogeneous -> powersum
    #          map (and, after a sign twist, the elementary one).
    mob = [[_Fr(0)] * N for _ in range(N)]
    cnt = [[0] * N for _ in range(N)]
    for c in _set_partitions(n):
        ci = pos[typ[c]]                                  # column = type of c
        inv_absmu_c = _Fr(1, _abs_mu_bottom_key(typ[c]))  # 1 / |mu(0, c)|
        for f in _refinements(c):
            fi = pos[typ[f]]                              # row = type of f
            mob[fi][ci] += _Fr(_moebius_interval(f, c)) * inv_absmu_c
            cnt[fi][ci] += 1

    sign = [_sign_key(k) for k in order]   # omega sign per index key

    # Assemble the two forward maps to the powersum basis, attaching the
    # multinomial/Bars/Factorial prefactors that the type-bucketing factored
    # out of the lattice sum.
    MP = [[_Fr(0)] * N for _ in range(N)]   # M -> P
    HP = [[_Fr(0)] * N for _ in range(N)]   # H -> P
    for i, mu in enumerate(order):
        ch = _choose(u, mu)          # Factorial(u)/Factorial(mu)/Bars(mu)
        bars = _bars_key(mu)
        fct = _factorial_key(mu)
        for j, la in enumerate(order):
            absla = _abs_mu_bottom_key(la)
            # M -> P : source mu is the finer type, target la the coarser;
            #          the lattice summand is the Mobius weight.
            MP[i][j] = _Fr(1) / ch / bars * absla * mob[i][j]
            # H -> P : source mu is the coarser type, target la the finer
            #          (hence the transposed access cnt[j][i]); the summand is
            #          a plain count of refinements.
            HP[i][j] = _Fr(1) / ch / fct * absla * cnt[j][i]

    # E -> P is H -> P with the omega sign applied in the powersum basis.
    EP = [[HP[i][j] * sign[j] for j in range(N)] for i in range(N)]

    # Reverse maps (from the powersum basis) by exact inversion.
    PM = _frac_inverse(MP)
    PH = _frac_inverse(HP)
    PE = _frac_inverse(EP)

    # F is the forgotten basis: omega applied to M.  Realize the sign action
    # in the powersum basis (M -> P, twist by sign, then P -> M) to get F -> M,
    # and invert for M -> F.
    MPdiag = [[MP[i][j] * sign[j] for j in range(N)] for i in range(N)]
    FM = _matmul(MPdiag, PM)
    MF = _frac_inverse(FM)

    I = [[_Fr(1 if i == j else 0) for j in range(N)] for i in range(N)]

    # Collect, for each basis, its matrix into the powersum basis ("toP") and
    # out of it ("frP").  P is the hub, so its own maps are the identity.
    toP = {'P': I, 'M': MP, 'E': EP, 'H': HP, 'F': _matmul(FM, MP)}
    frP = {'P': I, 'M': PM, 'E': PE, 'H': PH, 'F': _matmul(PM, MF)}

    # Every basis-to-basis transition factors through the powersum hub:
    #   X -> Y  =  (X -> P) (P -> Y).
    T = {}
    for X in 'PMEHF':
        for Y in 'PMEHF':
            T[(X, Y)] = _matmul(toP[X], frP[Y])
    return order, T




class MacMahonSymBasis_abstract(CombinatorialFreeModule, BindableClass):
    r"""
    Abstract base class for bases of MacMahon symmetric functions.

    This class contains the shared Sage machinery for the five implemented
    bases.  Each concrete basis defines a printed prefix, a basis name, and a
    one-letter basis code.

    EXAMPLES::

        sage: A = MacMahonSymmetricFunctions(QQ)
        sage: M = A.M()
        sage: M
        MacMahon symmetric functions over the Rational Field in the Monomial basis
        sage: M.an_element()
        M[[1]] + 2*M[[1, 2]]

    TESTS::

        sage: A = MacMahonSymmetricFunctions(QQ)
        sage: TestSuite(A.M()).run()
    """

    def __init__(self, alg, graded=True):
        r"""
        Initialize a realization of the MacMahon symmetric functions.

        INPUT:

        - ``alg`` -- the parent algebra whose basis this object realizes;
        - ``graded`` -- whether Sage should place the basis in the graded
          basis category.

        EXAMPLES::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: M = A.M()
            sage: M.one()
            M[]

        TESTS::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: TestSuite(A.P()).run()
        """

        def sorting_key(X):
            # Sort first by total degree, then lexicographically by the vector
            # partition.  This keeps printed expansions stable across bases.
            return (sum(sum(part) for part in X), list(X))

        CombinatorialFreeModule.__init__(
            self, alg.base_ring(),
            VectorPartitions(),
            category=MSymBases(alg, graded),
            sorting_key=sorting_key,
            bracket='', prefix=self._prefix
        )

    def _repr_term(self, vp):
        r"""
        Return the printed representation of one basis term.

        EXAMPLES::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: A.M()[VectorPartition([[1,1]])]
            M[[1, 1]]
        """
        return "{}{}".format(self._prefix, vp)

    def _an_element_(self):
        r"""
        Return a small sample element used by Sage's test suite.

        EXAMPLES::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: A.E().an_element()
            E[[1]] + 2*E[[1, 2]]
        """
        return self([[1]]) + 2 * self([[1, 2]])

    def _coerce_map_from_(self, R):
        r"""
        Decide whether ``R`` canonically coerces into ``self``.

        Direct maps are registered for the adjacent conversions implemented by
        each basis.  All other same-parent, compatible-base-ring conversions
        are routed through the powersum basis, following Sage's standard
        realization pattern.

        EXAMPLES::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: M, E = A.M(), A.E()
            sage: M.has_coerce_map_from(E)
            True
            sage: A.P().has_coerce_map_from(E)
            True
        """
        if isinstance(R, MacMahonSymBasis_abstract):
            # Only coerce between bases of the same MacMahon algebra, and only
            # when the base rings are compatible.
            if R.realization_of() != self.realization_of():
                return None
            if not self.base_ring().has_coerce_map_from(R.base_ring()):
                return None
            if self._basis_name == R._basis_name:
                return True
            # Any other same-parent conversion is routed through the powersum
            # basis, which is where the registered adjacent maps all meet.
            P = self.realization_of().P()
            return self._coerce_map_via([P], R)
        return super()._coerce_map_from_(R)

    # -- helper shared by every basis: expand one basis element in another ----

    def _convert_on_basis(self, mu, target_letter):
        r"""
        Convert one basis element to another basis.

        INPUT:

        - ``mu`` -- a vector partition indexing a basis element of ``self``;
        - ``target_letter`` -- one of ``'P'``, ``'M'``, ``'E'``, ``'H'``,
          ``'F'``.

        OUTPUT:

        The image of the basis element indexed by ``mu`` in the target basis.

        The transition matrix is read from the cached degree-local transition
        engine.

        EXAMPLES::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: M = A.M()
            sage: P = A.P()
            sage: lam = VectorPartition([[1,1]])
            sage: M._convert_on_basis(lam, 'P') == P(M[lam])
            True

        TESTS::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: M = A.M()
            sage: P = A.P()
            sage: lam = VectorPartition([[2,1]])
            sage: M(P(M[lam])) == M[lam]
            True
        """
        alg = self.realization_of()
        # Find the multidegree of mu and pull the cached transition table for
        # that degree; pick the matrix for (this basis -> target basis).
        u = _usum(mu)
        order, T = _degree_engine(u)
        mat = T[(self._basis_name_letter, target_letter)]
        key_to_elt = _key_to_element_map(u)        # canonical key -> VectorPartition
        src_key = _vp_to_key(mu)
        row = order.index(src_key)                 # the row for the source mu
        target = alg.realization_letter(target_letter)
        # Read this row of the matrix: each nonzero entry is the coefficient of
        # a target basis element, converted from an exact Fraction to a Sage
        # rational.
        coeffs = {}
        for j, la_key in enumerate(order):
            c = mat[row][j]
            if c != 0:
                coeffs[key_to_elt[la_key]] = QQ(c.numerator) / QQ(c.denominator)
        return target._from_dict(coeffs, coerce=True)


# -- small index helpers (module level so the engine and bases share them) ---

def _usum(mu):
    r"""
    Return the ambient multidegree of a vector partition.

    This is the element-wise sum of the parts of ``mu``, i.e. the vector
    ``u`` such that ``mu`` is a vector partition of ``u``.  It is what selects
    the degree-local transition engine for ``mu``.  The empty partition maps
    to the empty tuple.

    INPUT:

    - ``mu`` -- a vector partition (an iterable of equal-length integer
      vectors)

    EXAMPLES::

        sage: _usum(VectorPartition([[1, 1], [2, 0]])) == (3, 1)
        True
        sage: _usum(VectorPartition([]))
        ()
    """
    parts = [list(p) for p in mu]
    if not parts:
        return ()
    r = len(parts[0])
    return tuple(sum(int(p[i]) for p in parts) for i in range(r))


def _vp_to_key(mu):
    r"""
    Return the canonical tuple key for the vector partition ``mu``.

    Vector partitions are Sage elements, but the transition engine works with
    immutable tuple-of-tuples keys (parts sorted, then the list of parts
    sorted) so that the data can be hashed and cached.  This function produces
    that key.

    INPUT:

    - ``mu`` -- a vector partition

    EXAMPLES::

        sage: _vp_to_key(VectorPartition([[2, 0], [1, 1]])) == ((1, 1), (2, 0))
        True
    """
    return tuple(sorted(tuple(int(x) for x in part) for part in mu))


def _zmac(vp):
    r"""
    Return the power-sum Hall self-pairing of a vector partition.

    This is the diagonal entry of the Hall form in the power-sum basis,

    .. MATH::

        \langle P_\Lambda, P_\Lambda \rangle
        = \frac{\operatorname{Bars}(\Lambda)\,\operatorname{Factorial}(\Lambda)}
               {|\mu(\hat{0}, \Lambda)|} ,

    returned as a rational.  The power sums are orthogonal, so off-diagonal
    pairings vanish and this single value determines the form on each
    power-sum vector.  At one alphabet it is the classical `z_\lambda`.

    INPUT:

    - ``vp`` -- a vector partition

    EXAMPLES::

        sage: _zmac(VectorPartition([[2]])) == 2
        True
        sage: _zmac(VectorPartition([[1], [1]])) == 2
        True
    """
    key = _vp_to_key(vp)
    return QQ(_bars_key(key) * _factorial_key(key)) / QQ(_abs_mu_bottom_key(key))


@lru_cache(maxsize=None)
def _key_to_element_map(u):
    r"""
    Return the map from canonical keys to vector partitions in degree ``u``.

    The transition engine produces coefficients indexed by canonical keys
    (tuples of tuples); this cached dictionary turns each such key back into
    the corresponding :class:`VectorPartition`, which is the index the module
    elements actually use.

    INPUT:

    - ``u`` -- a tuple of nonnegative integers (the multidegree)

    EXAMPLES::

        sage: m = _key_to_element_map((2,))
        sage: m[((2,),)] == VectorPartition([[2]])
        True
        sage: m[((1,), (1,))] == VectorPartition([[1], [1]])
        True
    """
    out = {}
    for vp in VectorPartitions(list(u)):
        out[tuple(sorted(tuple(int(x) for x in part) for part in vp))] = \
            VectorPartition([list(part) for part in vp]) if list(vp) else VectorPartition([])
    return out


class MSymBases(Category_realization_of_parent):
    r"""
    The category of bases of MacMahon symmetric functions.

    This category supplies all basis parents with common parent and element
    methods: indexing, degree, counit, fallback coproduct/antipode, and the
    Hall inner product.
    """

    def __init__(self, base, graded):
        """Store the grading flag and initialize the realization category."""
        self._graded = graded
        Category_realization_of_parent.__init__(self, base)

    def _repr_(self):
        """Return a readable name for this category."""
        type_str = "graded" if self._graded else "filtered"
        return "Category of {} bases of {}".format(type_str, self.base())

    def super_categories(self):
        """Return the Sage super-categories satisfied by every basis."""
        R = self.base().base_ring()
        return [
            self.base().Realizations(),
            HopfAlgebras(R).Graded().WithBasis().Connected()
        ]

    class ParentMethods:
        """Methods shared by the parent object of each concrete basis."""

        def _repr_(self):
            """Return the printed name of this basis parent."""
            return "{} in the {} basis".format(self.realization_of(), self._basis_name)

        def __getitem__(self, p):
            r"""
            Return the basis element indexed by ``p``.

            The index may already be a ``VectorPartition`` or may be data that
            ``VectorPartitions`` can coerce to a vector partition.

            EXAMPLES::

                sage: A = MacMahonSymmetricFunctions(QQ)
                sage: A.P()[VectorPartition([[1,1]])]
                P[[1, 1]]
                sage: A.P()(VectorPartition([[1,1]])) == A.P()[VectorPartition([[1,1]])]
                True
            """
            if isinstance(p, VectorPartition):
                return self.monomial(p)
            try:
                vp = self._indices(p)
            except Exception:
                raise ValueError("cannot convert {} into an index for {}".format(p, self))
            return self.monomial(vp)

        def one_basis(self):
            r"""
            Return the basis index of the multiplicative identity.

            EXAMPLES::

                sage: A = MacMahonSymmetricFunctions(QQ)
                sage: A.M().one_basis()
                []
            """
            vp = self.basis().keys()
            return vp([])

        def degree_on_basis(self, vp):
            r"""
            Return the total degree of a vector-partition basis index.

            EXAMPLES::

                sage: A = MacMahonSymmetricFunctions(QQ)
                sage: A.P().degree_on_basis(VectorPartition([[2,1], [0,1]]))
                4
            """
            # Total weight of the vector partition, computed from its ambient
            # multidegree.  This is safe for the empty vector partition.
            return sum(_usum(vp))

        def is_field(self, proof=True):
            """Return ``False``; these basis parents are not fields."""
            return False

        # ---- Hopf structure -------------------------------------------------
        # The natural (native) basis for the coproduct and antipode is the
        # Powersum basis, where both have closed forms (see the Powersum class).
        # For every other basis they are obtained by coercion through Powersum.

        def counit_on_basis(self, vp):
            r"""
            Return the counit on a basis element.

            The Hopf algebra is connected graded, so the counit is one on the
            empty vector partition and zero on every positive-degree basis
            element.

            EXAMPLES::

                sage: A = MacMahonSymmetricFunctions(QQ)
                sage: P = A.P()
                sage: P.one().counit()
                1
                sage: P[VectorPartition([[1]])].counit()
                0
            """
            R = self.base_ring()
            return R.one() if len(list(vp)) == 0 else R.zero()

        def coproduct_by_coercion(self, x):
            r"""
            Compute the coproduct by converting through the powersum basis.

            EXAMPLES::

                sage: A = MacMahonSymmetricFunctions(QQ)
                sage: M = A.M()
                sage: x = M[VectorPartition([[1,1]])]
                sage: x.coproduct().parent() is M.tensor_square()
                True
            """
            # Delta(x) is computed in Powersum, where it is closed-form, then
            # each tensor factor is coerced back into ``self``.
            P = self.realization_of().Powersum()
            cp = P(x).coproduct()
            T = self.tensor_square()
            return T.sum(c * tensor([self(P.monomial(kl)), self(P.monomial(kr))])
                         for (kl, kr), c in cp.monomial_coefficients(copy=False).items())

        def antipode_by_coercion(self, x):
            r"""
            Compute the antipode by converting through the powersum basis.

            EXAMPLES::

                sage: A = MacMahonSymmetricFunctions(QQ)
                sage: H = A.H()
                sage: x = H[VectorPartition([[2,1]])]
                sage: x.antipode().antipode() == x
                True
            """
            P = self.realization_of().Powersum()
            return self(P(x).antipode())

        # ---- Hall inner product --------------------------------------------

        def hall_inner_product(self, x, y):
            """The Hall (Doubilet--Rosas) inner product <x, y>.

            Defined by declaring the monomial and homogeneous bases to be dual,
            <H[la], M[mu]> = delta_{la,mu}; equivalently the power sums are
            orthogonal with <P[la], P[la]> = Bars(la)*Factorial(la)/|mu(0,la)|
            (which is the classical z_lambda at one alphabet).  The forms agree;
            this is evaluated in the power-sum basis, where the Gram matrix is
            diagonal."""
            P = self.realization_of().Powersum()
            xc = P(x).monomial_coefficients(copy=False)
            yc = P(y).monomial_coefficients(copy=False)
            R = self.base_ring()
            total = R.zero()
            # Power sums are orthogonal, so only matching indices contribute,
            # each weighted by the diagonal Hall norm _zmac.  Loop over the
            # smaller support for efficiency.
            if len(yc) < len(xc):
                xc, yc = yc, xc
            for vp, a in xc.items():
                b = yc.get(vp)
                if b is not None:
                    total += a * b * R(_zmac(vp))
            return total


    class ElementMethods:
        """Methods shared by elements of all MacMahon bases."""

        def scalar(self, other):
            """The Hall inner product <self, other>; alias hall_inner_product."""
            return self.parent().hall_inner_product(self, other)

        hall_inner_product = scalar


class MacMahonSymmetricFunctions(UniqueRepresentation, Parent):
    r"""
    The algebra of MacMahon symmetric functions.

    INPUT:

    - ``R`` -- a commutative base ring.

    This parent represents the graded connected Hopf algebra of MacMahon
    symmetric functions over ``R``.  The implemented realizations are the
    powersum, monomial, elementary, homogeneous, and forgotten bases.

    EXAMPLES::

        sage: A = MacMahonSymmetricFunctions(QQ)
        sage: A
        MacMahon symmetric functions over the Rational Field
        sage: A.P()
        MacMahon symmetric functions over the Rational Field in the Powersum basis
        sage: A.M()
        MacMahon symmetric functions over the Rational Field in the Monomial basis

    TESTS::

        sage: A = MacMahonSymmetricFunctions(QQ)
        sage: A.a_realization() is A.P()
        True
    """

    def __init__(self, R):
        r"""
        Initialize the parent over the base ring ``R``.

        EXAMPLES::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: A.base_ring()
            Rational Field
        """
        category = HopfAlgebras(R).Graded().Connected().Commutative()
        Parent.__init__(self, base=R, category=category.WithRealizations())

    def _repr_(self):
        r"""
        Return the printed representation of this parent.

        EXAMPLES::

            sage: MacMahonSymmetricFunctions(QQ)
            MacMahon symmetric functions over the Rational Field
        """
        return "MacMahon symmetric functions over the {}".format(self.base_ring())

    def a_realization(self):
        r"""
        Return the default realization.

        The powersum basis is the default because the Hopf structure is native
        in that basis.

        EXAMPLES::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: A.a_realization() is A.P()
            True
        """
        return self.P()

    def realization_letter(self, letter):
        """Return the realization (basis) for a single-letter code in PMEHF."""
        return {'P': self.P, 'M': self.M, 'E': self.E,
                'H': self.H, 'F': self.F}[letter]()

    _shorthands = ('P', 'M', 'E', 'H', 'F')

    # -- bases ---------------------------------------------------------------

    class Powersum(MacMahonSymBasis_abstract):
        r"""
        The powersum basis of MacMahon symmetric functions.

        The basis element indexed by a vector partition ``Lambda`` is denoted
        ``P[Lambda]``.  Multiplication is concatenation of vector partitions.

        The powersum basis is the native basis for the coproduct and antipode.

        EXAMPLES::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: P = A.P()
            sage: lam = VectorPartition([[1,1]])
            sage: P[lam]
            P[[1, 1]]
            sage: P[lam].coproduct()
            P[] # P[[1, 1]] + P[[1, 1]] # P[]
            sage: P[lam].antipode()
            -P[[1, 1]]

        TESTS::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: P = A.P()
            sage: lam = VectorPartition([[1,0], [0,1]])
            sage: P[lam].antipode().antipode() == P[lam]
            True
        """
        _prefix = "P"
        _basis_name = "Powersum"
        _basis_name_letter = "P"

        def product_on_basis(self, x, y):
            r"""
            Multiply two powersum basis elements.

            In the powersum basis, multiplication concatenates vector-partition
            parts.

            EXAMPLES::

                sage: A = MacMahonSymmetricFunctions(QQ)
                sage: P = A.P()
                sage: P[VectorPartition([[1]])] * P[VectorPartition([[2]])]
                P[[1], [2]]
            """
            return self[VectorPartition(list(x) + list(y))]

        def coproduct_on_basis(self, vp):
            r"""Coproduct on the power-sum basis (Martin--Trist, Prop. 3.11):

                Delta(P[Lambda]) = sum_{J subseteq [l(Lambda)]}
                                       P[Lambda|J] (x) P[Lambda|complement of J],

            i.e. distribute the parts of the vector partition over the two tensor
            factors in every possible way (positions distinct, so repeated parts
            are handled with multiplicity).  At one alphabet this is the classical
            power-sum coproduct."""
            keys = self._indices
            parts = list(vp)
            ell = len(parts)
            T = self.tensor_square()
            terms = []
            # Distribute the parts of Lambda over the two tensor factors in
            # every possible way: choose a subset J of part-positions for the
            # left factor and send the rest to the right.  Positions (not
            # values) are chosen, so repeated parts are counted with the
            # correct multiplicity.
            for k in range(ell + 1):
                for J in combinations(range(ell), k):
                    Js = set(J)
                    left = [list(parts[i]) for i in range(ell) if i in Js]
                    right = [list(parts[i]) for i in range(ell) if i not in Js]
                    terms.append(tensor([self.monomial(keys(left)),
                                         self.monomial(keys(right))]))
            return T.sum(terms)

        def antipode_on_basis(self, vp):
            r"""
            Return the antipode of a powersum basis element.

            EXAMPLES::

                sage: A = MacMahonSymmetricFunctions(QQ)
                sage: P = A.P()
                sage: P[VectorPartition([[1], [1]])].antipode()
                P[[1], [1]]
            """
            # S(P[Lambda]) = (-1)^{l(Lambda)} P[Lambda]   (Martin--Trist, eq. 3.6)
            return (-1) ** len(list(vp)) * self.monomial(vp)

    P = Powersum

    class Monomial(MacMahonSymBasis_abstract):
        r"""
        The monomial basis of MacMahon symmetric functions.

        The basis element indexed by a vector partition ``Lambda`` is denoted
        ``M[Lambda]``.  Coercions between the monomial and powersum bases are
        registered during initialization.

        EXAMPLES::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: M = A.M()
            sage: P = A.P()
            sage: lam = VectorPartition([[1,1]])
            sage: M[lam]
            M[[1, 1]]
            sage: P(M[lam])
            P[[1, 1]]
            sage: M(P(M[lam])) == M[lam]
            True

        TESTS::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: M = A.M()
            sage: P = A.P()
            sage: M.has_coerce_map_from(P)
            True
            sage: P.has_coerce_map_from(M)
            True
        """
        _prefix = "M"
        _basis_name = "Monomial"
        _basis_name_letter = "M"

        def __init__(self, alg):
            r"""Initialize the monomial basis and register ``M <-> P`` maps."""
            MacMahonSymBasis_abstract.__init__(self, alg)
            p = self.realization_of().P()
            self.module_morphism(self._M_to_P, codomain=p).register_as_coercion()
            p.module_morphism(self._P_to_M, codomain=self).register_as_coercion()

        def _M_to_P(self, mu):
            """Return the powersum expansion of ``M[mu]``."""
            return self._convert_on_basis(mu, 'P')

        def _P_to_M(self, mu):
            """Return the monomial expansion of ``P[mu]``."""
            return self.realization_of().P()._convert_on_basis(mu, 'M')

        def product_on_basis(self, x, y):
            r"""
            Multiply monomial basis elements by converting through powersums.

            TESTS::

                sage: A = MacMahonSymmetricFunctions(QQ)
                sage: M = A.M()
                sage: a = VectorPartition([[1,1]])
                sage: b = VectorPartition([[1,2]])
                sage: M[a] * M[b] == M[b] * M[a]
                True
            """
            # No direct quasi-shuffle-like rule is used here; the cached change
            # of basis handles the product in the native powersum basis.
            p = self.realization_of().P()
            return self(p[x] * p[y])

    M = Monomial

    class Elementary(MacMahonSymBasis_abstract):
        r"""
        The elementary basis of MacMahon symmetric functions.

        The basis element indexed by a vector partition ``Lambda`` is denoted
        ``E[Lambda]``.  Multiplication is concatenation of vector partitions.

        EXAMPLES::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: E = A.E()
            sage: P = A.P()
            sage: lam = VectorPartition([[1,1]])
            sage: E[lam]
            E[[1, 1]]
            sage: P(E[lam])
            P[[1, 1]]
            sage: E(P(E[lam])) == E[lam]
            True

        TESTS::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: E = A.E()
            sage: P = A.P()
            sage: E.has_coerce_map_from(P)
            True
            sage: P.has_coerce_map_from(E)
            True
        """
        _prefix = "E"
        _basis_name = "Elementary"
        _basis_name_letter = "E"

        def __init__(self, alg, graded=True):
            r"""Initialize the elementary basis and register ``E <-> P`` maps."""
            MacMahonSymBasis_abstract.__init__(self, alg)
            p = self.realization_of().P()
            self.module_morphism(self._E_to_P, codomain=p).register_as_coercion()
            p.module_morphism(self._P_to_E, codomain=self).register_as_coercion()

        def _E_to_P(self, mu):
            """Return the powersum expansion of ``E[mu]``."""
            return self._convert_on_basis(mu, 'P')

        def _P_to_E(self, mu):
            """Return the elementary expansion of ``P[mu]``."""
            return self.realization_of().P()._convert_on_basis(mu, 'E')

        def product_on_basis(self, x, y):
            r"""
            Multiply elementary basis elements by concatenating parts.

            EXAMPLES::

                sage: A = MacMahonSymmetricFunctions(QQ)
                sage: E = A.E()
                sage: E[VectorPartition([[1]])] * E[VectorPartition([[2]])]
                E[[1], [2]]
            """
            return self[VectorPartition(list(x) + list(y))]

    E = Elementary

    class Homogeneous(MacMahonSymBasis_abstract):
        r"""
        The homogeneous basis of MacMahon symmetric functions.

        The basis element indexed by a vector partition ``Lambda`` is denoted
        ``H[Lambda]``.  This basis is Hall-dual to the monomial basis.

        EXAMPLES::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: P = A.P()
            sage: H = A.H()
            sage: M = A.M()
            sage: lam = VectorPartition([[2]])
            sage: H[lam].scalar(M[lam])
            1
            sage: H(P(H[lam])) == H[lam]
            True

        TESTS::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: H = A.H()
            sage: M = A.M()
            sage: lam = VectorPartition([[2]])
            sage: mu = VectorPartition([[1], [1]])
            sage: H[lam].scalar(M[mu])
            0
        """
        _prefix = "H"
        _basis_name = "Homogeneous"
        _basis_name_letter = "H"

        def __init__(self, alg):
            r"""Initialize the homogeneous basis and register ``H <-> P`` maps."""
            MacMahonSymBasis_abstract.__init__(self, alg)
            p = self.realization_of().P()
            self.module_morphism(self._H_to_P, codomain=p).register_as_coercion()
            p.module_morphism(self._P_to_H, codomain=self).register_as_coercion()

        def _H_to_P(self, mu):
            """Return the powersum expansion of ``H[mu]``."""
            return self._convert_on_basis(mu, 'P')

        def _P_to_H(self, mu):
            """Return the homogeneous expansion of ``P[mu]``."""
            return self.realization_of().P()._convert_on_basis(mu, 'H')

        def product_on_basis(self, x, y):
            r"""
            Multiply homogeneous basis elements by concatenating parts.

            EXAMPLES::

                sage: A = MacMahonSymmetricFunctions(QQ)
                sage: H = A.H()
                sage: H[VectorPartition([[1]])] * H[VectorPartition([[2]])]
                H[[1], [2]]
            """
            return self[VectorPartition(list(x) + list(y))]

    H = Homogeneous

    class Forgotten(MacMahonSymBasis_abstract):
        r"""
        The forgotten basis of MacMahon symmetric functions.

        The basis element indexed by a vector partition ``Lambda`` is denoted
        ``F[Lambda]``.  This basis is Hall-dual to the elementary basis.

        EXAMPLES::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: F = A.F()
            sage: E = A.E()
            sage: lam = VectorPartition([[2]])
            sage: E[lam].scalar(F[lam])
            1

        TESTS::

            sage: A = MacMahonSymmetricFunctions(QQ)
            sage: F = A.F()
            sage: M = A.M()
            sage: lam = VectorPartition([[2,1]])
            sage: F(M(F[lam])) == F[lam]
            True
        """
        _prefix = "F"
        _basis_name = "Forgotten"
        _basis_name_letter = "F"

        def __init__(self, alg):
            r"""Initialize the forgotten basis and register ``F <-> M`` maps."""
            MacMahonSymBasis_abstract.__init__(self, alg)
            m = self.realization_of().M()
            self.module_morphism(self._F_to_M, codomain=m).register_as_coercion()
            m.module_morphism(self._M_to_F, codomain=self).register_as_coercion()

        def _F_to_M(self, mu):
            """Return the monomial expansion of ``F[mu]``."""
            return self._convert_on_basis(mu, 'M')

        def _M_to_F(self, mu):
            """Return the forgotten expansion of ``M[mu]``."""
            return self.realization_of().M()._convert_on_basis(mu, 'F')

        def product_on_basis(self, x, y):
            r"""
            Multiply forgotten basis elements through the signed monomial map.

            TESTS::

                sage: A = MacMahonSymmetricFunctions(QQ)
                sage: F = A.F()
                sage: a = VectorPartition([[1,1]])
                sage: b = VectorPartition([[1,2]])
                sage: F[a] * F[b] == F[b] * F[a]
                True
            """
            # By convention F is omega(M), so multiplication is obtained by
            # applying the sign-twisted identification with the monomial basis.
            m = self.realization_of().M()
            return self((self.sign(x) * m[x]) * (self.sign(y) * m[y]))

    F = Forgotten
