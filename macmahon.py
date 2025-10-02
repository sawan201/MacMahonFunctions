from sage.all import *                      

def normalize_alpha(alpha, ell):            # Helper: validate and canonicalize a single multi-index α of length ell.
    a = tuple(int(v) for v in alpha)        # Coerce entries to ints and freeze as a tuple (hashable, comparable).
    if len(a) != ell:                        # Check the length matches the number of alphabets ℓ.
        raise ValueError(f"alpha {alpha} has length {len(a)} != ell={ell}")  # Fail fast if wrong length.
    if any(v < 0 for v in a):               # Disallow negative exponents.
        raise ValueError(f"alpha {alpha} has a negative entry")              # Explain the issue.
    if all(v == 0 for v in a):              # Disallow the all-zero vector (not a valid part).
        raise ValueError("alpha must not be all zeros")
    return a                                # Return the validated α as a tuple.

def normalize_key(alphas, ell):             # Helper: turn a multiset/list of α’s into a canonical monomial key.
    # alphas is an iterable of α’s (each a tuple of length ell)
    clean = tuple(normalize_alpha(a, ell) for a in alphas)  # Validate each α and collect them into a tuple.
    return tuple(sorted(clean))             # Sort lexicographically -> canonical order (so keys are unique).

class PSElement:                           # Minimal "Power-Sum" element (plain Python, not Sage Element).
    def __init__(self, ell, data=None):     # Construct with number of alphabets ℓ and an optional dict of terms.
        self.ell = ell                      # Store ℓ (used to validate/compose keys later).
        self.data = {}                      # Internal sparse representation: { key(tuple of α’s) -> coefficient }.
        if data:                            # If an initial mapping is provided,
            for k, c in data.items():       # iterate over (key, coefficient) pairs,
                if c != 0:                  # keep only nonzero coefficients (sparse).
                    self.data[k] = c

    @classmethod
    def one(cls, ell):                      # Construct the multiplicative identity 1 (empty product).
        return cls(ell, {(): 1})            # Empty key () encodes the monomial "1" with coefficient 1.

    @classmethod
    def zero(cls, ell):                     # Construct the additive identity 0.
        return cls(ell, {})                 # No terms -> the zero element.

    @classmethod
    def gen(cls, ell, alpha):               # Construct a single generator p_α.
        k = normalize_key([alpha], ell)     # Canonical key for the singleton multiset {α}.
        return cls(ell, {k: 1})             # Element with exactly that generator and coefficient 1.

    def __repr__(self):                     # Human-readable string for printing in the REPL / logs.
        if not self.data:                   # If there are no terms,
            return "0"                      # print "0".
        parts = []                          # Otherwise, build pieces for each term to join with " + ".
        for key, c in self.data.items():    # For each monomial key and its coefficient,
            if key == ():                   # if the key is empty,
                mon = "1"                   # the monomial is "1".
            else:                           # otherwise,
                mon = "*".join(f"p{a}" for a in key)  # render as p(α1)*p(α2)*... in order.
            if c == 1 and key != ():        # If coefficient is 1 and not the constant term,
                parts.append(mon)           # omit the leading "1*" for cleanliness.
            else:
                parts.append(f"{c}*{mon}")  # otherwise include the numeric coefficient.
        return " + ".join(parts)            # Join all terms with " + " and return.

    def __add__(self, other):               # Addition of two PSElements.
        assert self.ell == other.ell        # Ensure both live in the same number of alphabets.
        out = dict(self.data)               # Start with a copy of the left operand’s terms.
        for k, c in other.data.items():     # Add in the right operand’s terms,
            out[k] = out.get(k, 0) + c      # summing coefficients when keys match.
            if out[k] == 0:                 # Drop zeros that arise (clean sparsity).
                del out[k]
        return PSElement(self.ell, out)    # Return a new element with the merged mapping.

    def __neg__(self):                      # Unary minus.
        return PSElement(self.ell, {k: -c for k, c in self.data.items()})  # Flip all coefficients.

    def __sub__(self, other):               # Subtraction defined via addition and negation.
        return self + (-other)

    def __mul__(self, other):               # Multiplication of two PPSElements.
        assert self.ell == other.ell        # Must have the same ℓ.
        out = {}                            # Accumulate product terms here.
        for k1, c1 in self.data.items():    # For each term c1 * p^{k1} in the left,
            for k2, c2 in other.data.items():  # and each term c2 * p^{k2} in the right,
                k = normalize_key(k1 + k2, self.ell)  # concatenate the α-multisets and re-sort (canonical product key).
                out[k] = out.get(k, 0) + c1 * c2      # accumulate the product coefficient.
                if out[k] == 0:            # If it cancels to zero, remove it to keep the mapping sparse.
                    del out[k]
        return PSElement(self.ell, out)    # Return the product element.

def power_series_basis(ell, allowed_alphas, max_deg, *, as_elements=False):
    """
    Monomial basis for the formal power-series algebra in generators p_α,
    truncated to total degree ≤ max_deg.

    Parameters
    ----------
    ell : int
        Number of alphabets (length of each α).
    allowed_alphas : iterable of tuples
        Finite set of α’s you permit as generators (each α ∈ ℕ^ell \ {0}).
        Example for ℓ=2: [(1,0),(0,1),(1,1)].
    max_deg : int
        Truncation degree. Includes the constant 1 at degree 0.
    as_elements : bool, keyword-only (default: False)
        If True, return a list of PSElement’s (coeff 1) for each basis monomial.
        If False, return the canonical monomial keys (tuples of α’s).

    Returns
    -------
    list
        If as_elements=False: list of keys, each a tuple (α1, α2, ... , αd) with d ≤ max_deg.
        If as_elements=True: list of PSElement(ell, {key:1}) in the same order.
    """
    if max_deg < 0:
        return []

    # Deduplicate & validate the allowed generators
    pool = sorted({normalize_alpha(a, ell) for a in allowed_alphas})

    basis_keys = []

    # Degree 0: the constant 1 (empty key)
    basis_keys.append(())

    # Degrees 1..max_deg: multisets of generators
    for d in range(1, max_deg + 1):
        for combo in combinations_with_replacement(pool, d):
            key = normalize_key(combo, ell)   # canonical key for the monomial
            basis_keys.append(key)

    if as_elements:
        return [PSElement(ell, {k: 1}) for k in basis_keys]
    return basis_keys

