# Adaptation of lattice covering code for APs (Arithmetic Progressions, i.e. resudue classes)

from sage.all import ZZ, LCM, GCD, gcd, srange, Infinity

# Use [N,a] triples to encode a+NZ, displayed as <a;N>

class AP:
    r"""Class to store an AP encoded as [N,a] where:

    N is a positive integer (the modulus) or 0 for a singleton

    a with 0<=a<N is a class representative

    The 0 subgroup is encoded with N=None.

    """
    def __init__(self, N=None, a=None):
        r"""
        Construct a AP.

        INPUT:

        - ``N`` -- a non-negative integer
        - ``a`` -- an integer
        """
        if N is None:
            self.N = None
            self.a = None
        else:
            self.N = ZZ(N)
            if self.N:
                self.a = ZZ(a) % self.N
            else:
                self.a = ZZ(a)

    def __repr__(self):
        return f"<{self.a};{self.N}>"

    def is_trivial(self):
        """
        Return whether this is the trivial (rank 0) AP
        """
        return self.N is None

    def modulus(self):
        """
        Return the modulus of this AP
        """
        return self.N if self.N else Infinity

    def weight(self):
        return 1/self.N if self.N else Infinity

    def contains1(self,x):
        """
        Return whether self contains integer x
        """
        if self.N is None:
            return False
        return self.N.divides(self.a-x)

    def contains(self, other):
        """
        Return whether self contains another AP
        """
        return self.N.divides(other.N) and self.contains1(other.a)

    def is_contained_in(self, other):
        """
        Return whether self is contained in another AP
        """
        return other.N.divides(self.N) and other.contains1(self.a)

    def add_one(self, x):
        """
        Return the AP spanned by self and one more integer
        """
        if self.is_trivial():
            return AP(0,x)
        else:
            return AP(gcd(self.N, x - self.a), x)

    def __hash__(self):
        return hash((self.N, self.a))

    def __eq__(self,other):
        if self.N!=other.N:
            return False
        if self.is_trivial():
            return other.is_trivial()
        return other.contains1(self.a)

    def __ne__(self,other):
        return not self.__eq__(other)

    def __lt__(self, other):
        if self.is_trivial():
            return not other.is_trivial()
        if other.is_trivial():
            return False
        # compare moduli:
        t = other.N - self.N
        if t:
            return t>0
        # now the moduli are equal, compare a's
        return self.a < other.a

    def __gt__(self, other):
        return not self.__lt__(other)

    def __ge__(self, other):
        return  self.__eq__(other) or self.__gt__(other)

    def __le__(self, other):
        return  self.__eq__(other) or self.__lt__(other)


############ end of definition of class AP ##########################################################

# Convention: A is one AP, C is a list of APs

def moduli(C):
    """
    Return the list of moduli of this list of APs
    """
    return [A.N for A in C]

def modulus_lcm(C):
    """
    Return the lcm of of the moduli of the A in C
    """
    return LCM(moduli(C))

def weights(C):
    """
    Return the list of weights of this list of APs
    """
    return [A.weight() for A in C]

def weight(C):
    """
    Return the sum of A.weight() for A in C, where C is a list of APs.
    """
    return sum(weights(C))

def is_in_union(x, C):
    """
    Return True if x is in at least one of the APs A in the list C
    """
    return any(A.contains1(x) for A in C)

def full_cover(N):
    """
    Return the full modulus N covering.
    """
    return [AP(N,x) for x in srange(N)]

def isCover_rank2(C, debug=False):
    """
    Given a list of genuine APs, return whether they cover Z
    """
    # Check the necessary condition that the weight is at least 1.
    # The empty list has weight 0.

    if weight(C) < 1:
        return False

    # Check that every x mod N lies in at least one, where N is the modulus lcm
    N = modulus_lcm(C)
    return all(is_in_union(x,C) for x in srange(N))

def isCover(C, debug=False):
    """
    Given a list of APs, return whether they cover Z
    """
    return isCover_rank2([A for A in C if A.N])

def isCover_without1(C, i, debug=False):
    """
    Given a list of APs, return whether they cover Z if the
    i'th AP is deleted.
    """
    return isCover_rank2([A for j,A in enumerate(C) if j!=i and A.N])

def isFull(C, check=False):
    """
    Assuming that C is a list of APs which cover, return True iff
    (1) all are genuine APs, and (2) removing any breaks the covering
    property.  Note that (2) can only occur if the weight is strictly >1.

    If check is True, first check that C covers.
    """
    if check and not isCover(C):
        return False
    return (not any(A.N==0 for A in C)) and (weight(C)==1 or not any(isCover_without1(C,i) for i in range(len(C))))

def isOneMinimal(C, A):
    """
    Assuming that C covers, and A in C, return True iff A cannot be
    replaced by a proper subAP.
    """
    # print(f"Checking {C} for minimality w.r.t. {A}")
    # First a quick check on the weight: replacing A by a proper
    # subAP reduces the weight by at least wt(A)/2:
    w = weight(C)
    if A.weight() > 2*(w-1):
        return True

    # Now the full check.
    M = modulus_lcm(C)
    # any subAP must contain all these:
    S = [x for x in srange(M) if not any(A1!=A and A1.contains1(x) for A1 in C)]
    nS = len(S)
    if nS==0: # A is completely redundant
        return False
    x = S[0]
    D = GCD([M] + [x-y for y in S[1:]])
    # the smallest AP containing S is A(x;D)
    return D==A.N

def isMinimal(C, check=False):
    """
    Assuming that C covers, return True iff C is minimal.

    If check is True, first check that C covers.
    """
    # print(f"Checking {C} for minimality")
    if check and not isCover(C):
        return False
    return all(isOneMinimal(C,A) for A in C)

def isStronglyMinimal(C, check=False):
    """
    Assuming that C covers, return True iff C is strongly minimal

    If check is True, first check that C covers.
    """
    if check and not isCover(C):
        return False
    return all(isOneMinimal(C,A) for A in C)


