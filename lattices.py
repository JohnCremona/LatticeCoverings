# JC's revised version of PH's sage code to find minimal lattice coverings

# This version does not use lattices explicitly, just [N,c,d] triples to
# encode L(c:d;N).

from sage.all import gcd, xgcd, GCD, LCM, ZZ, Infinity, cached_function
from pvg import V, psi, P1, wedge

class lattice:
    r"""Class to store a lattice (subgroup of ZZ^2), encoded as [N,c,d] where:

    N is a positive integer (the index) or 0 for a rank 1 subgroup;

    (c,d) is a pair of coprime integers, defining the lattice L(c:d;N) if N>0
    or the rank 1 lattice <(c,d)> if N=0;

    The 0 subgroup is encoded as [0,0,0].

    Equality: [N1,c1,d1[=[N2,c2,d2] iff N1==N2 and N1 divides
    c1*d2-c2*d1 (so if N1=N2=0, either (c1,d1)=(c2,d2) or
    (-c2,-d2)). Unless [N1,c1,d1]=[0,0,0] which is only equal to
    itself.

    """
    def __init__(self, N=0, c=None, d=None):
        r"""
        Construct a lattice.

        INPUT:

        - ``N`` -- a non-negative integer

        - ``c``, ``d`` -- either two integers, which are coprime, or both 0 when N=0; or id d is None, c should be a vector in ZZ^2 which is either primitive or 0.
        """
        self.N = ZZ(N)
        if N==0 and c is None:
            self.c = self.d = ZZ(0)
        else:
            if d is None:
                self.c, self.d = c
            else:
                self.c = ZZ(c)
                self.d = ZZ(d)
        # we normalize on creation to make it faster to compute the
        # index of (c:d) in P(N), needed for sorting (rank 2 only)
        if N:
            P1N = P1(N)
            self.c, self.d = P1N.normalize(self.c, self.d)
            self.P1_index = P1N.index_of_normalized_pair(self.c, self.d)

    def __repr__(self):
        return f"L({self.c}:{self.d};{self.N})"

    def is_trivial(self):
        """
        Return whether this is the trivial (rank 0) lattice
        """
        return self.N==0 and self.c==0 and self.d==0

    def v(self):
        return (self.c, self.d)

    def basis(self):
        if self.is_trivial():
            return []
        v1 = self.v()
        if self.N == 0:
            return [v1]
        g,x,y = xgcd(self.c, self.d)
        assert g==1
        v2 = (self.N*y,-self.N*x) # so the lattice basis is [v1,v2]
        return [v1, v2]

    def lattice(self):
        """
        Return the associated subgroup of ZZ^2.
        """
        return V.span(self.basis())

    def index(self):
        """
        Return the index in ZZ^2 of the associated subgroup.
        """
        return self.N if self.N else Infinity

    def rank(self):
        """
        Return the rank of the associated subgroup of ZZ^2.
        """
        if self.N:
            return 2
        return 0 if self.c==0 and self.d==0 else 1

    def psi(self):
        """
        Return the number of cocylic lattices of this index.
        """
        return psi(self.N) if self.N else 0

    def weight(self):
        return 1/psi(self.N) if self.N else Infinity

    def contains1(self,v):
        """
        Return whether self contains vector v
        """
        if self.rank()==0:
            return v==0
        c, d = v
        return self.N.divides(c*self.d-d*self.c)

    def contains(self, other):
        """
        Return whether self contains another lattice
        """
        return self.N.divides(other.N) and self.contains1(other.v())

    def is_contained_in(self, other):
        """
        Return whether self is contained in another lattice
        """
        return other.N.divides(self.N) and other.contains1(self.v())

    def add_one(self, w):
        """
        Return the lattice spanned by self and one more vector
        """
        if self.is_trivial():
            return lattice(0,w)
        else:
            return lattice(gcd(self.N, wedge(self.v(),w)), self.v())

    def __hash__(self):
        return hash((self.N, self.c, self.d))

    def __eq__(self,other):
        if self.N!=other.N:
            return False
        if self.is_trivial():
            return other.is_trivial()
        if self.rank() != other.rank():
            return False
        # now both have the same rank 1 or 2
        return other.contains1(self.v())

    def __ne__(self,other):
        return not self.__eq__(other)

    def __lt__(self, other):
        # first compare ranks
        t = other.rank() - self.rank()
        if t:
            return t>0
        # now the ranks are equal, compare indices:
        t = other.N - self.N
        if t:
            return t>0
        # now the indices are equal, compare (c:d) in P(N)
        return self.P1_index < other.P1_index

    def __gt__(self, other):
        return not self.__lt__(other)

    def __ge__(self, other):
        return  self.__eq__(other) or self.__gt__(other)

    def __le__(self, other):
        return  self.__eq__(other) or self.__lt__(other)


############ end of definition of class lattice ##########################################################

def encode_lattice(L):
    """
    Convert an actual subgroup of ZZ^2 into a lattice
    """
    if L.rank()==0:
        return lattice()
    v = L.basis()[0]
    if L.rank()==1:
        return lattice(0, v)
    N = L.index_in(V)
    if gcd(v)!=1:
        A, _, U = L.basis_matrix().smith_form()
        v = (U[1][1],-U[0][1])
    return lattice(N,v)


# Convention: L is one lattice, LL is a list of lattices

def ranks(LL):
    """
    Return the list of indices of this list of lattices
    """
    return [L.rank() for L in LL]

def indices(LL):
    """
    Return the list of indices of this list of lattices
    """
    return [L.index() for L in LL]

def index_lcm(LL):
    """
    Return the lcm of of the indices of the L in LL
    """
    return LCM(indices(LL))

@cached_function
def lattice_sort_key(L):
    return [-L.rank(), L.index(), L.P1_index]

def weights(LL):
    """
    Return the list of weights of this list of lattices
    """
    return [L.weight() for L in LL]

def weight(LL):
    """
    Return the sum of L.weight() for L in LL, where LL is a list of lattices.
    """
    return sum(weights(LL))

def is_in_union(v, LL):
    """
    Return True if v is in at least one of the lattices L in the list LL
    """
    return any(L.contains1(v) for L in LL)

def full_cover(N):
    """
    Return the full index N covering.
    """
    return [lattice(N,v) for v in P1(N)]

def isCover_rank2(LL, debug=False):
    """
    Given a list of rank 2 lattices, return whether they cover Z^2
    """
    # Check the necessary condition that the weight is at least 1.
    # The empty list has weight 0.

    if weight(LL) < 1:
        return False

    # Check that every v in P(N) lies in at least one, where N is the index lcm
    N = index_lcm(LL)
    return all(is_in_union(v,LL) for v in P1(N))

def isCover(LL, debug=False):
    """
    Given a list of lattices, return whether they cover Z^2
    """
    return isCover_rank2([L for L in LL if L.rank()==2])

def isCover_without1(LL, i, debug=False):
    """
    Given a list of lattices, return whether they cover Z^2 if the
    i'th lattice is deleted.
    """
    return isCover_rank2([L for j,L in enumerate(LL) if j!=i and L.rank()==2])

def isFull(LL, check=False):
    """
    Assuming that LL is a list of lattices which cover, return True iff
    (1) all have full rank, and (2) removing any breaks the covering
    property.  Note that (2) can only occur if the weight is strictly >1.

    If check is True, first check that LL covers.
    """
    if check and not isCover(LL):
        return False
    return (not any(L.rank()<2 for L in LL)) and (weight(LL)==1 or not any(isCover_without1(LL,i) for i in range(len(LL))))

def isOneMinimal(LL, L):
    """
    Assuming that LL covers, and L in LL, return True iff L cannot be
    replaced by a proper sublattice.
    """
    # print(f"Checking {LL} for minimality w.r.t. {L}")
    # First a quick check on the weight: replacing L by a proper
    # sublattice reduces the weight by at least wt(L)/2:
    w = weight(LL)
    if L.weight() > 2*(w-1):
        return True

    # Now the full check.
    M = index_lcm(LL)
    PM = P1(M)
    # any sublattice must contain all these:
    S = [v for v in PM if not any(L1!=L and L1.contains1(v) for L1 in LL)]
    nS = len(S)
    if nS==0: # L is completely redundant
        return False
    v = S[0]
    D = GCD([M] + [wedge(v,w) for w in S[1:]])
    # the smallest lattice containing S is L(v;D)
    return D==L.index()

def isMinimal(LL, check=False):
    """
    Assuming that LL covers, return True iff LL is minimal.

    If check is True, first check that LL covers.
    """
    # print(f"Checking {LL} for minimality")
    if check and not isCover(LL):
        return False
    return all(isOneMinimal(LL,L) for L in LL)

def isStronglyMinimal(LL, check=False):
    """
    Assuming that LL covers, return True iff LL is strongly minimal

    If check is True, first check that LL covers.
    """
    if weight(LL)!=1:
        return False
    if check and not isCover(LL):
        return False
    return all(isOneMinimal(LL,L) for L in LL)

