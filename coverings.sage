from sage.all import Set
from pvg import primitive_vector_generator
from lattices import lattice, full_cover, ranks, weight, weights, indices, isFull, isCover, isMinimal, is_in_union

# Some global variables
max_skip = 0        # global to record how many primitive vectors are used
max_depth = 0       # global to record how deep the recursion went
vectors_used = []   # global list of the primitive vectors used
index_patterns = [] # global list of the distinct sorted index lists encountered
index_pattern_counter = dict() # keys are sorted index patterns as tuples
all_coverings = []  # global list of all coverings found

def FindLattice(LL, skip=0, depth=0, debug=False):
    """Given a list LL of n lattices which do *not* cover Z^2, and an integer skip>=0;
    assuming that the first 'skip' points (in PointList or as generated
    by primitive_vector_generator()) are all in the union; update the global list
    'all_coverings' of lists KK of n lattices such that
    (1) LL is contained in KK (up to permutation);
    (2) KK covers Z^2;
    (3) if LL' is any list of n proper lattices which cover Z^2
        which LL is contained in (up to permutation),
        there is some KK in the list which LL' is contained in.

    This is a recursive procedure.  Since LL is not a cover, there is
    a primitive vector v not in the union.  This is found by trying v
    in turn from the primitive vector generator until we find one not
    in the union, skipping over the first 'skip' vectors.  When v is
    found, up to n new lattice lists LL' are formed by replacing each
    lattice L in LL in turn by L+<v> (but only doing this to the first
    trivial lattice if there are more than one in LL), and testing if
    the new list LL' covers.  If so, and LL' is full, it is added to
    the global list; otherwise we recurse with LL', and with skip
    increased to the index of v plus 1.

    The recursion does terminate, since every time a lattice L is
    replaced by L'=L+<v> with v not in L, either the rank increases
    (from 0 to 1 or from 1 to 2), or the rank remains 2 but the index
    decreases (to a proper divisor of the old index).  This can happen
    only finitely many times in each branch.  The depth is hard to
    predict as it depends on how big the index is when the rank first
    reaches 2 (which will always happen in 2 steps starting from (0)).

    """
    global max_skip, max_depth, vectors_used, all_coverings
    max_skip = max(skip, max_skip)
    max_depth = max(depth, max_depth)
    pre = ' '*depth
    if debug:
        print(f"{pre}>>>---------------------------------------------------")
        print(f"{pre}In FindLattice() with {len(LL)} lattices, {skip = }, {depth = }, {debug = }")
        print(f"{pre}Lattices: {LL}")
        print(f"{pre}Ranks:    {ranks(LL)}")
        print(f"{pre}Indices:  {indices(LL)}")

    pvg = primitive_vector_generator(skip)
    v = next(pvg)

    # Find the first i such that LL[i]=(0) and set n_lattices to i+1,
    # or if none are (0) then set n_lattices to len(LL).  In the
    # recursion we only use the first n_lattices lattices, avoiding
    # repetitions of the TrivialModule.
    try:
        n_lattices = LL.index(lattice()) + 1
    except ValueError:
        n_lattices = len(LL)
    if debug:
        #print(f"{n_lattices = }")
        assert all(LL[i].rank()!=0 for i in range(n_lattices-1))
        assert n_lattices==len(LL) or LL[n_lattices-1].rank()==0

    # find the first primitive vector not in the union:
    while is_in_union(v,LL):
        skip += 1
        v = next(pvg)
        if debug:
            print(f"Incremented skip to {skip}, using {v = }")
    if skip>max_skip:
        max_skip = skip
        if debug:
            print(f"max_skip increases to {max_skip}")

    if debug:
        print(f"{pre}{skip = }, new vector {v = }")

    # use v to enlarge each of the first n_lattices lattices;
    # discard if that lattice becomes Z^2;
    # process the new list if it is a covering;
    # otherwise recurse with the new list
    for i in range(n_lattices):
        if debug:
            print(f" Step 3, {i = }")
        Lold = LL[i]
        old_index = Lold.index()
        # Lattices of prime index are maximal so we leave these alone.
        # NB checking primality for small integers is done with a
        # lookup table so is very fast.
        if Lold.rank()==2 and old_index.is_prime():
            continue
        Lnew = Lold.add_one(v)
        new_index = Lnew.index()
        if new_index==1:  # then the new vector has saturated LL[i] so this branch stops
            if debug:
                print("LL[i] enlarged to Z^2, this branch ends")
            continue # to next i

        if debug:
            print(f"LL[i] was {Lold} with index {old_index}, enlarges to {Lnew} with index {new_index}")

        LL[i] = Lnew # temporary for covering test and possible recursion
        if isCover(LL):
            if isFull(LL) and isMinimal(LL):
                # record that this vector v was useful:
                if v not in vectors_used:
                    vectors_used.append(v)
                if debug:
                    print(f"*************** Using {v = }")
                    print("*************** Enlarged lattice gives a covering")
                    print(f"***************  {LL}")
                    print(f"*************** indices {indices(LL)}")
                    print(f"*************** weights {weights(LL)}, total weight {weight(LL)}")
                # Sort LL and add it to the list if it is not there already.
                # We have to use a copy of LL, otherwise the LL we add gets changed
                sol = LL.copy()
                sol.sort() # key=lattice_sort_key)
                if debug:
                    print(f"--- processing a covering with Lattices:\n{sol}")
                ind = tuple(indices(sol)) # to use as a key
                wt = weight(sol)
                comm = "" if wt>1 else " (strongly minimal)"
                distinct = len(list(Set(ind)))==len(ind)
                if distinct:
                    comm += " (with distinct moduli) *******************************************"
                if sol not in all_coverings:
                    all_coverings.append(sol)
                    if ind not in index_patterns:
                        index_patterns.append(ind)
                        print(f"New index pattern # {len(index_patterns)}: {ind}, weight = {wt}{comm}")
                    index_pattern_counter[ind] = index_pattern_counter.get(ind,0) + 1
                if debug:
                    print(f"--- the number of coverings is now {len(all_coverings)}")

            else:
                if debug:
                    print(" - ignoring this covering as it is not minimal and full")
        else:
            if debug:
                print(f"Enlarged lattice does not give a covering, recursing with skip = {skip+1}")
            FindLattice(LL, skip+1, depth+1, debug)
        LL[i] = Lold
    if debug:
        print("<<<---------------------------------------------------")
    return

def minimal_coverings(n, verbose=True, debug=False):
    """
    Return a list of minimal coverings of size n.
    """
    print(f"Finding all minimal lattice coverings of size {n}")

    global max_skip, max_depth, vectors_used, index_patterns, index_pattern_counter, all_coverings
    max_skip = 0
    max_depth = 0
    vectors_used = []
    index_patterns = []
    index_pattern_counter = dict()
    all_coverings = []

    if n==1:
        if verbose:
            print("Only the trivial covering has size 1")
        return [full_cover(1)]
    if n==2:
        if verbose:
            print("No minimal coverings have size 2")
        return []

    P2 = full_cover(2)
    vectors_used = [L.v() for L in P2]
    LL = [lattice(0,v) for v in vectors_used] + [lattice()]*(n-3)
    FindLattice(LL, skip=3, debug=debug)
    # This save a little time compared with
    # FindLattice([TrivialModule for i in range(n)], debug= False)
    coverings = all_coverings

    if verbose:
        print(f"FindLattice() finds {len(coverings)} of size {n} after recursion to depth {max_depth}")
        print(f" --used {len(vectors_used)} primitive vectors of index up to {max_skip} :\n{vectors_used}")
        print(f"{len(index_patterns)} different index patterns occur:")
        print("Pattern\t\t Multiplicity")
        for pat,mul in index_pattern_counter.items():
            print(f"{pat}\t{mul}")

    coverings.sort(key=weight)

    strongs = [LL for LL in coverings if weight(LL)==1]
    others = [LL for LL in coverings if weight(LL)>1]
    all_strong = len(others)==0

    if all_strong:
        if verbose:
            print(f"All {len(strongs)} minimal coverings found are strongly minimal.")
        return strongs

    if verbose:
        print(f"Only {len(strongs)} coverings found are strongly minimal, the other {len(others)} are not.")

    minimals = [LL for LL in others if isMinimal(LL)]

    if verbose:
        if not minimals:
            print(f"All {len(strongs)} minimal coverings are strongly minimal.")
        else:
            print(f" - of the coverings which are not strongly minimal, {len(minimals)} are minimal.")
        print(f"There are {len(strongs)+len(minimals)} minimal coverings in total.")

    return strongs + minimals
