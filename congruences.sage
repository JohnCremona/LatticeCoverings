# Program to find all congruence coverings of Z of a given size

from sage.all import Set
from AP import AP, moduli, is_in_union, weight, weights, isCover, isFull, isMinimal

# Some global variables
max_skip = 0        # global to record how many  integers are used
max_depth = 0       # global to record how deep the recursion went
integers_used = []   # global list of the integers used
modulus_patterns = [] # global list of the distinct sorted modulus lists encountered
all_coverings = []  # global list of all coverings found

def FindCovering(C, skip=0, depth=0, debug=False):
    """Given a list C of n APs which do *not* cover Z, and an integer skip>=0;
    assuming that the first 'skip' integers are all in the union; update the global list
    'all_coverings' of coverings

    This is a recursive procedure.  Since C is not a cover, there is
    an integer not in the union.  This is found by trying x
    in turn (starting from 0 and incrememnting by 1) until we find one not
    in the union, skipping over the first 'skip' integers.  When x is
    found, up to n new AP lists C' are formed by replacing each
    A in C in turn by A+<x> (but only doing this to the first
    trivial AP if there are more than one in C), and testing if
    the new list C' covers.  If so, and C' is full, it is added to
    the global list; otherwise we recurse with C', and with skip
    increased to x+1.

    """
    global max_skip, max_depth, integers_used, all_coverings
    max_skip = max(skip, max_skip)
    max_depth = max(depth, max_depth)
    if debug:
        pre = ' '*depth
        print(f"{pre}>>>---------------------------------------------------")
        print(f"{pre}In FindCovering() with {len(C)} APs, {skip = }, {depth = }, {debug = }")
        print(f"{pre}Indices: {moduli(C)}")

    x = skip

    # Find the first i such that C[i]={} and set n_APs to i+1,
    # or if none are {} then set n_APs to len(C).  In the
    # recursion we only use the first n_APs APs, avoiding
    # repetitions of the empty set.
    try:
        n_APs = C.index(AP()) + 1
    except ValueError:
        n_APs = len(C)
    if debug:
        print(f"After step 1, {n_APs = }")
        assert not any(C[i].is_trivial() for i in range(n_APs-1))
        assert n_APs==len(C) or C[n_APs-1].N is None

    # find the first integer not in the union:
    while is_in_union(x,C):
        skip += 1
        x += 1
        if debug:
            print(f"Incremented skip to {skip}, using {x = }")
    if skip>max_skip:
        max_skip = skip
        if debug:
            print(f"max_skip increases to {max_skip}")

    if debug:
        print(f"After step 2, {skip = } and {x = }")

    # use x to enlarge each of the first n_APs APs;
    # discard if that AP becomes Z;
    # process the new list if it is a covering;
    # otherwise recurse with the new list
    for i in range(n_APs):
        if debug:
            print(f" Step 3, {i = }")
        Aold = C[i]
        old_modulus = Aold.N
        # APs of prime modulus are maximal so we leave these alone.
        # NB checking primality for small integers is done with a
        # lookup table so is very fast.
        if old_modulus and old_modulus.is_prime():
            continue
        Anew = Aold.add_one(x)
        new_modulus = Anew.N
        if new_modulus==1:  # then the new integer has saturated C[i] so this branch stops
            if debug:
                print("C[i] enlarged to Z, this branch ends")
            continue # to next i

        if debug:
            print(f"C[i] was {Aold}, enlarges to {Anew}")

        # record that this integer x was useful:
        if x not in integers_used:
            integers_used.append(x)
            if debug:
                print(f"Using {x = }")

        C[i] = Anew # temporary for covering test and possible recursion
        if isCover(C):
            if isFull(C): # and isMinimal(C):
                if debug:
                    print("***************Enlarged AP gives a covering")
                    print(f"*************** moduli {moduli(C)}")
                    print(f"*************** weights {weights(C)}, total weight {weight(C)}")
                # Sort C and add it to the list if it is not there already.
                # We have to use a copy of C, otherwise the C we add gets changed
                sol = C.copy()
                sol.sort()
                ind = moduli(sol)
                wt = weight(sol)
                comm = ""
                if wt==1:
                    comm = " (strongly minimal)"
                else:
                    if isMinimal(sol):
                        comm = " (minimal)"
                    else:
                        comm = " (not minimal)"
                distinct = len(list(Set(ind)))==len(ind)
                if distinct:
                    comm += " (with distinct moduli)"
                if debug:
                    print(f"--- processing a covering with APs:\n{sol}")
                if sol not in all_coverings:
                    all_coverings.append(sol)
                    print(f"New covering # {len(all_coverings)}: {sol} {comm}")
                if debug:
                    print(f"--- the number of coverings is now {len(all_coverings)}")
                if ind not in modulus_patterns:
                    modulus_patterns.append(ind)
                    print(f"New modulus pattern # {len(modulus_patterns)}: {ind}, weight = {wt}{comm}")
            else:
                if debug:
                    print(" - ignoring this covering as it is not full")
        else:
            if debug:
                print(f"Enlarged AP does not give a covering, recursing with skip = {skip+1}")
            FindCovering(C, skip+1, depth+1, debug)
        C[i] = Aold
    if debug:
        print("<<<---------------------------------------------------")
    return

def minimal_coverings(n, verbose=True):
    """
    Return a list of minimal covering congruences of size n.
    """
    print(f"Finding all minimal covering congruences of size {n}")

    global max_skip, max_depth, integers_used, modulus_patterns, all_coverings
    max_skip = 0
    max_depth = 0
    integers_used = []
    modulus_patterns = []
    all_coverings = []
    if n>1:
        integers_used = [0,1]
        C = [AP(0,x) for x in integers_used] + [AP()]*(n-2)
        FindCovering(C, skip=2)
    else:
        if verbose:
            print("The only covering congruence of size 1 is the trivial one")
        C = [AP(1,0)]
        all_coverings = [C]
    coverings = all_coverings

    if verbose and n>1:
        print(f"FindCovering() finds {len(coverings)} of size {n} after recursion to depth {max_depth}")
        print(f" --used {len(integers_used)} primitive integers of modulus up to {max_skip} :\n{integers_used}")
        print(f"{len(modulus_patterns)} different modulus patterns occur")

    coverings.sort(key=weight)

    strongs = [C for C in coverings if weight(C)==1]
    others = [C for C in coverings if weight(C)>1]
    all_strong = len(others)==0

    if all_strong:
        if verbose:
            print(f"All {len(strongs)} minimal coverings found are strongly minimal.")
        return strongs

    if verbose:
        print(f"Only {len(strongs)} coverings found are strongly minimal, the other {len(others)} are not.")

    minimals = [C for C in others if isMinimal(C)]

    if verbose:
        if not minimals:
            print(f"All {len(strongs)} minimal coverings are strongly minimal.")
        else:
            print(f" - of the coverings which are not strongly minimal, {len(minimals)} are minimal.")
        print(f"There are {len(strongs)+len(minimals)} minimal coverings in total.")

    return strongs + minimals
