# Sage functions for systematically finding all index lists for
# strongly minimal coverings, by (1) solving the weight equations, and
# (2) eliminating index lists which satisfy the weight equation but
# which cannot come from a strongly minimal lattice covering as one or
# more necessary conditions fail.

from sage.all import Gamma0, srange, ZZ, gcd, lcm, cartesian_product_iterator, cached_function

# An index list [N_1,...,N_n] satisfies the weight equation iff sum(1/psi(N_i))=1.

@cached_function
def psi(N):
    return 1 if N==0 else Gamma0(N).index()

# psi is not an increasing function, e.g. psi(6)=12, psi(7)=8.

# psi(x)=M has only finitely many solutions x and these satisfy x<M
# (except psi(1)=1).  We make a lookup table of the solutions for M up
# to psimax:

psimax = 100
psi_inv_tab = dict([(x,[]) for x in srange(psimax)])
for N in srange(1,psimax):
    psiN = psi(N)
    if psiN<psimax:
        psi_inv_tab[psiN].append(N)


# Given $n$, find all $N_1\le N_2\le\dots\le N_n$ with $\sum_{i=1}^{n}\frac{1}{\psi(N_i)}=1$.

# First find all M_1, ..., M_n with sum(1/M_i)=1.  Then expand to
# solutions in N_i by using the lookup table to replace each M_i with
# one or more solutions N_i to psi(N_i)=M_i.

def solve_weights(n, total, minpsi, strong=True, debug=False):
    """Returns a list of weakly increasing lists of n values of psi(N)
    satisfying sum(psi(N))=total, with all values >=minpsi.

    'strong' is not used (always True) at present.

    Algorithm: assuming M_1 <= M_2 <= ... <= M_n, find upper and lower
    bounds for M_1 in terms of n and total.  For each, solve
    recursively with n-1 terms and new_total=total-1/M_1.

    Note: the same code would solve sum(1/M_i)=total with n terms for
    arbitrary positive integers M_i.  All we do that is special here
    is to ignore any M which are not values of psi, as determined from
    the lookup table.
    """
    if debug:
        print(f"In solve_weights() with {n=}, {total=}, {minpsi=}")
    if n==0 or (strong and total<=0):
        return []
    ans = []
    for psiN in srange(minpsi,psimax):
        if not psi_inv_tab[psiN]:
            continue
        # We require 1/psiN <= total; if equal and n==1 then one solution, otherwise recurse:
        t = psiN*total-n
        if t > 0:
            break
        if debug:
            print(f" - trying {psiN=}")
        if t == 0:
            if debug:
                print(f" - {psiN=} fits exactly ({n} times)")
            ans.append([psiN]*n)
        else: # t<0
            if n==1:
                continue
            if debug:
                print(f" - {psiN=} fits, using recursion for the rest")
            tails = solve_weights(n-1,total-ZZ(1)/psiN, psiN, strong, debug)
            if debug:
                print(f" - recursion returns {tails}")
            for tail in tails:
                ans.append([psiN]+tail)
    if debug:
        print(f"*** solve_weights() with {n=}, {total=}, {minpsi=} returns {ans}")
    return ans

def Nlist_from_psiNlist(psis, debug=False):
    """
    Given a list of psi(N) values, return a list of lists of N with those values.
    """
    if debug:
        print(f"List of psi(N): {psis}")
    Ns = [psi_inv_tab[x] for x in psis]
    if debug:
        print(f"List of lists of N: {Ns}")
    if not all(y for y in Ns):
        return []
    allNs = list(cartesian_product_iterator(Ns))
    if debug:
        print(f"List of lists of N: {allNs}")
    return allNs


def is_valid_Nlist(Nlist, strong=True, debug=False):
    """
    Test a list Nlist of indices N for validity as an index sequence
    for a strongly minimal covering. This is not a complete test yet,
    we just impose some necessary condictions.  These suffice for
    n<=8.
    """
    if debug:
        print(f"Checking validity of {Nlist} ({strong=})")

    # (1) check the weight (in)equality holds:
    wt = sum((ZZ(1)/psi(N) for N in Nlist))
    if not (wt==1 if strong else wt>=1):
        if debug:
            print("weight condition fails")
        return False
    if debug:
        print("weight condition passes")

    # (2) in the strong case, make sure that no two indices are coprime:
    if strong:
        if any((gcd(N1,N2)==1 for N1 in Nlist for N2 in Nlist)):
            if debug:
                print("NO: there are coprime indices")
            return False
        if debug:
            print("OK: no coprime indices")

    # (3) various tests for each prime p dividing any index
    supp = lcm(Nlist).support()
    for p in supp:
        if debug:
            print(f"{p=}:")

        # (3)(a) Check that we have at least p+1 lattices with p|index:
        Np = sum(N%p==0 for N in Nlist)
        if Np<=p:
            if debug:
                print(f"NO: only {Np} terms are divisible by {p}")
            return False
        if debug:
            print(f"OK: {Np} terms are divisible by {p}")

        # (3)(b) If strong and we have p lattices of index p,
        # check that we have no two indices p*m,p*n with m,n coprime:
        if strong:
            if Nlist.count(p)==p:
                if debug:
                    print(f"{p} terms are equal to {p}")
                pNlist = [N//p for N in Nlist if N%p==0 and N!=p]
                if debug:
                    print(f"Other terms divisible by {p} have cofactors {pNlist}")
                if any((gcd(N1,N2)==1 for N1 in pNlist for N2 in pNlist)):
                    return False
                if debug:
                    print("OK")

    # No more tests except in the strong case
    if not strong:
        return True

    N2 = Nlist.count(2)
    N3 = Nlist.count(3)
    N4 = Nlist.count(4)
    N6 = Nlist.count(6)

    # (4) Rule out [2,4,6,...] with more than four 6s
    if N2 and N4 and N6>4:
        if debug:
            print("NO: 2,4 and more than four 6s")
        return False

    # (5) Rule out [2,2,4,...] and [2,4,4,4,...] if not all the rest are multiples of 4,
    # or they are, but two cofactors are coprime:
    if (N2==2 and N4==1) or (N2==1 and N4==3):
        Nlist2 = [N for N in Nlist if N!=2 and N!=4]
        if not all(N%4==0 for N in Nlist2):
            return False
        Nlist2m = [N//4 for N in Nlist2]
        if any((gcd(N1,N2)==1 for N1 in Nlist2m for N2 in Nlist2m)):
            return False

    # (6) Rule out [2,4,4,...] if not all the rest are multiples of 2,
    # or they are, but two cofactors are coprime:
    if (N2==1 and N4==2):
        Nlist2 = [N for N in Nlist if N!=2 and N!=4]
        if not all(N%2==0 for N in Nlist2):
            return False
        Nlist2m = [N//2 for N in Nlist2]
        if any((gcd(N1,N2)==1 for N1 in Nlist2m for N2 in Nlist2m)):
            return False

    # (7) Rule out [2,2,6,6,6,...] or [2,4,4,6,6,6,...] if not all the rest are multiples of 6,
    # or they are, but two cofactors are coprime:
    if (N2==2 and N6==3):
        Nlist2 = [N for N in Nlist if N!=2 and N!=6]
        if not all(N%6==0 for N in Nlist2):
            return False
        Nlist2m = [N//6 for N in Nlist2]
        if any((gcd(N1,N2)==1 for N1 in Nlist2m for N2 in Nlist2m)):
            return False
    if (N2==1 and N4==2 and N6==3):
        Nlist2 = [N for N in Nlist if N!=2 and N!=4 and N!=6]
        if not all(N%6==0 for N in Nlist2):
            return False
        Nlist2m = [N//6 for N in Nlist2]
        if any((gcd(N1,N2)==1 for N1 in Nlist2m for N2 in Nlist2m)):
            return False

    # (8) Rule out [3,3,3,6,6,6,...] if not all the rest are multiples of 6,
    # or they are, but two cofactors are coprime:
    if (N3==3 and N6==2):
        Nlist2 = [N for N in Nlist if N!=3 and N!=6]
        if not all(N%6==0 for N in Nlist2):
            return False
        Nlist2m = [N//6 for N in Nlist2]
        if any((gcd(N1,N2)==1 for N1 in Nlist2m for N2 in Nlist2m)):
            return False

    # (9) Rule out [3,3,6,6,6,6,...] if not all the rest are multiples of 6,
    # or they are, but two cofactors are coprime:
    if (N3==2 and N6>=4):
        Nlist2 = [N for N in Nlist if N!=3 and N!=6]
        if not all(N%6==0 for N in Nlist2):
            return False
        Nlist2m = [N//6 for N in Nlist2]
        if any((gcd(N1,N2)==1 for N1 in Nlist2m for N2 in Nlist2m)):
            return False

    return True

# The main function.

def all_index_sequences(n, strong=True, debug=False):
    """
    Return a list of possible sorted index sequences for strongly minimal coverings of length n.

    'strong' is redundant (always True, the nonstrong case is not implemented).

    (1) Use solve_weights() to find a list of all lists [M1,M2,...,Mn]
    where each Mi is a value of psi, satisfying the weight equation
    sum(1/Mi)=1.

    (2) Hence find a list of all lists [N1,...,Nn] satisfying sum(1/psi(Ni))=1.

    (3) Use is_valid_Nlist() to discard any which fail to satisfy one of several necessary conditions.

    """
    # For n=1,2,3 we just write down the knwon solutions.
    if n==1:
        return [[1]]
    if n==2:
        return []
    if n==3:
        return [[2,2,2]]

    # Now n>=4. Use the recursive function to find integer solutions of length n, total 1, all psi(N)>=3:
    psiNlist = solve_weights(n, total=1, minpsi=3, strong=True, debug=debug)

    # Now replace each psiN in each list with all possible N with that value of psi(N)
    Nlists = sum((Nlist_from_psiNlist(s) for s in psiNlist), [])
    if debug:
        print(f"Before validity check there are {len(Nlists)} solutions")

    # Finally weed out any which fail our tests:
    ans = []
    for Nlist in Nlists:
        s = sorted(Nlist)
        if s not in ans and is_valid_Nlist(s, debug=False):
            ans.append(s)
    if debug:
        print(f"After validity check and removal of repeats there are {len(ans)} solutions")
    return ans
