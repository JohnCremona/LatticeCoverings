# pvg.py:  utilities for generating primitive vectors

from sage.all import ZZ, QQ, FreeModule, cached_function, Gamma0, P1List

V = FreeModule(ZZ,2)
TrivialModule = V.zero_submodule()

def wedge(v,w):
    """
    The wedge product of v=(a,b) and w=(c,d), that is, a*d-b*c
    """
    a,b = v
    c,d = w
    return a*d-b*c

# A list of primitive vectors, no longer used

PointList = [V((1, 0)), V((0, 1)), V((1, 1)), V((1, -1)), V((1, 2)),
             V((2, 1)), V((1, 3)), V((3, 1)), V((1, -3)), V((3, -1)), V((1, 4)),
             V((2, 3)), V((3, 2)), V((4, 1)), V((1, -4)), V((2, -3)), V((3, -2)),
             V((4, -1)), V((5, 1)), V((1, 5)), V((5, -1)), V((1, -5)), V((1, 6)),
             V((2, 5)), V((3, 4)), V((4, 3)), V((5, 2)), V((6, 1)), V((1, 7)),
             V((3, 5)), V((5, 3)), V((7, 1)), V((1, 8)), V((2, 7)), V((4, 5)),
             V((5, 4)), V((7, 2)), V((8, 1)), V((1, 9)), V((3, 7)), V((7, 3)),
             V((9, 1)), V((1, 10)), V((2, 9)), V((3, 8)), V((4, 7)), V((5, 6)),
             V((6, 5)), V((7, 4)), V((8, 3)), V((9, 2)), V((10, 1)), V((1, 11)),
             V((5, 7)), V((7, 5)), V((11, 1)), V((1, 12)), V((2, 11)), V((3, 8)),
             V((4, 7)), V((5, 8)), V((6, 7)), V((7, 6)), V((8, 5)), V((9, 4)),
             V((10, 3)), V((11, 2)), V((12, 1)), V((1, 13)), V((3, 11)), V((5, 9)),
             V((9, 5)), V((11, 3)), V((13, 1)), V((1, 14)), V((2, 13)), V((4, 11)),
             V((7, 8)), V((8, 7)), V((11, 4)), V((13, 2)), V((14, 1)), V((1, 15)),
             V((3, 13)), V((5, 11)), V((7, 9)), V((9, 7)), V((11, 5)), V((13, 3)),
             V((15, 1)), V((1, 16)), V((8, 9)), V((9, 8)), V((16, 1)), V((2, 15)),
             V((1, 30)), V((1, 17)), V((30, 1)), V((17, 1))]

def primitive_vector_generator(skip=0):
    """A generator for all primitive vectors in ZZ^2 up to sign, using
    Sage's generator of rational numbers (in order of height).

    To use this set pvg=primitive_vector_generator() and then
    v=next(pvg) will deliver the vectors (ad infinitum).

    Setting pvg=primitive_vector_generator(n) automatically skips the
    first n vectors so the first next(svg) will be the (n+1)st.

    """
    if skip==0:
        yield V((1,0)) # special case as 1/0 is not in QQ
    n = 0
    for r in QQ:
        n += 1
        if n>=skip:
            yield V((r.numerator(), r.denominator()))

# Sage has a built-in function for generating P^1(N) as a list of
# pairs (c,d) (as these are used for modular symbol computations).

@cached_function
def P1(N):
    return P1List(N)

@cached_function
def psi(N):
    """
    Return the value of psi(N) = #P(Z/NZ).
    """
    return Gamma0(N).index() if N else 0

