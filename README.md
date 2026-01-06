# Code to accompany the paper *Lattice coverings and homogeneous covering congruences* by John Cremona and Peter Koymans

This repository contains SageMath code to compute minimal and strongly
minimal coverings of **Z**^2 by finite collections of lattices
(subgroups of finite index), and coverings of **Z** by finite
systems of congruences.

The code has been written and tested using SageMath version 10.8.  To
run the code, one may use one of the following Jupyter notebooks,
ensuring that the kernel used is this (or a later) version:

1. Coverings_1_to_6.ipynb:  list details of all minimal lattice coverings
of sizes up to 6.
2. Coverings_7.ipynb:  list details of all minimal lattice coverings
of size 7.  Running time under 2 minutes.
3. Coverings_8.ipynb:  list details of all minimal lattice coverings
of size 8.  Running time about 4 hours.

These use the python files pvg.py (primitive vector utilities),
lattices.py (the lattice class and related utilties) and the SageMath
file coverings.sage (the main recursive function FindLattice() and
top-level function minimal_coverings().  Instead of using the Jupyter
notebooks it is also possible to load the code into any SageMath
session with the command

> %runfile coverings.sage

followed by (for example)

> minimal_coverings(6)

Two additional notebooks are included:

4. Weights.ipynb:  generate solutions to the lattice weight equation
and hence find possible index sequences for lattice coverings of
small size.
5. Congruences.ipynb: list details of minimal congruence coverings of
**Z**.


