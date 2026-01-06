from sage.all import ZZ, deepcopy
def refine_sequence(S, p, div=0, norepeats=True):
    """
    S is a nested list of lists of indices, p a prime. Returns a list of refined lists S'
    obtained by replacing each integer N in S by either [N*p]*p or [N*p]*(p+1) depending
    on whether p|N or not.

    If div is 1 only do this for p|N, if div is -1 only do this
    for p~|N, else (div=0) do it for either.

    If norepeats is True, only make the substitutions for the first of each different entry in the sequence.
    """
    ans = []
    Si_done = []
    for i, Si in enumerate(S):
        if Si not in ZZ and len(Si)==1:
            Si=Si[0]
        print(f"{p}-refining {Si} from {S}")
        if norepeats and Si in Si_done:
            print(" - repeat, ignoring")
            continue
        Si_done.append(Si)
        # Si is either an integer or another (possibly nested) list
        if Si in ZZ:
            N = Si
            if p.divides(N):
                if div>=0:
                    copyS = deepcopy(S)
                    copyS[i] = [p*N for _ in range(p)]
                    #print(f"replaced {Si} with {copyS[i]}")
                    ans.append(copyS)
            else:
                if div<=0:
                    copyS = deepcopy(S)
                    copyS[i] = [p*N for _ in range(p+1)]
                    #print(f"replaced {Si} with {copyS[i]}")
                    #print(f"old S: {S}")
                    #print(f"new S: {copyS}")
                    ans.append(copyS)
        else: # Si is another list, use recursion
            for sub in refine_sequence(Si, p, div, norepeats):
                copyS = deepcopy(S)
                copyS[i] = sub
                #print(f"replaced {Si} with {sub}")
                ans.append(copyS)
    for a in ans:
        for i,ai in enumerate(a):
            if ai not in ZZ and len(ai)==1:
                a[i] = ai[0]
    print(f"The {p}-refinements of {S} with {div=} are \n{ans}")
    return ans
