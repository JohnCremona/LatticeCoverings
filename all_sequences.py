from sage.all import primes
from refine_sequences import refine_sequence

@cached_function
def all_sequences(n, norepeats=True):
    if n<=0:
        return []
    if n==1:
        return [[1]]
    ans = []
    for p in primes(n): ## all p < n
        for S in all_sequences(n-p, norepeats):
            for T in refine_sequence(S, p, -1, norepeats):
                try:
                    T.sort()
                except:
                    pass
                if T not in ans:
                    ans.append(T)
        for S in all_sequences(n-p+1, norepeats):
            for T in refine_sequence(S, p, +1, norepeats):
                try:
                    T.sort()
                except:
                    pass
                if T not in ans:
                    ans.append(T)
    print(f"all_sequences({n}) returns {ans}")
    return ans #[T[0] for T in ans]
