## lam is a VectorPartition
def SetPartitionOfType(lam,u):
    uFirst = [1+sum(u[:i]) for i in range(len(u))]
    pi = len(lam)*[[]]
    for j,vec in enumerate(lam):
        for i,x in enumerate(vec):
            pi[j] = pi[j] + list(range(uFirst[i],uFirst[i]+x))
            uFirst[i] = uFirst[i]+x
    return pi