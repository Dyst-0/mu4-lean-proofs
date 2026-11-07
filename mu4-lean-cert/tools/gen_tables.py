"""Generate the GF(4^6) tables used by the Lean files (mu4-proof/lean, 2026-11-05).
Field: A = GF(4)[t]/(t^6 + t^2 + t + w), GF(4) = {0,1,w,w^2} coded 0,1,2,3 (code d0 + 2 d1 = d0 + d1 w), as in
runs/hyper/hp2.c (MODLOW = {2,1,1,0,0,0}). Elements of A: 12-bit codes, coordinate l in bits 2l, 2l+1 (hp2.c's coding)."""
M4 = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
MODLOW = [2,1,1,0,0,0]          # t^6 = sum MODLOW[i] t^i
N = 6
def polymul(a, b):              # a, b: lists of N coefficients
    c = [0]*(2*N-1)
    for i in range(N):
        for j in range(N):
            c[i+j] ^= M4[a[i]][b[j]]
    for d in range(2*N-2, N-1, -1):
        t = c[d]
        if t:
            c[d] = 0
            for i in range(N):
                if MODLOW[i]: c[d-N+i] ^= M4[t][MODLOW[i]]
    return c[:N]
def tpow(n):
    v = [1]+[0]*(N-1)
    for _ in range(n): v = polymul(v, [0,1,0,0,0,0])
    return v
pw = [tpow(n) for n in range(11)]
if __name__ == '__main__':
    names = ['z','o','w','w2']
    for n in range(11): print(n, pw[n], '[' + ', '.join(names[c] for c in pw[n]) + ']')
    # cross-check against hp2.c's polymul on 12-bit codes
    def code(v): return sum(c << (2*l) for l, c in enumerate(v))
    def dec(x): return [(x >> (2*l)) & 3 for l in range(N)]
    import random
    rng = random.Random(1)
    for _ in range(2000):
        a, b = rng.randrange(4096), rng.randrange(4096)
        lhs = code(polymul(dec(a), dec(b)))
        rhs = 0
        for i in range(N):
            for j in range(N):
                cc = M4[dec(a)[i]][dec(b)[j]]
                if cc:
                    for k in range(N): rhs ^= M4[cc][pw[i+j][k]] << (2*k)
        assert lhs == rhs
    print('structure-constant multiplication agrees with polymul on 2000 random pairs')
