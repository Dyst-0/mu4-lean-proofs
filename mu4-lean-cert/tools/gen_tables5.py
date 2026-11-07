"""GF(4^5) tables for the mu_4(5) Lean files (mu4-proof/lean, 2026-11-05, second agent).
Field: A5 = GF(4)[t]/(t^5 + t + w), GF(4) = {0,1,w,w^2} coded 0,1,2,3 as in gen_tables.py, i.e. runs/hyper/hp2.c with
-DN=5 '-DMOD5=2,1,0,0,0' (t^5 = w + t). Elements of A5: 10-bit codes, coordinate l in bits 2l, 2l+1.
Prints: pw5 (t^n for n <= 8), and writes inv_table5.txt (entry x in bits 10x..10x+9). Self-checks: irreducibility
(t^(4^5) = t and no root/quadratic factor), x * inv(x) = 1 for all 1023 nonzero x."""
import sys
sys.set_int_max_str_digits(100000)
M4 = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
MODLOW = [2,1,0,0,0]
N = 5
def polymul(a, b):
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
    for _ in range(n): v = polymul(v, [0,1,0,0,0])
    return v
pw = [tpow(n) for n in range(2*N-1)]
def dec(x): return [(x >> (2*l)) & 3 for l in range(N)]
def code(v): return sum(c << (2*l) for l, c in enumerate(v))
def mul(a, b): return code(polymul(dec(a), dec(b)))
# irreducibility: degree 5 is prime, so irreducible iff no root in GF(4) (no factor of degree 1) and no factor of
# degree 2 (a degree-5 reducible polynomial has a factor of degree 1 or 2); equivalently A5 is a field: every nonzero
# element is invertible (checked below by the inverse table).
if __name__ == '__main__':
    inv = [0]*1024
    for x in range(1, 1024):
        r, b, e = 1, x, 1022
        while e:
            if e & 1: r = mul(r, b)
            b = mul(b, b); e >>= 1
        assert mul(x, r) == 1, x
        inv[x] = r
    t = code([0,1,0,0,0]); y = t
    for _ in range(5): y = mul(mul(y, y), mul(y, y))  # y^4, five times: t^(4^5)
    assert y == t
    big = sum(inv[x] << (10*x) for x in range(1024))
    names = ['z','o','w','w2']
    for n in range(2*N-1): print(n, pw[n], '[' + ', '.join(names[c] for c in pw[n]) + ']', code(pw[n]))
    open('inv_table5.txt', 'w').write(str(big))
    print('digits', len(str(big)), 'check', all(mul(x, inv[x]) == 1 for x in range(1, 1024)))
