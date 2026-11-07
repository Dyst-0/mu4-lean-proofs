"""An explicit 11-term (symmetric) bilinear scheme for multiplication in A5 = GF(4)[t]/(t^5+t+w), built from scratch
for the Lean upper bound of mu_4(5) (lean/Mu4/N5/Upper5.lean; second agent, 11-05): CRT for the product of two
polynomials of degree <= 4 with the places t = 0, 1, w, w^2 (1 product each), two irreducible quadratics (Karatsuba,
3 products each) and infinity (x4*y4), then reduction mod t^5+t+w. The output vectors c_r are solved by linear algebra
over GF(4) and the scheme is re-verified on all 25 basis pairs. Output: rows a_r (= b_r) and c_r as GF(4) codes."""
import sys
sys.path.insert(0, '.')
from gen_tables5 import M4, polymul, pw
N = 5
INV4 = [0, 1, 3, 2]
def ev(t):                          # the form x -> x(t), as a coefficient row
    row, p = [], 1
    for i in range(N): row.append(p); p = M4[p][t]
    return row
def polymod_row(q, i):              # t^i mod q (q monic quadratic t^2 + al t + be): coefficients (c0, c1)
    al, be = q
    c = [1, 0]
    for _ in range(i):
        c = [M4[be][c[1]], c[0] ^ M4[al][c[1]]]
    return c
quads = [(al, be) for al in range(4) for be in range(1, 4) if all((M4[t][t] ^ M4[al][t] ^ be) != 0 for t in range(4))]
Q = quads[:2]
rows = []
for t in range(4): rows.append(ev(t))
for q in Q:
    u0 = [polymod_row(q, i)[0] for i in range(N)]; u1 = [polymod_row(q, i)[1] for i in range(N)]
    rows += [u0, u1, [a ^ b for a, b in zip(u0, u1)]]
rows.append([0, 0, 0, 0, 1])
R = len(rows)
assert R == 11
eqs = []
for i in range(N):
    for j in range(N):
        eqs.append(([M4[rows[r][i]][rows[r][j]] for r in range(R)], pw[i + j][:]))
piv = {}
eqs = [(list(c), list(v)) for c, v in eqs]
used = [False] * len(eqs)
for col in range(R):
    p = next((e for e in range(len(eqs)) if not used[e] and eqs[e][0][col]), None)
    if p is None: continue
    used[p] = True; iv = INV4[eqs[p][0][col]]
    eqs[p] = ([M4[iv][a] for a in eqs[p][0]], [M4[iv][a] for a in eqs[p][1]])
    for e in range(len(eqs)):
        if e != p and eqs[e][0][col]:
            f = eqs[e][0][col]
            eqs[e] = ([a ^ M4[f][b] for a, b in zip(eqs[e][0], eqs[p][0])], [a ^ M4[f][b] for a, b in zip(eqs[e][1], eqs[p][1])])
    piv[col] = p
for e in range(len(eqs)):
    if not any(eqs[e][0]): assert not any(eqs[e][1]), 'inconsistent'
C = [[0]*N for _ in range(R)]
for col, p in piv.items(): C[col] = eqs[p][1]
for i in range(N):
    for j in range(N):
        s = [0]*N
        for r in range(R):
            cc = M4[rows[r][i]][rows[r][j]]
            for k in range(N): s[k] ^= M4[cc][C[r][k]]
        assert s == pw[i + j], (i, j)
names = ['0', '1', 'w', 'w2']
print('quadratics (al, be):', Q, 'pivots', len(piv))
print('A_ROWS', [[names[c] for c in r] for r in rows])
print('C_ROWS', [[names[c] for c in r] for r in C])
print('verified: sum_r a_r(e_i) a_r(e_j) c_r = e_i e_j for all 25 pairs')
