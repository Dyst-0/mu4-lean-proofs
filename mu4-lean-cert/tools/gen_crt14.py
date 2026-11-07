"""An explicit 14-term (symmetric) bilinear scheme for multiplication in A = GF(4)[t]/(t^6+t^2+t+w), built from
scratch for the Lean upper bound (lean/Mu4/Upper.lean): CRT for the product of two polynomials of degree <= 5 with
the places t = 0, 1, w, w^2 (1 product each), three irreducible quadratics (Karatsuba, 3 products each) and infinity
(x5*y5), then reduction mod t^6+t^2+t+w. The output vectors c_r are solved by linear algebra over GF(4) and the whole
scheme is re-verified on all 36 basis pairs. Output: rows a_r (= b_r) and c_r as lists of GF(4) codes (0,1,2,3 = 0,1,w,w^2)."""
from gen_tables import M4, polymul, pw
ADD = lambda a, b: a ^ b
INV4 = [0, 1, 3, 2]
def ev(a, t):                       # value at t of the form x -> x(t), as a coefficient row
    row, p = [], 1
    for i in range(6): row.append(p); p = M4[p][t]
    return row
def polymod_row(q, i):              # t^i mod q (q monic quadratic t^2 + al t + be): coefficients (c0, c1)
    al, be = q
    c = [1, 0]
    for _ in range(i):              # multiply by t: (c0 + c1 t) t = c0 t + c1 t^2 = -be c1 + (c0 - al c1) t
        c = [M4[be][c[1]], c[0] ^ M4[al][c[1]]]
    return c
quads = [(al, be) for al in range(4) for be in range(1, 4) if all((M4[t][t] ^ M4[al][t] ^ be) != 0 for t in range(4))]
Q = quads[:3]
rows = []                            # the 14 forms a_r on coordinates x_0..x_5
for t in range(4): rows.append(ev(None, t))
for q in Q:
    u0 = [polymod_row(q, i)[0] for i in range(6)]; u1 = [polymod_row(q, i)[1] for i in range(6)]
    rows += [u0, u1, [a ^ b for a, b in zip(u0, u1)]]
rows.append([0, 0, 0, 0, 0, 1])
assert len(rows) == 14
def dot(r, v):
    s = 0
    for a, b in zip(r, v): s ^= M4[a][b]
    return s
# Solve sum_r a_r(e_i) a_r(e_j) c_r = e_i e_j  (36 x 6 equations, unknowns c_r, 14 x 6)
E = [[1 if k == i else 0 for k in range(6)] for i in range(6)]
eqs = []                             # each equation: coefficients over the 14 unknown vectors, rhs vector
for i in range(6):
    for j in range(6):
        eqs.append(([M4[rows[r][i]][rows[r][j]] for r in range(14)], pw[i + j][:]))
# Gaussian elimination on the 14 unknowns (vector-valued rhs)
piv = {}
eqs = [(list(c), list(v)) for c, v in eqs]
used = [False] * len(eqs)
for col in range(14):
    p = next((e for e in range(len(eqs)) if not used[e] and eqs[e][0][col]), None)
    if p is None: continue
    used[p] = True; iv = INV4[eqs[p][0][col]]
    eqs[p] = ([M4[iv][a] for a in eqs[p][0]], [M4[iv][a] for a in eqs[p][1]])
    for e in range(len(eqs)):
        if e != p and eqs[e][0][col]:
            f = eqs[e][0][col]
            eqs[e] = ([a ^ M4[f][b] for a, b in zip(eqs[e][0], eqs[p][0])], [a ^ M4[f][b] for a, b in zip(eqs[e][1], eqs[p][1])])
    piv[col] = p
for e in range(len(eqs)):            # consistency: no equation 0 = nonzero
    if not any(eqs[e][0]): assert not any(eqs[e][1]), 'inconsistent'
assert len(piv) == 14, len(piv)
C = [eqs[piv[r]][1] for r in range(14)]
# verify on all basis pairs
for i in range(6):
    for j in range(6):
        s = [0]*6
        for r in range(14):
            cc = M4[rows[r][i]][rows[r][j]]
            for k in range(6): s[k] ^= M4[cc][C[r][k]]
        assert s == pw[i + j], (i, j)
print('quadratics (al, be):', Q)
print('A_ROWS', rows)
print('C_ROWS', C)
print('verified: sum_r a_r(e_i) a_r(e_j) c_r = e_i e_j for all 36 pairs')
