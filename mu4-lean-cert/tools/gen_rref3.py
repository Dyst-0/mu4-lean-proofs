"""Witness table for rref_cover3 (mu_4(5) certificate, second agent 11-05): for every pair (u, u') of 6-bit codes
(vectors of GF(4)^3) that is linearly independent, the index i of a reduced echelon pair K_i = (r0, r1) of rrefPairs3
and coefficient codes ab, cd with r0 = a u + b u', r1 = c u + d u' (a = ab & 3, b = ab >> 2, ...). Entry
64 u + u' = (i << 8) | (ab << 4) | cd in 16 bits; 0 for dependent pairs. The Lean kernel re-checks every entry."""
import sys
sys.set_int_max_str_digits(100000)
M4 = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
def coord(x, l): return (x >> (2*l)) & 3
def smul(c, x): return sum(M4[c][coord(x, l)] << (2*l) for l in range(3))
def first_nz(x):
    for l in range(3):
        if coord(x, l): return l
    return None
rref = []
for r0 in range(64):
    for r1 in range(64):
        p, q = first_nz(r0), first_nz(r1)
        if p is not None and q is not None and p < q and coord(r0, p) == 1 and coord(r1, q) == 1 and coord(r0, q) == 0:
            rref.append((r0, r1))
assert len(rref) == 21
def lin(ab, u, v): return smul(ab & 3, u) ^ smul(ab >> 2, v)
def indep(u, v): return all(ab == 0 or lin(ab, u, v) % 64 != 0 for ab in range(16))
tab = [0]*4096
for u in range(64):
    for v in range(64):
        if not indep(u, v): continue
        span = {lin(ab, u, v): ab for ab in range(16)}
        w = next((i, span[r0], span[r1]) for i, (r0, r1) in enumerate(rref) if r0 in span and r1 in span)
        tab[64*u + v] = (w[0] << 8) | (w[1] << 4) | w[2]
for u in range(64):
    for v in range(64):
        if indep(u, v):
            e = tab[64*u+v]; i, ab, cd = e >> 8, (e >> 4) & 15, e & 15
            assert lin(ab, u, v) == rref[i][0] and lin(cd, u, v) == rref[i][1]
print('rref3', rref)
print('table', sum(tab[k] << (16*k) for k in range(4096)))
