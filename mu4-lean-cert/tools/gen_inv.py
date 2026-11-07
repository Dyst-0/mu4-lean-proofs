"""Inverse table of GF(4^6) on 12-bit codes, packed into one natural number (entry x in bits 12x..12x+11).
Used by lean/Mu4/GFField.lean; the Lean kernel re-checks x * inv(x) = 1 for every nonzero x."""
import sys
sys.set_int_max_str_digits(100000)
sys.path.insert(0, '.')
from gen_tables import polymul, pw
def dec(x): return [(x >> (2*l)) & 3 for l in range(6)]
def code(v): return sum(c << (2*l) for l, c in enumerate(v))
def mul(a, b): return code(polymul(dec(a), dec(b)))
inv = [0]*4096
for x in range(1, 4096):
    # x^4094 by square and multiply
    r, b, e = 1, x, 4094
    while e:
        if e & 1: r = mul(r, b)
        b = mul(b, b); e >>= 1
    assert mul(x, r) == 1
    inv[x] = r
big = sum(inv[x] << (12*x) for x in range(4096))
print('pwC', [code(pw[n]) for n in range(11)])
open('inv_table.txt', 'w').write(str(big))
print('digits', len(str(big)), 'inv[2]', inv[2], 'check', all(mul(x, inv[x]) == 1 for x in range(1, 4096)))
