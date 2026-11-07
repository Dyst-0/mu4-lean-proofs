/-!
# Case lists of the mu_4(5) search (input data)

`pList5`: the 3 representatives `P = span(p0, p1)` of the 2-dim subspaces of GF(4^5) under multiplication and
Galois (`runs/hyper/plist5.txt`, from `runs/hyper/porbits5.py`). `sList5`: the 17 representatives of `Ŝ` under
multiplication (`runs/hyper/ctrl5/Sclasses5.txt`, `hp2_5 --print-S`). Elements are 10-bit codes. Their coverage is
proved in `Mu4/N5/Cover.lean`.
-/

namespace Mu4.N5

def pList5 : List (Nat × Nat) := [(1, 4), (1, 20), (1, 28)]

def sList5 : List (Nat × Nat) :=
  [(1, 4), (1, 16), (1, 20), (1, 52), (1, 36), (1, 64), (1, 196), (1, 132), (1, 164), (1, 212), (1, 180),
   (1, 116), (1, 228), (1, 772), (1, 516), (1, 784), (1, 532)]

end Mu4.N5
