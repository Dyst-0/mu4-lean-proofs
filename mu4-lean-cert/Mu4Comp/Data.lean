/-!
# Case lists (input data of the search)

`pList`: the 10 representatives `P = span(p0, p1)` of the 2-dim subspaces of GF(4^6) under
multiplication and Galois (`runs/hyper/plist.txt`, from `runs/hyper/porbits.py`).
`sList`: the 69 representatives `Ŝ = span(s0, s1)` of the 2-dim subspaces under multiplication
(`runs/hyper/Sclasses6.txt`, `hp2 --print-S`). Elements are 12-bit codes. That these lists cover all
2-dim subspaces is proved in `Mu4/Lower/Orbits.lean`.
-/

namespace Mu4.Search

def pList : List (Nat × Nat) :=
  [(1, 1768), (1, 1304), (1, 1136), (1, 1188), (1, 2000), (1, 348), (1, 1976), (1, 92),
   (1, 1352), (1, 1960)]

def sList : List (Nat × Nat) :=
  [(1, 4), (1, 16), (1, 20), (1, 52), (1, 36), (1, 64), (1, 68), (1, 196), (1, 132), (1, 80),
   (1, 244), (1, 164), (1, 208), (1, 100), (1, 212), (1, 180), (1, 144), (1, 116), (1, 228),
   (1, 148), (1, 256), (1, 260), (1, 772), (1, 516), (1, 272), (1, 820), (1, 548), (1, 784),
   (1, 292), (1, 528), (1, 804), (1, 532), (1, 320), (1, 644), (1, 336), (1, 340), (1, 1012),
   (1, 976), (1, 372), (1, 660), (1, 708), (1, 740), (1, 756), (1, 452), (1, 468), (1, 912),
   (1, 628), (1, 2052), (1, 1040), (1, 3124), (1, 3092), (1, 1088), (1, 2180), (1, 1104),
   (1, 2228), (1, 1140), (1, 1156), (1, 2244), (1, 1168), (1, 3856), (1, 1316), (1, 1344),
   (1, 2692), (1, 2740), (1, 2772), (1, 2644), (1, 1588), (1, 2996), (1, 3668)]

end Mu4.Search
