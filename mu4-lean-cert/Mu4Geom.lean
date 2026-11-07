import Mu4Comp.Codes

/-!
# The search for G1 (core Lean only)

G1 (`audit/PROOF.md`): no 12 points of PG(4,4) have every 4 of them independent.

Codes of `GF(4)^5` are those of `Mu4Comp/Codes.lean` restricted to the coordinates `0..4`
(bits `0..9`). `points` lists the 341 normalized nonzero codes (first nonzero coordinate 1),
increasing. The search mirrors `runs/hyper/main_check/geom_main.c`:

* the five chosen points `e_0, …, e_4` come first (`cur0`), with the planes through three of
  them marked (`f0`);
* `noExt k cur f cands = true` says that no `k` points of `cands`, taken in increasing order,
  can be added to `cur` one by one so that each new point is unmarked when it is added; adding
  `p` marks every code of `span{p, a, b}` for `a, b` in `cur` (`addPoint`).

The soundness of the search is proved in `Mu4/Lower/Geometry.lean`. This is a library of its own
(core Lean only, `precompileModules`), so that adding it left the shared library of `Mu4Comp`,
whose hash is in the traces of the C3 check modules, unchanged.
-/

namespace Mu4.Geom
open Mu4 F4

/-- The four elements of GF(4). -/
def allF4 : List F4 := [z, o, w, w2]

/-- The first nonzero coordinate among `0..4` (`z` if there is none). -/
def firstCoord (x : Nat) : F4 :=
  if coordC x 0 ≠ z then coordC x 0 else
  if coordC x 1 ≠ z then coordC x 1 else
  if coordC x 2 ≠ z then coordC x 2 else
  if coordC x 3 ≠ z then coordC x 3 else coordC x 4

/-- Scale a code so that its first nonzero coordinate is 1. -/
def normC (x : Nat) : Nat := smulC (F4.inv (firstCoord x)) x

/-- The points of PG(4,4): the normalized nonzero codes below `4^5`, increasing. -/
def points : List Nat := (List.range 1024).filter fun x => x != 0 && normC x == x

/-- The four multiples `0, x, ω x, ω² x` of a code. -/
def mults (x : Nat) : List Nat := allF4.map fun r => smulC r x

/-- Mark every code of `span{a, b, c}` (the multiples are computed once: `mulw` builds its
64-bit mask from a decimal literal at every call in the compiled code). -/
def markPlane (f : Array Bool) (a b c : Nat) : Array Bool :=
  let mb := mults b
  let mc := mults c
  (mults a).foldl (fun f ra => mb.foldl (fun f sb => let rsab := ra ^^^ sb
    mc.foldl (fun f tc => f.setIfInBounds (rsab ^^^ tc) true) f) f) f

/-- Add `p` to the chosen points `cur`: mark the planes through `p` and two points of `cur`. -/
def addPoint (f : Array Bool) (p : Nat) : List Nat → Array Bool
  | [] => f
  | a :: rest => addPoint (rest.foldl (fun f b => markPlane f p a b) f) p rest

/-- No `k` points of `cands`, in order, extend `cur` (each unmarked when it is added). -/
def noExt : Nat → List Nat → Array Bool → List Nat → Bool
  | 0, _, _, _ => false
  | _ + 1, _, _, [] => true
  | k + 1, cur, f, p :: rest =>
      (f.getD p false || noExt k (p :: cur) (addPoint f p cur) rest) && noExt (k + 1) cur f rest

/-- Add the points of a list one by one, starting from `(f, cur)`. -/
def addAll : List Nat → Array Bool × List Nat → Array Bool × List Nat
  | [], acc => acc
  | p :: ps, (f, cur) => addAll ps (addPoint f p cur, p :: cur)

/-- The standard basis `e_0, …, e_4` of `GF(4)^5`. -/
def basis5 : List Nat := [1, 4, 16, 64, 256]

/-- The basis as chosen points, with its marks. -/
def start : Array Bool × List Nat := addAll basis5 (Array.replicate 1024 false, [])

/-- G1 as a search: no `k` further points extend the basis (G1 is `geomCheck 7 = true`). The
argument keeps the search out of the closed constants that a precompiled module computes when it
is loaded. -/
def geomCheck (k : Nat) : Bool := noExt k start.2 start.1 points

/-- Diagnostic, not used by the proof: the number of nodes below `cur` in the search tree and
the largest size of `cur` reached (to compare with `geom_main.c`). -/
def treeSize : Nat → List Nat → Array Bool → List Nat → Nat × Nat
  | 0, cur, _, _ => (0, cur.length)
  | _ + 1, cur, _, [] => (0, cur.length)
  | k + 1, cur, f, p :: rest =>
      let r := treeSize (k + 1) cur f rest
      if f.getD p false then r
      else
        let c := treeSize k (p :: cur) (addPoint f p cur) rest
        (r.1 + c.1 + 1, max r.2 c.2)

end Mu4.Geom
