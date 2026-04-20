import DeanLean.Basic
import DeanLean.Cpp.Code.Ordering

namespace Cpp

/-! # C++ algorithms (N4950 §27.7-27.9): min/max, clamp, sorted operations

  Formalizes basic C++ algorithms from `<algorithm>` using the `StrongOrd`
  typeclass and `strongCmp` function. All operations work on the
  three-way `Cpp.Ordering` returned by `strongCmp`.

  C++ semantics: these algorithms use a strict weak ordering via `operator<`.
  We model this using `strongCmp a b != .gt` as the "less-than-or-equal"
  relation, which corresponds to `!(b < a)` in C++.
-/

/-! ## Equality-reflecting StrongOrd -/

/-- A `StrongOrd` instance where `.eq` comparison implies actual equality.
    This holds for Nat, Int, and other types with canonical representations.
    Needed for `min_comm` and `max_comm` (since distinct objects may compare equal). -/
class StrongOrdEq (T : Type) [StrongOrd T] : Prop where
  cmp_eq_imp_eq : ∀ (a b : T), StrongOrd.strongCmp a b = .eq → a = b

/-! ## The ordering relation derived from strongCmp -/

/-- `cmpLe a b` means `strongCmp a b != .gt`, i.e., `a <= b`. -/
def cmpLe {T : Type} [StrongOrd T] (a b : T) : Prop :=
  StrongOrd.strongCmp a b ≠ Ordering.gt

/-! ## §27.8.5 min -- returns the smaller of two values -/

/-- `std::min(a, b)` -- returns `a` if `a <= b`, otherwise `b`.
    C++ returns the first argument when equal (stable). -/
def cppMin {T : Type} [StrongOrd T] (a b : T) : T :=
  match StrongOrd.strongCmp a b with
  | .gt => b
  | _   => a

/-! ## §27.8.6 max -- returns the larger of two values -/

/-- `std::max(a, b)` -- returns `a` if `a >= b`, otherwise `b`.
    C++ returns the first argument when equal (stable). -/
def cppMax {T : Type} [StrongOrd T] (a b : T) : T :=
  match StrongOrd.strongCmp a b with
  | .lt => b
  | _   => a

/-! ## §27.8.8 clamp -- clamps a value to a range -/

/-- `std::clamp(v, lo, hi)` -- clamps `v` to the range `[lo, hi]`.
    Precondition: `lo <= hi` (i.e., `strongCmp lo hi != .gt`). -/
def cppClamp {T : Type} [StrongOrd T] (v lo hi : T) : T :=
  match StrongOrd.strongCmp v lo with
  | .lt => lo
  | _   =>
    match StrongOrd.strongCmp v hi with
    | .gt => hi
    | _   => v

/-! ## §27.8.5 min_element -- minimum element of a range -/

/-- `std::min_element` on a list -- returns the minimum element.
    Returns `default` on empty list. -/
def minElement {T : Type} [StrongOrd T] [Inhabited T] (l : List T) : T :=
  match l with
  | []      => default
  | x :: xs => xs.foldl (fun acc y => cppMin acc y) x

/-! ## §27.8.6 max_element -- maximum element of a range -/

/-- `std::max_element` on a list -- returns the maximum element.
    Returns `default` on empty list. -/
def maxElement {T : Type} [StrongOrd T] [Inhabited T] (l : List T) : T :=
  match l with
  | []      => default
  | x :: xs => xs.foldl (fun acc y => cppMax acc y) x

/-! ## §27.8.4 is_sorted -- checks if a range is sorted -/

/-- `std::is_sorted` on a list -- returns `true` if the list is sorted
    in non-decreasing order according to `strongCmp`. -/
def isSorted {T : Type} [StrongOrd T] : List T → Bool
  | []  => true
  | [_] => true
  | a :: b :: rest =>
    match StrongOrd.strongCmp a b with
    | .gt => false
    | _   => isSorted (b :: rest)

end Cpp
