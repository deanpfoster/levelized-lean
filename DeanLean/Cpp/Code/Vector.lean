import DeanLean.Basic

namespace Cpp

/-- `Vector T` models C++ `std::vector<T>` (§24.3.11) as a wrapper around `Array T`. -/
structure Vector (T : Type) where
  data : Array T
deriving Repr, BEq, Inhabited, DecidableEq

namespace Vector

variable {T : Type}

/-- Default-constructed vector (empty). -/
def empty : Vector T := ⟨#[]⟩

/-- Number of elements (§24.3.11.3). -/
def size (v : Vector T) : Nat := v.data.size

/-- Whether the vector is empty (§24.3.11.3). -/
def isEmpty (v : Vector T) : Bool := v.data.isEmpty

/-- Remove all elements (§24.3.11.3). -/
def clear (_ : Vector T) : Vector T := ⟨#[]⟩

/-- Append an element at the end (§24.3.11.5). -/
def push_back (v : Vector T) (x : T) : Vector T := ⟨v.data.push x⟩

/-- Remove the last element (§24.3.11.5). Requires non-empty. -/
def pop_back (v : Vector T) : Vector T := ⟨v.data.pop⟩

/-- Indexed access with bounds proof (§24.3.11.4). -/
def get (v : Vector T) (i : Fin v.size) : T := v.data[i.val]'(i.isLt)

/-- Access the first element (§24.3.11.4). Requires non-empty. -/
def front (v : Vector T) (h : v.size > 0) : T := v.data[0]'h

/-- Access the last element (§24.3.11.4). Requires non-empty. -/
def back (v : Vector T) (h : v.size > 0) : T :=
  v.data[v.data.size - 1]'(by simp [size] at h; omega)

/-- Insert element at position `i`, shifting subsequent elements right. -/
def insert (v : Vector T) (i : Nat) (x : T) (_h : i ≤ v.size) : Vector T :=
  let left := v.data.extract 0 i
  let right := v.data.extract i v.size
  ⟨(left.push x) ++ right⟩

/-- Erase element at position `i`, shifting subsequent elements left. -/
def erase (v : Vector T) (i : Nat) (h : i < v.size) : Vector T :=
  ⟨v.data.eraseIdx i h⟩

/-- Construct a vector from a list. -/
def ofList (l : List T) : Vector T := ⟨l.toArray⟩

/-- Construct a vector from an array. -/
def ofArray (a : Array T) : Vector T := ⟨a⟩

/-- Convert vector to list. -/
def toList (v : Vector T) : List T := v.data.toList

/-- Convert vector to array. -/
def toArray (v : Vector T) : Array T := v.data

instance : EmptyCollection (Vector T) := ⟨Vector.empty⟩

end Vector

end Cpp
