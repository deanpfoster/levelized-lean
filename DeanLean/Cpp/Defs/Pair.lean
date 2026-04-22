import DeanLean.Basic

namespace Cpp

structure Pair (T1 T2 : Type) where
  first : T1
  second : T2
deriving Repr, BEq, Inhabited, DecidableEq

namespace Pair

variable {T1 T2 U1 U2 : Type}

def make (a : T1) (b : T2) : Pair T1 T2 := ⟨a, b⟩

def swap (p : Pair T1 T2) : Pair T2 T1 := ⟨p.second, p.first⟩

def map_first (f : T1 → U1) (p : Pair T1 T2) : Pair U1 T2 := ⟨f p.first, p.second⟩

def map_second (f : T2 → U2) (p : Pair T1 T2) : Pair T1 U2 := ⟨p.first, f p.second⟩

def get (p : Pair T1 T2) (i : Fin 2) : T1 ⊕ T2 :=
  match i with
  | ⟨0, _⟩ => .inl p.first
  | ⟨1, _⟩ => .inr p.second

instance [Ord T1] [Ord T2] : Ord (Pair T1 T2) where
  compare a b :=
    match compare a.first b.first with
    | .eq => compare a.second b.second
    | ord => ord

def tuple_size (_ : Pair T1 T2) : Nat := 2

end Pair

def make_pair {T1 T2 : Type} (a : T1) (b : T2) : Pair T1 T2 := ⟨a, b⟩

end Cpp
