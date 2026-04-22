import DeanLean.Basic

namespace Cpp

/-! ## Variant2: tagged union of 2 types (models std::variant<T1,T2>) -/

inductive Variant2 (T1 T2 : Type) where
  | first  (val : T1) : Variant2 T1 T2
  | second (val : T2) : Variant2 T1 T2
deriving Repr, BEq, Inhabited

namespace Variant2

variable {T1 T2 : Type}

-- §22.6.3.5 index(): returns the zero-based index of the active alternative
def index : Variant2 T1 T2 → Fin 2
  | first _  => ⟨0, by omega⟩
  | second _ => ⟨1, by omega⟩

-- §22.6.5 holds_alternative: check if a specific alternative (by index) is active
def holds_alternative (v : Variant2 T1 T2) (i : Fin 2) : Bool :=
  v.index == i

-- §22.6.5 get (by index): extract value with proof of correct alternative
def get_first (v : Variant2 T1 T2) (h : v.index = ⟨0, by omega⟩) : T1 :=
  match v, h with
  | first val, _ => val

def get_second (v : Variant2 T1 T2) (h : v.index = ⟨1, by omega⟩) : T2 :=
  match v, h with
  | second val, _ => val

-- §22.6.3.4 valueless_by_exception: in our pure setting, always false
def valueless_by_exception (_ : Variant2 T1 T2) : Bool := false

-- §22.6.7 visit: apply a visitor function to the held value
def visit {R : Type} (f1 : T1 → R) (f2 : T2 → R) : Variant2 T1 T2 → R
  | first v  => f1 v
  | second v => f2 v

-- variant_size: number of alternatives
def variant_size (_ : Variant2 T1 T2) : Nat := 2

end Variant2

/-! ## Variant3: tagged union of 3 types (models std::variant<T1,T2,T3>) -/

inductive Variant3 (T1 T2 T3 : Type) where
  | first  (val : T1) : Variant3 T1 T2 T3
  | second (val : T2) : Variant3 T1 T2 T3
  | third  (val : T3) : Variant3 T1 T2 T3
deriving Repr, BEq, Inhabited

namespace Variant3

variable {T1 T2 T3 : Type}

-- §22.6.3.5 index()
def index : Variant3 T1 T2 T3 → Fin 3
  | first _  => ⟨0, by omega⟩
  | second _ => ⟨1, by omega⟩
  | third _  => ⟨2, by omega⟩

-- §22.6.5 holds_alternative
def holds_alternative (v : Variant3 T1 T2 T3) (i : Fin 3) : Bool :=
  v.index == i

-- §22.6.5 get (by index): extract with proof
def get_first (v : Variant3 T1 T2 T3) (h : v.index = ⟨0, by omega⟩) : T1 :=
  match v, h with
  | first val, _ => val

def get_second (v : Variant3 T1 T2 T3) (h : v.index = ⟨1, by omega⟩) : T2 :=
  match v, h with
  | second val, _ => val

def get_third (v : Variant3 T1 T2 T3) (h : v.index = ⟨2, by omega⟩) : T3 :=
  match v, h with
  | third val, _ => val

-- §22.6.3.4 valueless_by_exception
def valueless_by_exception (_ : Variant3 T1 T2 T3) : Bool := false

-- §22.6.7 visit
def visit {R : Type} (f1 : T1 → R) (f2 : T2 → R) (f3 : T3 → R) : Variant3 T1 T2 T3 → R
  | first v  => f1 v
  | second v => f2 v
  | third v  => f3 v

-- variant_size
def variant_size (_ : Variant3 T1 T2 T3) : Nat := 3

end Variant3

end Cpp
