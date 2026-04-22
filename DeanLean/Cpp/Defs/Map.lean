import DeanLean.Cpp.Defs.Ordering

/-! # C++ sorted associative containers (N4950 §24.4)

  Formalizes simplified `std::map<K,V>` and `std::set<K>`.
  The C++ spec defines these by their INVARIANTS (sorted, unique keys),
  not their implementation. We model them using sorted `List` for provability.

  Uses `StrongOrd` for key comparison (three-way comparison with total order laws).
-/

namespace Cpp

/-! ## Sorted list predicates -/

/-- A list of keys is sorted (strictly increasing) according to `StrongOrd`. -/
def SortedKeys {K : Type} [StrongOrd K] : List K → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
    StrongOrd.strongCmp a b = .lt ∧ SortedKeys (b :: rest)

/-- A list of key-value pairs is sorted by keys (strictly increasing). -/
def SortedPairs {K : Type} {V : Type} [StrongOrd K] : List (K × V) → Prop
  | [] => True
  | [_] => True
  | (k₁, _) :: (k₂, v₂) :: rest =>
    StrongOrd.strongCmp k₁ k₂ = .lt ∧ SortedPairs ((k₂, v₂) :: rest)

/-! ## Map K V — sorted associative container (§24.4.4) -/

/-- `std::map<K,V>` — a sorted list of key-value pairs with unique keys.
    The invariant is that keys are strictly sorted according to `StrongOrd`. -/
structure Map (K : Type) (V : Type) [StrongOrd K] where
  /-- The underlying sorted list of key-value pairs -/
  entries : List (K × V)
  /-- Invariant: the entries are sorted by key -/
  sorted : SortedPairs entries

namespace Map

variable {K : Type} {V : Type} [StrongOrd K]

/-! ### Core operations -/

/-- `std::map<K,V>()` — the empty map (§24.4.4.2) -/
def empty : Map K V := ⟨[], True.intro⟩

/-- Insert a key-value pair into a sorted list, maintaining sort order.
    If the key already exists, its value is replaced. -/
def insertAux (k : K) (v : V) : List (K × V) → List (K × V)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    match StrongOrd.strongCmp k k' with
    | .lt => (k, v) :: (k', v') :: rest
    | .eq => (k, v) :: rest
    | .gt => (k', v') :: insertAux k v rest

/-- Helper lemma: the first key of insertAux result -/
private theorem insertAux_head_key (k : K) (v : V) (k' : K) (v' : V)
    (rest : List (K × V))
    (hgt : StrongOrd.strongCmp k k' = .gt) :
    insertAux k v ((k', v') :: rest) = (k', v') :: insertAux k v rest := by
  simp [insertAux, hgt]

/-- Helper: inserting into a sorted list preserves sortedness -/
theorem insertAux_sorted (k : K) (v : V) (l : List (K × V))
    (hs : SortedPairs l) : SortedPairs (insertAux k v l) := by
  induction l with
  | nil => simp [insertAux, SortedPairs]
  | cons p tl ih =>
    obtain ⟨k', v'⟩ := p
    simp only [insertAux]
    cases hcmp : StrongOrd.strongCmp k k' with
    | lt =>
      exact ⟨hcmp, hs⟩
    | eq =>
      cases tl with
      | nil => simp [SortedPairs]
      | cons q tl' =>
        obtain ⟨k'', v''⟩ := q
        have hlt : StrongOrd.strongCmp k' k'' = .lt := by
          simp only [SortedPairs] at hs; exact hs.1
        have hsrest : SortedPairs ((k'', v'') :: tl') := by
          simp only [SortedPairs] at hs; exact hs.2
        exact ⟨StrongOrd.cmp_eq_lt_trans k k' k'' hcmp hlt, hsrest⟩
    | gt =>
      cases tl with
      | nil =>
        simp only [insertAux, SortedPairs]
        exact ⟨(StrongOrd.cmp_lt_iff_gt k' k).mpr hcmp, True.intro⟩
      | cons q tl' =>
        obtain ⟨k'', v''⟩ := q
        have hlt : StrongOrd.strongCmp k' k'' = .lt := by
          simp only [SortedPairs] at hs; exact hs.1
        have hsrest : SortedPairs ((k'', v'') :: tl') := by
          simp only [SortedPairs] at hs; exact hs.2
        have ihtl : SortedPairs (insertAux k v ((k'', v'') :: tl')) := ih hsrest
        -- Now we need: SortedPairs ((k', v') :: insertAux k v ((k'', v'') :: tl'))
        -- We case split on what insertAux does to (k'', v'') :: tl'
        simp only [insertAux] at ihtl ⊢
        cases hcmp2 : StrongOrd.strongCmp k k'' with
        | lt =>
          -- insertAux returns (k,v) :: (k'', v'') :: tl'
          -- Need: cmp k' k = .lt ∧ (cmp k k'' = .lt ∧ SortedPairs ((k'', v'') :: tl'))
          -- We know cmp k k' = .gt so cmp k' k = .lt
          have hk'k : StrongOrd.strongCmp k' k = .lt :=
            (StrongOrd.cmp_lt_iff_gt k' k).mpr hcmp
          exact ⟨hk'k, hcmp2, hsrest⟩
        | eq =>
          -- insertAux returns (k,v) :: tl'
          -- Need: cmp k' k = .lt ∧ SortedPairs ((k, v) :: tl')
          -- We know cmp k k'' = .eq and cmp k' k'' = .lt
          -- So cmp k' k = cmp k' k'' trans eq... actually:
          -- cmp k k'' = .eq means k ≈ k'', and cmp k' k'' = .lt
          -- So cmp k' k = .lt by eq_lt_trans in reverse
          have hk'k : StrongOrd.strongCmp k' k = .lt := by
            have hk''k := StrongOrd.flip_eq_means_eq k k'' hcmp2
            exact StrongOrd.cmp_lt_eq_trans k' k'' k hlt hk''k
          simp only [hcmp2] at ihtl
          exact ⟨hk'k, ihtl⟩
        | gt =>
          -- insertAux returns (k'', v'') :: insertAux k v tl'
          -- Need: cmp k' k'' = .lt ∧ SortedPairs ((k'', v'') :: insertAux k v tl')
          simp only [hcmp2] at ihtl
          exact ⟨hlt, ihtl⟩

/-- `insert(k, v)` — insert or update a key-value pair (§24.4.4.3).
    If `k` already exists, its value is replaced (like `insert_or_assign`). -/
def insert (m : Map K V) (k : K) (v : V) : Map K V :=
  ⟨insertAux k v m.entries, insertAux_sorted k v m.entries m.sorted⟩

/-- Find a key in a sorted list of pairs. -/
def findAux (k : K) : List (K × V) → Option V
  | [] => none
  | (k', v') :: rest =>
    match StrongOrd.strongCmp k k' with
    | .lt => none
    | .eq => some v'
    | .gt => findAux k rest

/-- `find(k)` — look up a key in the map (§24.4.4.5).
    Returns `some v` if found, `none` otherwise. -/
def find (m : Map K V) (k : K) : Option V :=
  findAux k m.entries

/-- Erase a key from a sorted list. -/
def eraseAux (k : K) : List (K × V) → List (K × V)
  | [] => []
  | (k', v') :: rest =>
    match StrongOrd.strongCmp k k' with
    | .lt => (k', v') :: rest
    | .eq => rest
    | .gt => (k', v') :: eraseAux k rest

/-- Helper: erasing from a sorted list preserves sortedness -/
theorem eraseAux_sorted (k : K) (l : List (K × V))
    (hs : SortedPairs l) : SortedPairs (eraseAux k l) := by
  induction l with
  | nil => simp [eraseAux, SortedPairs]
  | cons p tl ih =>
    obtain ⟨k', v'⟩ := p
    simp only [eraseAux]
    cases hcmp : StrongOrd.strongCmp k k' with
    | lt => exact hs
    | eq =>
      cases tl with
      | nil => exact True.intro
      | cons q tl' =>
        simp only [SortedPairs] at hs
        exact hs.2
    | gt =>
      cases tl with
      | nil => simp [eraseAux, SortedPairs]
      | cons q tl' =>
        obtain ⟨k'', v''⟩ := q
        have hlt : StrongOrd.strongCmp k' k'' = .lt := by
          simp only [SortedPairs] at hs; exact hs.1
        have hsrest : SortedPairs ((k'', v'') :: tl') := by
          simp only [SortedPairs] at hs; exact hs.2
        have ihtl := ih hsrest
        simp only [eraseAux] at ihtl ⊢
        cases hcmp2 : StrongOrd.strongCmp k k'' with
        | lt =>
          -- eraseAux returns (k'', v'') :: tl' (unchanged)
          exact ⟨hlt, hsrest⟩
        | eq =>
          -- eraseAux returns tl'
          -- Need: SortedPairs ((k', v') :: tl')
          simp only [hcmp2] at ihtl
          cases tl' with
          | nil => exact True.intro
          | cons r tl'' =>
            obtain ⟨k''', v'''⟩ := r
            have hlt2 : StrongOrd.strongCmp k'' k''' = .lt := by
              simp only [SortedPairs] at hsrest; exact hsrest.1
            have hsrest2 : SortedPairs ((k''', v''') :: tl'') := by
              simp only [SortedPairs] at hsrest; exact hsrest.2
            exact ⟨StrongOrd.cmp_lt_trans k' k'' k''' hlt hlt2, hsrest2⟩
        | gt =>
          -- eraseAux returns (k'', v'') :: eraseAux k tl'
          simp only [hcmp2] at ihtl
          exact ⟨hlt, ihtl⟩

/-- `erase(k)` — remove a key from the map (§24.4.4.6). -/
def erase (m : Map K V) (k : K) : Map K V :=
  ⟨eraseAux k m.entries, eraseAux_sorted k m.entries m.sorted⟩

/-- `contains(k)` — check if a key exists (§24.4.4.5). -/
def contains (m : Map K V) (k : K) : Bool :=
  match m.find k with
  | some _ => true
  | none => false

/-- `size()` — number of elements in the map (§24.4.4.1). -/
def size (m : Map K V) : Nat :=
  m.entries.length

/-- `keys()` — extract the sorted list of keys. -/
def keys (m : Map K V) : List K :=
  m.entries.map Prod.fst

/-- `values()` — extract the list of values (in key order). -/
def values (m : Map K V) : List V :=
  m.entries.map Prod.snd

end Map

/-! ## Set K — sorted set (§24.4.3) -/

/-- `std::set<K>` — a sorted list of unique elements.
    The invariant is that elements are strictly sorted according to `StrongOrd`. -/
structure CppSet (K : Type) [StrongOrd K] where
  /-- The underlying sorted list of elements -/
  elems : List K
  /-- Invariant: elements are sorted -/
  sorted : SortedKeys elems

namespace CppSet

variable {K : Type} [StrongOrd K]

/-! ### Core operations -/

/-- The empty set (§24.4.3.2) -/
def empty : CppSet K := ⟨[], True.intro⟩

/-- Insert an element into a sorted list, maintaining sort order.
    No-op if the element already exists. -/
def insertAux (k : K) : List K → List K
  | [] => [k]
  | k' :: rest =>
    match StrongOrd.strongCmp k k' with
    | .lt => k :: k' :: rest
    | .eq => k' :: rest
    | .gt => k' :: insertAux k rest

/-- Helper: inserting into a sorted list preserves sortedness -/
theorem insertAux_sorted (k : K) (l : List K)
    (hs : SortedKeys l) : SortedKeys (insertAux k l) := by
  induction l with
  | nil => simp [insertAux, SortedKeys]
  | cons k' tl ih =>
    simp only [insertAux]
    cases hcmp : StrongOrd.strongCmp k k' with
    | lt =>
      exact ⟨hcmp, hs⟩
    | eq => exact hs
    | gt =>
      cases tl with
      | nil =>
        simp only [insertAux, SortedKeys]
        exact ⟨(StrongOrd.cmp_lt_iff_gt k' k).mpr hcmp, True.intro⟩
      | cons k'' tl' =>
        have hlt : StrongOrd.strongCmp k' k'' = .lt := by
          simp only [SortedKeys] at hs; exact hs.1
        have hsrest : SortedKeys (k'' :: tl') := by
          simp only [SortedKeys] at hs; exact hs.2
        have ihtl : SortedKeys (insertAux k (k'' :: tl')) := ih hsrest
        simp only [insertAux] at ihtl ⊢
        cases hcmp2 : StrongOrd.strongCmp k k'' with
        | lt =>
          have hk'k : StrongOrd.strongCmp k' k = .lt :=
            (StrongOrd.cmp_lt_iff_gt k' k).mpr hcmp
          exact ⟨hk'k, hcmp2, hsrest⟩
        | eq =>
          have hk'k : StrongOrd.strongCmp k' k = .lt := by
            have hk''k := StrongOrd.flip_eq_means_eq k k'' hcmp2
            exact StrongOrd.cmp_lt_eq_trans k' k'' k hlt hk''k
          simp only [hcmp2] at ihtl
          -- For Set, .eq means keep the existing element k'
          -- insertAux returns k' :: tl' (unchanged for .eq)
          -- But wait, let's check: ihtl is about insertAux k (k'' :: tl')
          -- With hcmp2 = .eq, insertAux k (k'' :: tl') = k'' :: tl'
          -- So we need SortedKeys (k' :: k'' :: tl') = hs
          exact hs
        | gt =>
          simp only [hcmp2] at ihtl
          exact ⟨hlt, ihtl⟩

/-- `insert(k)` — insert an element (§24.4.3.3). -/
def insert (s : CppSet K) (k : K) : CppSet K :=
  ⟨insertAux k s.elems, insertAux_sorted k s.elems s.sorted⟩

/-- Find an element in a sorted list. -/
def findAux (k : K) : List K → Bool
  | [] => false
  | k' :: rest =>
    match StrongOrd.strongCmp k k' with
    | .lt => false
    | .eq => true
    | .gt => findAux k rest

/-- `contains(k)` — check if an element exists (§24.4.3.5). -/
def contains (s : CppSet K) (k : K) : Bool :=
  findAux k s.elems

/-- Erase an element from a sorted list. -/
def eraseAux (k : K) : List K → List K
  | [] => []
  | k' :: rest =>
    match StrongOrd.strongCmp k k' with
    | .lt => k' :: rest
    | .eq => rest
    | .gt => k' :: eraseAux k rest

/-- Helper: erasing from a sorted list preserves sortedness -/
theorem eraseAux_sorted (k : K) (l : List K)
    (hs : SortedKeys l) : SortedKeys (eraseAux k l) := by
  induction l with
  | nil => simp [eraseAux, SortedKeys]
  | cons k' tl ih =>
    simp only [eraseAux]
    cases hcmp : StrongOrd.strongCmp k k' with
    | lt => exact hs
    | eq =>
      cases tl with
      | nil => exact True.intro
      | cons k'' tl' =>
        simp only [SortedKeys] at hs
        exact hs.2
    | gt =>
      cases tl with
      | nil => simp [eraseAux, SortedKeys]
      | cons k'' tl' =>
        have hlt : StrongOrd.strongCmp k' k'' = .lt := by
          simp only [SortedKeys] at hs; exact hs.1
        have hsrest : SortedKeys (k'' :: tl') := by
          simp only [SortedKeys] at hs; exact hs.2
        have ihtl := ih hsrest
        simp only [eraseAux] at ihtl ⊢
        cases hcmp2 : StrongOrd.strongCmp k k'' with
        | lt =>
          exact ⟨hlt, hsrest⟩
        | eq =>
          simp only [hcmp2] at ihtl
          cases tl' with
          | nil => exact True.intro
          | cons k''' tl'' =>
            have hlt2 : StrongOrd.strongCmp k'' k''' = .lt := by
              simp only [SortedKeys] at hsrest; exact hsrest.1
            have hsrest2 : SortedKeys (k''' :: tl'') := by
              simp only [SortedKeys] at hsrest; exact hsrest.2
            exact ⟨StrongOrd.cmp_lt_trans k' k'' k''' hlt hlt2, hsrest2⟩
        | gt =>
          simp only [hcmp2] at ihtl
          exact ⟨hlt, ihtl⟩

/-- `erase(k)` — remove an element (§24.4.3.6). -/
def erase (s : CppSet K) (k : K) : CppSet K :=
  ⟨eraseAux k s.elems, eraseAux_sorted k s.elems s.sorted⟩

/-- `size()` — number of elements (§24.4.3.1). -/
def size (s : CppSet K) : Nat :=
  s.elems.length

end CppSet

end Cpp
