namespace Dif

/-- Heap value. -/
inductive HeapVal : Type where
| num : Nat -> HeapVal
| bool : Bool -> HeapVal

/-- A heap is a mapping from locations to values -/
def Heap : Type := Nat -> HeapVal

/-- A permission -/
inductive Permission : Type where
| zero : Permission   -- 0
| read : Permission   -- 1/2
| write : Permission  -- 1

/-- A permission map is a mapping from locations to permissions -/
def PermMap : Type := Nat -> Permission

/-- Two permission maps are joinable or not. -/
def PermMap.Joinable : PermMap -> PermMap -> Prop
| f, g => ∀ l,
  (f l = Permission.zero) ∨ (g l = Permission.zero) ∨
  (f l = Permission.read ∧ g l = Permission.read)

/-- Join of two permissions, i.e. fractional addition: `read + read = write`.
Incompatible combinations are undefined. -/
def Permission.join : Permission -> Permission -> Option Permission
| .zero, p => some p
| p, .zero => some p
| .read, .read => some .write
| _, _ => none

/-- Pointwise join of two permission maps, defined only on joinable maps. -/
def PermMap.join (f g : PermMap) (h : f.Joinable g) : PermMap := fun l =>
  ((f l).join (g l)).get (by
    have hl := h l
    cases hf : f l <;> cases hg : g l <;> simp_all [Permission.join])

def PermMap.empty : PermMap := fun _ => Permission.zero

end Dif
