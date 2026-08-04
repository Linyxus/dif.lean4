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

/-! ## Permissions -/

namespace Permission

@[simp] theorem zero_join (p : Permission) : Permission.zero.join p = some p := rfl

@[simp] theorem join_zero (p : Permission) : p.join Permission.zero = some p := by
  cases p <;> rfl

theorem join_comm (p q : Permission) : p.join q = q.join p := by
  cases p <;> cases q <;> rfl

/-- Associativity of the partial join, in Kleisli form. -/
theorem join_assoc (p q r : Permission) :
    (p.join q).bind (fun s => s.join r) = (q.join r).bind (fun s => p.join s) := by
  cases p <;> cases q <;> cases r <;> rfl

/-- The join is cancellative: a defined `p ⊕ q = p ⊕ q'` forces `q = q'`. -/
theorem join_cancel {p q q' : Permission} (hdef : (p.join q).isSome = true)
    (h : p.join q = p.join q') : q = q' := by
  cases p <;> cases q <;> cases q' <;> simp_all [join]

/-- Definedness of the permission join, in the shape of `PermMap.Joinable`. -/
theorem join_isSome_iff (p q : Permission) :
    (p.join q).isSome = true ↔
      p = Permission.zero ∨ q = Permission.zero ∨
        (p = Permission.read ∧ q = Permission.read) := by
  cases p <;> cases q <;> simp [join]

/-- A join is zero exactly when both sides are. -/
theorem join_eq_zero_iff {p q : Permission} :
    p.join q = some Permission.zero ↔
      p = Permission.zero ∧ q = Permission.zero := by
  cases p <;> cases q <;> simp [join]

/-- Reassociation of a defined double join, with explicit witnesses. -/
theorem join_assoc_exists {p q r s t : Permission}
    (h1 : p.join q = some s) (h2 : s.join r = some t) :
    ∃ u, q.join r = some u ∧ p.join u = some t := by
  have key : (q.join r).bind (fun u => p.join u) = some t := by
    rw [← join_assoc, h1]
    exact h2
  cases hqr : q.join r with
  | none => rw [hqr] at key; exact nomatch key
  | some u =>
    rw [hqr] at key
    exact ⟨u, rfl, key⟩

end Permission

/-! ## Permission maps -/

namespace PermMap

/-- `Joinable` coincides with pointwise definedness of `Permission.join`. -/
theorem joinable_iff_isSome (f g : PermMap) :
    f.Joinable g ↔ ∀ l, ((f l).join (g l)).isSome = true := by
  constructor
  · intro h l
    exact (Permission.join_isSome_iff _ _).mpr (h l)
  · intro h l
    exact (Permission.join_isSome_iff _ _).mp (h l)

theorem Joinable.symm {f g : PermMap} (h : f.Joinable g) : g.Joinable f := by
  intro l
  cases h l with
  | inl h0 => exact .inr (.inl h0)
  | inr h' =>
    cases h' with
    | inl h0 => exact .inl h0
    | inr hr => exact .inr (.inr ⟨hr.2, hr.1⟩)

theorem empty_joinable (f : PermMap) : PermMap.empty.Joinable f :=
  fun _ => .inl rfl

theorem joinable_empty (f : PermMap) : f.Joinable PermMap.empty :=
  fun _ => .inr (.inl rfl)

/-- A permission map is joinable with itself iff it grants write nowhere:
the duplicable resources are exactly the read-only ones. -/
theorem joinable_self_iff (f : PermMap) :
    f.Joinable f ↔ ∀ l, f l ≠ Permission.write := by
  constructor
  · intro h l hw
    have hl := h l
    simp_all
  · intro h l
    cases hf : f l with
    | zero => exact .inl rfl
    | read => exact .inr (.inr ⟨rfl, rfl⟩)
    | write => exact absurd hf (h l)

/-- The defining property of `PermMap.join`: pointwise, it is the
(defined) permission join. -/
theorem join_spec (f g : PermMap) (h : f.Joinable g) (l : Nat) :
    (f l).join (g l) = some (f.join g h l) := by
  simp [PermMap.join, Option.some_get]

@[simp] theorem empty_join (f : PermMap) (h : PermMap.empty.Joinable f) :
    PermMap.empty.join f h = f := rfl

@[simp] theorem join_empty (f : PermMap) (h : f.Joinable PermMap.empty) :
    f.join PermMap.empty h = f := by
  funext l
  have hs : (f l).join Permission.zero = some (f.join PermMap.empty h l) :=
    join_spec f PermMap.empty h l
  rw [Permission.join_zero] at hs
  exact (Option.some.inj hs).symm

theorem join_comm (f g : PermMap) (h : f.Joinable g) :
    f.join g h = g.join f h.symm := by
  funext l
  have h1 := join_spec f g h l
  have h2 := join_spec g f h.symm l
  rw [Permission.join_comm] at h2
  exact Option.some.inj (h1.symm.trans h2)

/-- Joins are cancellative at the map level as well. -/
theorem join_cancel {f g g' : PermMap} (h : f.Joinable g) (h' : f.Joinable g')
    (he : f.join g h = f.join g' h') : g = g' := by
  funext l
  have hs := join_spec f g h l
  have hs' := join_spec f g' h' l
  rw [he] at hs
  exact Permission.join_cancel (by rw [hs]; rfl) (hs.trans hs'.symm)

/-- If `f ⊕ g` is joinable with `k`, so is `g` alone. -/
theorem Joinable.of_join_left {f g k : PermMap} (hfg : f.Joinable g)
    (h : (f.join g hfg).Joinable k) : g.Joinable k := by
  intro l
  have hs := join_spec f g hfg l
  have ht := join_spec (f.join g hfg) k h l
  cases Permission.join_assoc_exists hs ht with
  | intro _u hu =>
    apply (Permission.join_isSome_iff _ _).mp
    rw [hu.1]
    rfl

/-- If `(f ⊕ g) ⊕ k` is defined, `f` is joinable with `g ⊕ k`. -/
theorem Joinable.assoc {f g k : PermMap} (hfg : f.Joinable g)
    (h : (f.join g hfg).Joinable k) :
    f.Joinable (g.join k (hfg.of_join_left h)) := by
  intro l
  have hs := join_spec f g hfg l
  have ht := join_spec (f.join g hfg) k h l
  have hgk := join_spec g k (hfg.of_join_left h) l
  cases Permission.join_assoc_exists hs ht with
  | intro u hu =>
    have hu' : g.join k (hfg.of_join_left h) l = u :=
      Option.some.inj (hgk.symm.trans hu.1)
    apply (Permission.join_isSome_iff _ _).mp
    rw [hu', hu.2]
    rfl

/-- Associativity of the map join. -/
theorem join_assoc (f g k : PermMap) (hfg : f.Joinable g)
    (h : (f.join g hfg).Joinable k) :
    (f.join g hfg).join k h
      = f.join (g.join k (hfg.of_join_left h)) (hfg.assoc h) := by
  funext l
  have hs := join_spec f g hfg l
  have ht := join_spec (f.join g hfg) k h l
  have hgk := join_spec g k (hfg.of_join_left h) l
  have hv := join_spec f (g.join k (hfg.of_join_left h)) (hfg.assoc h) l
  cases Permission.join_assoc_exists hs ht with
  | intro u hu =>
    have hu' : g.join k (hfg.of_join_left h) l = u :=
      Option.some.inj (hgk.symm.trans hu.1)
    rw [hu'] at hv
    exact Option.some.inj (hu.2.symm.trans hv)

/-- A joined map vanishes at a location exactly when both components do:
the footprint of a join is the union of the footprints. -/
theorem join_apply_eq_zero_iff (f g : PermMap) (hj : f.Joinable g) (l : Nat) :
    f.join g hj l = Permission.zero ↔
      f l = Permission.zero ∧ g l = Permission.zero := by
  have hs := join_spec f g hj l
  constructor
  · intro h0
    rw [h0] at hs
    exact Permission.join_eq_zero_iff.mp hs
  · intro ⟨h1, h2⟩
    rw [h1, h2] at hs
    exact (Option.some.inj hs).symm

end PermMap

/-! ## Heaps and footprint agreement -/

namespace Heap

/-- Pointwise update of a heap. -/
def update (h : Heap) (l : Nat) (v : HeapVal) : Heap :=
  fun l' => if l' = l then v else h l'

@[simp] theorem update_same (h : Heap) (l : Nat) (v : HeapVal) :
    h.update l v l = v := by
  simp [update]

theorem update_other (h : Heap) {l l' : Nat} (hne : l' ≠ l) (v : HeapVal) :
    h.update l v l' = h l' := by
  simp [update, hne]

/-- Two heaps agree on (the footprint of) a permission map if they coincide
at every location carrying nonzero permission. -/
def AgreeOn (π : PermMap) (h₁ h₂ : Heap) : Prop :=
  ∀ l, π l ≠ Permission.zero → h₁ l = h₂ l

theorem AgreeOn.refl (π : PermMap) (h : Heap) : AgreeOn π h h :=
  fun _ _ => rfl

theorem AgreeOn.symm {π : PermMap} {h₁ h₂ : Heap} (h : AgreeOn π h₁ h₂) :
    AgreeOn π h₂ h₁ :=
  fun l hl => (h l hl).symm

theorem AgreeOn.trans {π : PermMap} {h₁ h₂ h₃ : Heap} (a : AgreeOn π h₁ h₂)
    (b : AgreeOn π h₂ h₃) : AgreeOn π h₁ h₃ :=
  fun l hl => (a l hl).trans (b l hl)

/-- Any two heaps agree on the empty footprint. -/
theorem agreeOn_empty (h₁ h₂ : Heap) : AgreeOn PermMap.empty h₁ h₂ :=
  fun _ hl => absurd rfl hl

/-- Agreement on a join is agreement on both halves. -/
theorem agreeOn_join_iff {f g : PermMap} (hj : f.Joinable g) {h₁ h₂ : Heap} :
    AgreeOn (f.join g hj) h₁ h₂ ↔ AgreeOn f h₁ h₂ ∧ AgreeOn g h₁ h₂ := by
  constructor
  · intro h
    constructor
    · intro l hl
      apply h l
      intro h0
      exact hl ((PermMap.join_apply_eq_zero_iff f g hj l).mp h0).1
    · intro l hl
      apply h l
      intro h0
      exact hl ((PermMap.join_apply_eq_zero_iff f g hj l).mp h0).2
  · intro ⟨ha, hb⟩ l hl
    cases hf : f l with
    | zero =>
      apply hb l
      intro hg
      exact hl ((PermMap.join_apply_eq_zero_iff f g hj l).mpr ⟨hf, hg⟩)
    | read => exact ha l (by simp [hf])
    | write => exact ha l (by simp [hf])

/-- Writing at a location outside the footprint of `π` is invisible on `π`. -/
theorem agreeOn_update {π : PermMap} (h : Heap) {l : Nat}
    (hl : π l = Permission.zero) (v : HeapVal) :
    AgreeOn π h (h.update l v) := by
  intro l' hl'
  have hne : l' ≠ l := fun he => hl' (by rw [he]; exact hl)
  rw [update_other h hne]

end Heap

end Dif
