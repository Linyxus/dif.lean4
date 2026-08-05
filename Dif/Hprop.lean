import Dif.Heap

namespace Dif

/-- A DIF proposition. -/
def Hprop : Type := Heap -> PermMap -> Prop

/-- Exactly permission `p` is held at `loc`; the heap is unconstrained. -/
def Hprop.accAt (loc : Nat) (p : Permission) : Hprop
| _, π => π loc = p

/-- Full (write) permission at `loc`. -/
def Hprop.acc (loc : Nat) : Hprop := Hprop.accAt loc .write

/-- Read-only permission at `loc`. -/
def Hprop.accRO (loc : Nat) : Hprop := Hprop.accAt loc .read

/-- The empty DIF proposition: no permissions are held. -/
def Hprop.empty : Hprop
| _, π => π = PermMap.empty

/-! ## Entailment -/

/-- Entailment: `P` entails `Q` in every state. -/
def Hprop.entails (P Q : Hprop) : Prop :=
  ∀ h π, P h π -> Q h π

/-- Equivalence of DIF propositions, pointwise. -/
def Hprop.equiv (P Q : Hprop) : Prop :=
  ∀ h π, P h π ↔ Q h π

@[inherit_doc] infix:25 " ⊢ " => Hprop.entails
@[inherit_doc] infix:25 " ⊣⊢ " => Hprop.equiv

theorem Hprop.entails.refl (P : Hprop) : P ⊢ P :=
  fun _ _ hp => hp

theorem Hprop.entails.trans {P Q R : Hprop} (h1 : P ⊢ Q) (h2 : Q ⊢ R) : P ⊢ R :=
  fun h π hp => h2 h π (h1 h π hp)

theorem Hprop.equiv.of_entails {P Q : Hprop} (h1 : P ⊢ Q) (h2 : Q ⊢ P) : P ⊣⊢ Q :=
  fun h π => ⟨h1 h π, h2 h π⟩

theorem Hprop.equiv.mp {P Q : Hprop} (h : P ⊣⊢ Q) : P ⊢ Q :=
  fun h' π hp => (h h' π).mp hp

theorem Hprop.equiv.mpr {P Q : Hprop} (h : P ⊣⊢ Q) : Q ⊢ P :=
  fun h' π hp => (h h' π).mpr hp

theorem Hprop.equiv.refl (P : Hprop) : P ⊣⊢ P :=
  fun _ _ => Iff.rfl

theorem Hprop.equiv.symm {P Q : Hprop} (h : P ⊣⊢ Q) : Q ⊣⊢ P :=
  fun h' π => (h h' π).symm

theorem Hprop.equiv.trans {P Q R : Hprop} (h1 : P ⊣⊢ Q) (h2 : Q ⊣⊢ R) : P ⊣⊢ R :=
  fun h π => (h1 h π).trans (h2 h π)

/-! ## Separating conjunction -/

/-- Separating conjunction: the permission map splits into two joinable
halves satisfying the conjuncts on the shared heap. -/
def Hprop.sep (P Q : Hprop) : Hprop
| h, π => ∃ (π₁ π₂ : PermMap) (hj : π₁.Joinable π₂),
    π₁.join π₂ hj = π ∧ P h π₁ ∧ Q h π₂

@[inherit_doc] infixr:70 " ∗ " => Hprop.sep

/-- `∗` is monotone in both arguments. -/
theorem Hprop.sep_mono {P P' Q Q' : Hprop} (hP : P ⊢ P') (hQ : Q ⊢ Q') :
    P ∗ Q ⊢ P' ∗ Q' := by
  intro h π ⟨π₁, π₂, hj, hjoin, h1, h2⟩
  exact ⟨π₁, π₂, hj, hjoin, hP h π₁ h1, hQ h π₂ h2⟩

theorem Hprop.sep_comm_entails (P Q : Hprop) : P ∗ Q ⊢ Q ∗ P := by
  intro h π ⟨π₁, π₂, hj, hjoin, h1, h2⟩
  refine ⟨π₂, π₁, hj.symm, ?_, h2, h1⟩
  rw [← PermMap.join_comm]
  exact hjoin

/-- `∗` is commutative. -/
theorem Hprop.sep_comm (P Q : Hprop) : P ∗ Q ⊣⊢ Q ∗ P :=
  equiv.of_entails (sep_comm_entails P Q) (sep_comm_entails Q P)

theorem Hprop.sep_assoc_entails (P Q R : Hprop) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) := by
  intro h π ⟨π₁₂, π₃, hj, hjoin, ⟨π₁, π₂, hj', hjoin', h1, h2⟩, h3⟩
  subst hjoin'
  rw [PermMap.join_assoc] at hjoin
  exact ⟨π₁, π₂.join π₃ (hj'.of_join_left hj), hj'.assoc hj, hjoin, h1,
    ⟨π₂, π₃, hj'.of_join_left hj, rfl, h2, h3⟩⟩

theorem Hprop.sep_assoc_entails' (P Q R : Hprop) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R :=
  ((((sep_comm_entails P (Q ∗ R)).trans
      (sep_assoc_entails Q R P)).trans
    (sep_comm_entails Q (R ∗ P))).trans
      (sep_assoc_entails R P Q)).trans
    (sep_comm_entails R (P ∗ Q))

/-- `∗` is associative. -/
theorem Hprop.sep_assoc (P Q R : Hprop) : (P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R) :=
  equiv.of_entails (sep_assoc_entails P Q R) (sep_assoc_entails' P Q R)

/-- `empty` is a left unit for `∗`. -/
theorem Hprop.empty_sep (P : Hprop) : Hprop.empty ∗ P ⊣⊢ P := by
  apply equiv.of_entails
  · intro h π ⟨π₁, π₂, hj, hjoin, hE, hP⟩
    have hE' : π₁ = PermMap.empty := hE
    subst hE'
    rw [PermMap.empty_join] at hjoin
    rw [← hjoin]
    exact hP
  · intro h π hp
    exact ⟨PermMap.empty, π, PermMap.empty_joinable π,
      PermMap.empty_join π (PermMap.empty_joinable π), rfl, hp⟩

/-- `empty` is a right unit for `∗`. -/
theorem Hprop.sep_empty (P : Hprop) : P ∗ Hprop.empty ⊣⊢ P :=
  (sep_comm P Hprop.empty).trans (empty_sep P)

/-- Write permission is exactly two read halves. -/
theorem Hprop.acc_split (loc : Nat) :
    Hprop.acc loc ⊣⊢ Hprop.accRO loc ∗ Hprop.accRO loc := by
  apply equiv.of_entails
  · intro h π hp
    have hp' : π loc = Permission.write := hp
    have hj : PermMap.Joinable (fun l => if l = loc then .read else π l)
        (fun l => if l = loc then .read else .zero) := by
      intro l
      by_cases hl : l = loc
      · exact .inr (.inr ⟨if_pos hl, if_pos hl⟩)
      · exact .inr (.inl (if_neg hl))
    refine ⟨_, _, hj, ?_, if_pos rfl, if_pos rfl⟩
    funext l
    apply (PermMap.join_apply_eq_iff _ _ hj l (π l)).mpr
    show (if l = loc then Permission.read else π l).join
        (if l = loc then Permission.read else Permission.zero) = some (π l)
    by_cases hl : l = loc
    · rw [if_pos hl, if_pos hl, hl, hp']
      rfl
    · rw [if_neg hl, if_neg hl]
      exact Permission.join_zero (π l)
  · intro h π ⟨π₁, π₂, hj, hjoin, h1, h2⟩
    have h1' : π₁ loc = Permission.read := h1
    have h2' : π₂ loc = Permission.read := h2
    show π loc = Permission.write
    have hs := PermMap.join_spec π₁ π₂ hj loc
    rw [h1', h2', hjoin] at hs
    exact (Option.some.inj hs).symm

/-- Write permission is exclusive: `acc loc ∗ acc loc` is unsatisfiable. -/
theorem Hprop.acc_exclusive (loc : Nat) (h : Heap) (π : PermMap) :
    ¬ (Hprop.acc loc ∗ Hprop.acc loc) h π := by
  intro ⟨π₁, π₂, hj, _, h1, h2⟩
  have h1' : π₁ loc = Permission.write := h1
  have h2' : π₂ loc = Permission.write := h2
  have := hj loc
  grind

/-! ## Points-To -/

/-- The heap stores `v` at `loc`, and exactly permission `p` is held there.
This is the first heap-reading assertion; the permission conjunct is what
makes the heap read self-framing (see `pointsToAt_selfFraming`). -/
def Hprop.pointsToAt (loc : Nat) (v : HeapVal) (p : Permission) : Hprop
| h, π => h loc = v ∧ π loc = p

/-- Full points-to: `loc` stores `v` and write permission is held. -/
def Hprop.pointsTo (loc : Nat) (v : HeapVal) : Hprop :=
  Hprop.pointsToAt loc v .write

/-- Read-only points-to: `loc` stores `v` and read permission is held. -/
def Hprop.pointsToRO (loc : Nat) (v : HeapVal) : Hprop :=
  Hprop.pointsToAt loc v .read

/-- Forgetting the stored value turns a points-to into a bare accessibility. -/
theorem Hprop.pointsToAt_entails_accAt (loc : Nat) (v : HeapVal) (p : Permission) :
    Hprop.pointsToAt loc v p ⊢ Hprop.accAt loc p :=
  fun _ _ hp => hp.2

theorem Hprop.pointsTo_entails_acc (loc : Nat) (v : HeapVal) :
    Hprop.pointsTo loc v ⊢ Hprop.acc loc :=
  pointsToAt_entails_accAt loc v .write

theorem Hprop.pointsToRO_entails_accRO (loc : Nat) (v : HeapVal) :
    Hprop.pointsToRO loc v ⊢ Hprop.accRO loc :=
  pointsToAt_entails_accAt loc v .read

/-- Two points-to assertions at the same location agree on the value, even
across a separating conjunction: there is only one total heap. In
partial-heaps separation logic the analogous fact requires an overlap
argument; in the IDF model it is immediate. -/
theorem Hprop.pointsToAt_agree {loc : Nat} {v w : HeapVal} {p q : Permission}
    {h : Heap} {π : PermMap}
    (hs : (Hprop.pointsToAt loc v p ∗ Hprop.pointsToAt loc w q) h π) : v = w := by
  have ⟨π₁, π₂, hj, hjoin, h1, h2⟩ := hs
  have h1' : h loc = v ∧ π₁ loc = p := h1
  have h2' : h loc = w ∧ π₂ loc = q := h2
  exact h1'.1.symm.trans h2'.1

/-- Write points-to is exclusive, whatever the claimed values are. -/
theorem Hprop.pointsTo_exclusive (loc : Nat) (v w : HeapVal) (h : Heap)
    (π : PermMap) : ¬ (Hprop.pointsTo loc v ∗ Hprop.pointsTo loc w) h π :=
  fun hs => acc_exclusive loc h π
    (sep_mono (pointsTo_entails_acc loc v) (pointsTo_entails_acc loc w) h π hs)

/-- A write points-to splits into two read halves of the same value. -/
theorem Hprop.pointsTo_split (loc : Nat) (v : HeapVal) :
    Hprop.pointsTo loc v ⊣⊢ Hprop.pointsToRO loc v ∗ Hprop.pointsToRO loc v := by
  apply equiv.of_entails
  · intro h π hp
    have hp' : h loc = v ∧ π loc = Permission.write := hp
    have ⟨π₁, π₂, hj, hjoin, ha1, ha2⟩ := (acc_split loc).mp h π hp'.2
    exact ⟨π₁, π₂, hj, hjoin, ⟨hp'.1, ha1⟩, ⟨hp'.1, ha2⟩⟩
  · intro h π ⟨π₁, π₂, hj, hjoin, h1, h2⟩
    have h1' : h loc = v ∧ π₁ loc = Permission.read := h1
    have h2' : h loc = v ∧ π₂ loc = Permission.read := h2
    exact ⟨h1'.1, (acc_split loc).mpr h π ⟨π₁, π₂, hj, hjoin, h1'.2, h2'.2⟩⟩

/-! ## Self-framing -/

/-- An assertion is self-framing if it only depends on the part of the heap
covered by its permission map: modifying locations outside the footprint
cannot invalidate it. This is the central well-formedness condition of
implicit dynamic frames. -/
def Hprop.SelfFraming (P : Hprop) : Prop :=
  ∀ h1 h2 π,
    Heap.AgreeOn π h1 h2 ->
    P h1 π -> P h2 π

/-- Pure permission assertions never read the heap, so they are self-framing. -/
theorem Hprop.accAt_selfFraming (loc : Nat) (p : Permission) :
    (Hprop.accAt loc p).SelfFraming :=
  fun _ _ _ _ hp => hp

theorem Hprop.acc_selfFraming (loc : Nat) : (Hprop.acc loc).SelfFraming :=
  accAt_selfFraming loc .write

theorem Hprop.accRO_selfFraming (loc : Nat) : (Hprop.accRO loc).SelfFraming :=
  accAt_selfFraming loc .read

theorem Hprop.empty_selfFraming : Hprop.empty.SelfFraming :=
  fun _ _ _ _ hp => hp

/-- A points-to with nonzero permission is self-framing: the permission held
at `loc` licenses the heap read at `loc`. -/
theorem Hprop.pointsToAt_selfFraming (loc : Nat) (v : HeapVal) {p : Permission}
    (hp : p ≠ Permission.zero) : (Hprop.pointsToAt loc v p).SelfFraming := by
  intro h1 h2 π hagree hp1
  have hp1' : h1 loc = v ∧ π loc = p := hp1
  have hloc : h1 loc = h2 loc := hagree loc (by rw [hp1'.2]; exact hp)
  exact ⟨hloc.symm.trans hp1'.1, hp1'.2⟩

theorem Hprop.pointsTo_selfFraming (loc : Nat) (v : HeapVal) :
    (Hprop.pointsTo loc v).SelfFraming :=
  pointsToAt_selfFraming loc v (fun h => nomatch h)

theorem Hprop.pointsToRO_selfFraming (loc : Nat) (v : HeapVal) :
    (Hprop.pointsToRO loc v).SelfFraming :=
  pointsToAt_selfFraming loc v (fun h => nomatch h)

/-- Reading the heap without permission is NOT self-framing: with zero
permission at `loc`, the footprint excludes `loc`, yet the assertion
constrains the heap there. This counterexample is why self-framing is a
nontrivial property. -/
theorem Hprop.pointsToAt_zero_not_selfFraming (loc : Nat) :
    ¬ (Hprop.pointsToAt loc (HeapVal.num 0) Permission.zero).SelfFraming := by
  intro hsf
  have h2 := hsf (fun _ => HeapVal.num 0)
    (Heap.update (fun _ => HeapVal.num 0) loc (HeapVal.num 1))
    PermMap.empty (Heap.agreeOn_empty _ _) ⟨rfl, rfl⟩
  have h2' : Heap.update (fun _ => HeapVal.num 0) loc (HeapVal.num 1) loc
      = HeapVal.num 0 := h2.1
  have hup : Heap.update (fun _ => HeapVal.num 0) loc (HeapVal.num 1) loc
      = HeapVal.num 1 := Heap.update_same _ loc (HeapVal.num 1)
  exact nomatch hup.symm.trans h2'

/-- Self-framing is closed under separating conjunction: each conjunct reads
the heap only within its own half of the footprint. -/
theorem Hprop.SelfFraming.sep {P Q : Hprop} (hP : P.SelfFraming)
    (hQ : Q.SelfFraming) : (P ∗ Q).SelfFraming := by
  intro h1 h2 π hagree ⟨π₁, π₂, hj, hjoin, hp, hq⟩
  subst hjoin
  have ⟨ha1, ha2⟩ := (Heap.agreeOn_join_iff hj).mp hagree
  exact ⟨π₁, π₂, hj, rfl, hP h1 h2 π₁ ha1 hp, hQ h1 h2 π₂ ha2 hq⟩

/-- Self-framing respects equivalence of assertions. -/
theorem Hprop.SelfFraming.of_equiv {P Q : Hprop} (hP : P.SelfFraming)
    (he : P ⊣⊢ Q) : Q.SelfFraming :=
  fun h1 h2 π hagree hq => (he h2 π).mp (hP h1 h2 π hagree ((he h1 π).mpr hq))

end Dif
