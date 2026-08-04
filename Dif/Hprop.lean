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
  simp_all

end Dif
