import Foundations.Finite
import Foundations.Structures

namespace Naturals

open Structures
open Finite

-- The goal: Proving that natural numbers for a commutative monoid under addition.

def add (n : 𝐍) (m : 𝐍) : 𝐍 :=
  match m with
    | 𝟘 => n
    | Natural.succ k => Natural.succ (add n k)

infixl:65 " + " => add

-- The natural numbers are a magma
instance : Magma 𝐍 where
  op := add

-- The natural numbers are a semigroup

theorem nat_addAssoc (x y z : 𝐍) : (x + y) + z = x + (y + z) := by
  induction z with
  | zero => rw [add, add]
  | succ k hk =>
    rw [add, hk, add, add]

instance : Semigroup 𝐍 where
  op_assoc := nat_addAssoc


-- The natural numbers are a monoid

theorem nat_leftZero (x : 𝐍) : 𝟘 + x = x := by
  induction x with
    | zero => rw [add]
    | succ k hk =>
      rw [add, hk]

theorem nat_rightZero (x : 𝐍) : x + 𝟘 = x := by
  rw [add]

instance : Monoid 𝐍 where
  unit := 𝟘
  left_unit := nat_leftZero
  right_unit := nat_rightZero

-- The natural numbers are a commutative monoid

theorem switching_succ (x y : 𝐍) : x + (Natural.succ y) = (Natural.succ x) + y := by
  induction y with
    | zero =>
      rw [nat_rightZero, add, nat_rightZero]
    | succ k hk =>
      rw [add, add, add, ←add, hk]


theorem nat_addComm (x y : 𝐍) : x + y = y + x := by
  induction y with
  | zero =>  rw [nat_leftZero, nat_rightZero]
  | succ a ha =>
    induction x with
    | zero => rw [nat_leftZero, nat_rightZero]
    | succ b hb =>
      rw [add, add, ha, switching_succ]


instance : CommMonoid 𝐍 where
  op_comm := nat_addComm

-- Addition allows for left and right cancellation.

theorem nat_addLeftCancel (z x y : 𝐍) (h : z + x = z + y) : x = y := by
  induction z with
  | zero =>
    rw [nat_leftZero] at h
    rw [nat_leftZero] at h
    exact h
  | succ k hk =>
    apply hk
    apply succ_inj
    rw [←add, ←add]
    rw [switching_succ, h]
    rw [←switching_succ]

theorem nat_addRightCancel (z x y : 𝐍) (h : x + z = y + z) : x = y := by
  rw [nat_addComm x z] at h
  rw [nat_addComm y z] at h
  apply nat_addLeftCancel z x y
  exact h

theorem nat_addLeftComm (x y z : 𝐍) : x + (y + z) = y + (x + z) := by
  rw [←nat_addAssoc, ←nat_addAssoc]
  rw [nat_addComm x y]


-- == ORDERING THE NATURALS ==

notation "𝟙" => Natural.succ 𝟘

theorem nat_rightAddImpliesZero (n x : 𝐍) (h : n + x = n) : x = 𝟘 := by
  induction n with
  | zero =>
    rw [nat_leftZero] at h
    exact h
  | succ k hk =>
    rw [nat_addComm, add] at h
    apply hk
    apply succ_inj
    rw [nat_addComm]
    exact h

theorem nat_addToZeroImpliesZero (n m : 𝐍) (h : n + m = 𝟘) : m = 𝟘 := by
  induction n with
  | zero =>
    rw [nat_leftZero] at h
    exact h
  | succ k hk =>
    rw [nat_addComm, add] at h
    simp at h



def ord (n m : 𝐍) :=
  ∃ t : 𝐍, n + t = m

-- If n ≤ m, either n = m, or n + 1 ≤ m.
theorem nat_eqOrGeqPlusOne (n m : 𝐍) (hnm : ord n m) :
  (n = m) ∨ (ord (Natural.succ n) m) := by
    induction n with
    | zero =>
      induction m with
      | zero =>
        apply Or.intro_left
        rfl
      | succ k hk =>
        apply Or.intro_right
        unfold ord
        apply Exists.intro k
        rw [nat_addComm, add, nat_rightZero]
    | succ l hl =>
      match hnm with
      | ⟨p, hp⟩ =>
        induction p with
        | zero =>
          rw [nat_rightZero] at hp
          apply Or.intro_left
          exact hp
        | succ k hk =>
          apply Or.intro_right
          unfold ord
          apply Exists.intro k
          rw [←switching_succ]
          exact hp

theorem nat_ordRefl (n : 𝐍) : ord n n := by
  apply Exists.intro 𝟘
  rw [nat_rightZero]

theorem nat_ordAntisymm (n m : 𝐍) (hnm : ord n m) (hmn : ord m n) : n = m := by
  unfold ord at *
  match hnm with
  | ⟨p, hp⟩ =>
    match hmn with
      | ⟨q, hq⟩ =>
        rw [←hp, nat_addAssoc] at hq
        have h₁ := nat_rightAddImpliesZero n (p + q) hq
        rw [nat_addComm] at h₁
        have h₂ := nat_addToZeroImpliesZero q p h₁
        rw [h₂, nat_rightZero] at hp
        exact hp

theorem nat_ordTrans (l m n : 𝐍) (hlm : ord l m) (hmn : ord m n) : ord l n := by
  unfold ord at *
  match hlm with
    | ⟨p, hp⟩ =>
      match hmn with
        | ⟨q, hq⟩ =>
          apply Exists.intro (p + q)
          rw [←nat_addAssoc, hp]
          exact hq

-- The natural numbers form a poset.
instance : Poset 𝐍 where
  ord := ord
  ord_refl := nat_ordRefl
  ord_antisymm := nat_ordAntisymm
  ord_trans := nat_ordTrans



-- The natural numbers form a total order.

theorem nat_ordTotal (n m : 𝐍) : ord n m ∨ ord m n := by
  induction m with
  | zero =>
    apply Or.intro_right
    apply Exists.intro n
    rw [nat_leftZero]
  | succ k hk =>
    cases hk with
    | inl h₁ =>
      apply Or.intro_left
      unfold ord at *
      match h₁ with
      | ⟨p, hp⟩ =>
        apply Exists.intro (Natural.succ p)
        rw [add, hp]
    | inr h₂ =>
      have c := nat_eqOrGeqPlusOne k n h₂
      cases c with
      | inl h₃ =>
        apply Or.intro_left
        apply Exists.intro 𝟙
        rw [add, nat_rightZero, h₃]
      | inr h₄ =>
        apply Or.intro_right
        exact h₄

instance : TotalOrder 𝐍 where
  comparable := nat_ordTotal
