import Foundations.Naturals
import Foundations.Structures

namespace Integers

open Naturals
open Structures

-- The goal: Proving that the integers form a group under addition.


def diff_eq (p₁ : 𝐍 × 𝐍) (p₂ : 𝐍 × 𝐍) : Prop :=
  match (p₁, p₂) with
    | ((a₁, b₁), (a₂, b₂)) => a₁ + b₂ = a₂ + b₁

theorem refl_of_diff_eq (p : 𝐍 × 𝐍) : diff_eq p p := by
  unfold diff_eq
  simp

theorem symm_of_diff_eq (p q : 𝐍 × 𝐍) : diff_eq p q → diff_eq q p := by
  unfold diff_eq
  simp
  intro h
  rw [h]

theorem trans_of_diff
    (p q r : 𝐍 × 𝐍)
    (hpq : diff_eq p q)
    (hqr : diff_eq q r) :
    diff_eq p r := by
  unfold diff_eq at *
  simp at *
  apply nat_addLeftCancel q.snd
  rw [←nat_addAssoc]
  rw [nat_addComm q.snd]
  rw [hpq]
  rw [←nat_addAssoc]
  rw [nat_addComm q.snd]
  rw [←hqr]
  rw [nat_addAssoc, nat_addAssoc]
  rw [nat_addComm p.snd]

instance Integer.Setoid : Setoid (𝐍 × 𝐍) := {
  r := diff_eq
  iseqv := {
    refl := refl_of_diff_eq
    symm :=  by
      intro x y
      exact symm_of_diff_eq x y
    trans := by
      intro x y z hxy hyz
      exact trans_of_diff x y z hxy hyz
  }
}

def Integer : Type := Quotient Integer.Setoid

theorem Integer.Setoid_Iff (p₁ p₂ : 𝐍 × 𝐍) : p₁ ≈ p₂ ↔ diff_eq p₁ p₂ := by
  rfl

notation "𝐙" => Integer

def natToInt (n : 𝐍) : 𝐙 := Quotient.mk Integer.Setoid (n, 𝟘)

notation "𝟘" => natToInt 𝟘

def nat_addPairsToInt (p₁ p₂ : 𝐍 × 𝐍) : 𝐙 :=
  Quotient.mk Integer.Setoid (p₁.fst + p₂.fst, p₁.snd + p₂.snd)

def add : 𝐙 → 𝐙 → 𝐙 :=
  Quotient.lift₂
    nat_addPairsToInt
    (by
      intro a b c d hac hbd
      apply Quotient.sound
      rw [Integer.Setoid_Iff] at *
      unfold diff_eq at *
      simp at *
      have h : (a.fst + c.snd) + (b.fst + d.snd) = (c.fst + a.snd) + (d.fst + b.snd) :=
        by
        rw [hac, hbd]
      calc
        a.fst + b.fst + (c.snd + d.snd) = a.fst + c.snd + (b.fst + d.snd) := by
          simp only [nat_addComm, nat_addLeftComm]
        _ = c.fst + a.snd + (d.fst + b.snd) := by rw [h]
        _ = c.fst + d.fst + (a.snd + b.snd) := by simp only [nat_addComm, nat_addLeftComm]
      )

infixl:65 " + " => add


def nat_zeroPairToNeg (p : 𝐍 × 𝐍) : 𝐙 :=
  Quotient.mk Integer.Setoid (p.snd, p.fst)

def neg : 𝐙 → 𝐙 :=
  Quotient.lift
    nat_zeroPairToNeg
    (by
      intro a b c
      apply Quotient.sound
      rw [Integer.Setoid_Iff] at *
      unfold diff_eq at *
      simp at *
      rw [nat_addComm, ←c, nat_addComm]
    )

def nat_toNeg : 𝐍 → 𝐙 := neg ∘ natToInt

-- The integers are a magma
instance : Magma 𝐙 where
  op := add

-- natToInt is a magma homomorphism.
theorem natAddToIntAdd (n m : 𝐍) :
  (natToInt n) + (natToInt m) = natToInt (n + m) := by
  apply Quotient.sound
  rw [Integer.Setoid_Iff] at *
  unfold diff_eq at *
  simp at *
  rw [nat_rightZero, nat_rightZero, nat_rightZero]

-- nat_toNeg is a magma homomorphism.
theorem natAddToNegIntAdd (n m : 𝐍) :
  (nat_toNeg n) + (nat_toNeg m) = nat_toNeg (n + m) := by
  apply Quotient.sound
  rw [Integer.Setoid_Iff] at *
  unfold diff_eq at *
  simp at *
  rw [nat_leftZero, nat_leftZero]





-- For any k : 𝐙, there's either an n with k = nat_toInt n,
-- or k = nat_toNeg n.

theorem int_NatOrNeg (k : 𝐙) :
  ∃ n : 𝐍, (natToInt n = k) ∨ (nat_toNeg n = k) := by
    induction k using Quotient.inductionOn with
    | h p =>
      cases p with
        | mk p₁ p₂ =>
          have t := nat_ordTotal p₁ p₂
          cases t with
          | inl c₁ =>
            unfold ord at c₁
            match c₁ with
            | ⟨c₂, hc⟩ =>
              apply Exists.intro c₂
              apply Or.intro_right
              apply Quotient.sound
              simp
              rw [Integer.Setoid_Iff]
              unfold diff_eq
              simp
              rw [nat_leftZero, hc]
          | inr c₃ =>
            unfold ord at c₃
            match c₃ with
            | ⟨c₄, hc⟩ =>
              apply Exists.intro c₄
              apply Or.intro_left
              apply Quotient.sound
              rw [Integer.Setoid_Iff]
              unfold diff_eq
              simp
              rw [nat_rightZero]
              rw [nat_addComm]
              exact hc



-- The integers are a semigroup

theorem int_addAssoc (x y z : 𝐙) : (x + y) + z = x + (y + z) := by
  induction x using Quotient.inductionOn with
  | h x' =>
    induction y using Quotient.inductionOn with
    | h y' =>
      induction z using Quotient.inductionOn with
      | h z' =>
        apply Quotient.sound
        simp
        rw [Integer.Setoid_Iff]
        unfold diff_eq
        simp
        simp only [nat_addAssoc]

instance : Semigroup 𝐙 where
  op_assoc := int_addAssoc

-- The integers are a monoid

theorem int_leftZero (x : 𝐙) : 𝟘 + x = x := by
  induction x using Quotient.inductionOn with
  | h x' =>
    apply Quotient.sound
    simp
    rw [Integer.Setoid_Iff]
    unfold diff_eq
    simp
    rw [nat_addComm 𝟘, nat_addAssoc]

theorem int_rightZero (x : 𝐙) : x + 𝟘 = x := by
  induction x using Quotient.inductionOn with
  | h x' =>
    apply Quotient.sound
    simp
    rw [Integer.Setoid_Iff]
    unfold diff_eq
    simp
    rw [nat_addAssoc, nat_addComm 𝟘]


instance : Monoid 𝐙 where
  unit := 𝟘
  left_unit := int_leftZero
  right_unit := int_rightZero

-- The integers are an Abelian group

theorem int_addComm (x y : 𝐙) : x + y = y + x := by
  induction x using Quotient.inductionOn with
  | h x' =>
    induction y using Quotient.inductionOn with
    | h y' =>
      apply Quotient.sound
      rw [Integer.Setoid_Iff]
      unfold diff_eq
      simp
      rw [nat_addComm x'.fst, nat_addComm y'.snd]

theorem int_leftInv (x : 𝐙) : (neg x) + x = (𝟘 : 𝐙) := by
  induction x using Quotient.inductionOn with
  | h x' =>
    unfold neg
    apply Quotient.sound
    rw [Integer.Setoid_Iff]
    unfold diff_eq
    simp
    rw [nat_rightZero, nat_leftZero, nat_addComm]

theorem int_rightInv (x : 𝐙) : x + (neg x) = (𝟘 : 𝐙) := by
  rw [int_addComm, int_leftInv]

instance : Group 𝐙 where
  inv := neg
  left_inv := int_leftInv
  right_inv := int_rightInv

instance : Abelian 𝐙 where
  op_comm := int_addComm
