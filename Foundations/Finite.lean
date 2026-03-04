
namespace Finite

-- Finite lists
inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α

notation "[]" => List.nil
notation x "::" xs => List.cons x xs

-- Nonempty lists
inductive NonemptyList (α : Type) where
  | item (x : α) : NonemptyList α
  | cons : α → NonemptyList α → NonemptyList α

notation "[" x "]" => NonemptyList.item x
notation x ":::" xs => NonemptyList.cons x xs

-- Natural numbers
inductive Natural : Type where
  | zero : Natural
  | succ (n : Natural) : Natural

notation "𝐍" => Natural
notation "𝟘" => Natural.zero

theorem succ_inj (n m : 𝐍) (h : Natural.succ n = Natural.succ m) : n = m :=
  by
    simp at h
    exact h

def length (l : List α) : Natural :=
  match l with
    | [] => 𝟘
    | _ :: l' => Natural.succ (length l')

-- Finite binary trees
inductive BinaryTree (α : Type) where
  | leaf (x : α) : BinaryTree α
  | bin : BinaryTree α → BinaryTree α → BinaryTree α
