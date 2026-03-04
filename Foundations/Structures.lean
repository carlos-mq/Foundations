import Foundations.Finite

namespace Structures

-- == MAGMAS ==

-- Magma: A structure with a binary operation.
class Magma (G : Type) where
  op : G → G → G

infixl:65 " ⋆ " => Magma.op

-- One can describe a given application of elements of a magma
-- as a binary tree.
def MagmaTree [Magma G] (t : Finite.BinaryTree G) : G :=
  match t with
    | Finite.BinaryTree.leaf x => x
    | Finite.BinaryTree.bin t₁ t₂ => (MagmaTree t₁) ⋆ (MagmaTree t₂)

-- == SEMIGROUPS ==

-- Semigroup: A magma where the operation is associative.
class Semigroup (G : Type) extends Magma G where
  op_assoc : ∀ (x y z : G), (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z)

def SemigroupSum [Semigroup G] (l : Finite.NonemptyList G) : G :=
  match l with
    | [x] => x
    | x ::: xs => x ⋆ (SemigroupSum xs)

notation "Σ₁" l => SemigroupSum l

-- In a semigroup, the result of an application doesn't depend on the
-- parenthetization.

-- == MONOIDS ==

-- Monoid: A semigroup with an unit element.
class Monoid (G : Type) extends Semigroup G where
  unit : G
  left_unit (x : G) : unit ⋆ x = x
  right_unit (x : G) : x ⋆ unit = x

def MonoidSum [Monoid G] (l : Finite.List G) : G :=
  match l with
    | [] => Monoid.unit
    | x :: xs => x ⋆ (MonoidSum xs)

notation "Σ₀" l => MonoidSum l

-- == COMMUTATIVE MONOIDS ==

-- A commutative monoid: A monoid where the operation commutes.
class CommMonoid (G : Type) extends Monoid G where
  op_comm (x y : G) : x ⋆ y = y ⋆ x


-- == GROUPS ==

-- Group: A monoid with inverses.
class Group (G : Type) extends Monoid G where
  inv : G → G
  left_inv (x : G) : (inv x) ⋆ x = unit
  right_inv (x : G) : x ⋆ (inv x) = unit

-- == ABELIAN GROUPS ==

-- Abelian group: A group where the operation is commutative.
class Abelian (G : Type) extends Group G where
  op_comm (x y : G) : x ⋆ y = y ⋆ x

-- == POSETS ==

-- A poset: A structure with a binary relation called an order.
class Poset (G : Type) where
  ord : G → G → Prop
  ord_refl (x : G) : ord x x
  ord_antisymm (x y : G) (h₁ : ord x y) (h₂ : ord y x) : x = y
  ord_trans (x y z : G) (h₁ : ord x y) (h₂ : ord y z) : ord x z

infixl:65 " ≤ " => Poset.ord

-- A total order: A poset where every pair of elements are comparable.
class TotalOrder (G : Type) extends Poset G where
  comparable (x y : G) : x ≤ y ∨ y ≤ x
