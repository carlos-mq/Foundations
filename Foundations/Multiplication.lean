
import Foundations.Integers

-- == DEFINING MULTIPLICATION FOR 𝐍 AND 𝐙 ==
namespace Multiplication
open Finite
open Integers
open Naturals

def mult (n m : 𝐍) : 𝐍 :=
  match m with
    | Natural.zero => 𝟘
    | Natural.succ k => n + (mult n k)

infixl:65 " * " => mult
