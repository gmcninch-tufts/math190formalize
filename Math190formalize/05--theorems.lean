/-
Copyright (c) 2024 George McNinch. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Author : George McNinch
-/

/-
course: Math 190 - Tufts University
instructor: George McNinch
semester: 2024 Spring
-/

----------------------------------------------------------------------------------
-- 03 -- Theorems
----------------------------------------------------------------------------------

import Mathlib.Tactic



--------------------------------------------------------------------------------


/- Lean has a way of representing a `ring` as a type.

   It knows the ring axioms.

-/
namespace myring

variable (R : Type*) [Ring R]

variable (a b c: R)

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end myring
--------------------------------------------------------------------------------

/- The square bracket declaration in

  `variable (R : Type*) [Ring R]`

  requires some explanation, for which we are going to *wait* a bit.

  But really what this says is that R is a type which has been given
  the structure of a ring; e.g. addition is defined:

  `add : R → R → R`

  and we have `a + b == add a b`

-/

variable (R : Type*) [CommRing R]
variable (a b c d : R)

-- the `ring` tactic can provide proofs of basic identities

example : d^2 * a * b * c = b * (d^2 * a * c) := by 
  ring


example : (a + b) * (c + d)  = a*c + a*d + b*c + b * d :=  by
  ring

-- we can *search* for proofs by using `exact?`

example (a : R) : a * 0 = 0 :=  by 
  exact?


theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, add_left_neg, zero_add]
