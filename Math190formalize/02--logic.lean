/-
Copyright (c) 2024 George McNinch. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Author : George McNinch
-/

/-
course: Math 190 - Tufts University
insructor: George McNinch
semester: 2024 Spring
-/

----------------------------------------------------------------------------------
-- 02 -- Logic in Lean
----------------------------------------------------------------------------------

import Mathlib.Tactic

variable (a b c: ℕ)

example : a * b * c = (a * b)  * c := by
 rfl
