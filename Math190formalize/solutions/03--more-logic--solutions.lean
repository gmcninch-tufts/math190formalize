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
-- 03 -- more logic
----------------------------------------------------------------------------------

import Mathlib.Tactic


-- problem 1.1
example : (P → Q → R) → P ∧ Q → R := by
  intro h ⟨ xp, xq ⟩
  exact h xp xq
  done

-- problem 1.2
example : P → Q → P ∧ Q := by
  intro xp xq
  exact ⟨ xp, xq ⟩
  done

-- problem 1.3
/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro ⟨ xp, xq ⟩
  exact ⟨ xq, xp ⟩
  done

-- problem 1.4
example : P → P ∧ True := by
  intro xp
  constructor  -- now we just need to construct terms of the components of the and-proposition
  · exact  xp
  · triv
  done

-- **or**

-- problem 1.4
example : P → P ∧ True := by
  intro xp
  exact ⟨ xp, True.intro ⟩
  done

-- **or**

-- problem 1.4
example : P → P ∧ True := λ xp => ⟨ xp, True.intro ⟩



-- problem 1.5
example : False → P ∧ False := by
  intro f
  exfalso
  exact f
  done

-- problem 1.6
/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro ⟨ xp, _ ⟩ ⟨ _, yr ⟩
  constructor
  · exact xp
  · exact yr
  done

-- **or**

-- problem 1.6
/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := λ (And.intro xp _) (And.intro _ yr) => And.intro xp yr

-- problem 1.7
example : (P ∧ Q → R) → P → Q → R := by
  intro hpqr
  intro p q
  exact hpqr (And.intro p q)
  done

-- **or**

-- problem 1.7
example : (P ∧ Q → R) → P → Q → R := by
  intro hpqr
  intro p q
  apply hpqr
  constructor
  · exact p
  · exact q
  done


--------------------------------------------------------------------------------
-- problems for you to work on -- group 2


-- problem 2.1
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hepq heqr
  have hpr : P → R := by
    intro p
    exact heqr.mp (hepq.mp p)
  have hrp : R → P := by
    intro r
    exact hepq.mpr (heqr.mpr r)
  exact ⟨ hpr, hrp ⟩
  done

-- problem 2.2

example : P ∧ Q ↔ Q ∧ P := by
  have and_symm { A B : Prop} (h : A ∧ B) : B ∧ A := by
    exact ⟨ h.2, h.1 ⟩
  have hf : P ∧ Q → Q ∧ P := by
    intro hpq
    exact and_symm hpq
  have hr : Q ∧ P → P ∧ Q := by
    intro hqp
    exact and_symm hqp
  exact ⟨ hf, hr ⟩
  done

-- problem 2.3
example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  sorry
  done

-- problem 2.4
example : P ↔ P ∧ True := by
  sorry
  done

-- problem 2.5
example : False ↔ P ∧ False := by
  sorry
  done

-- problem 2.6
example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  sorry
  done

-- problem 2.7
example : ¬(P ↔ ¬P) := by
  sorry
  done
