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

import Mathlib.Tactic

--------------------------------------------------------------------------------
-- 07 --Algebra (Linear algebra)
--------------------------------------------------------------------------------

-- We've seen a bit about using `structures` and `classes`to create
-- objects representing common mathematical abstractions in `Lean`.
-- Here I want to explore some of these ideas in the context of *linear algebra*.

-- but let me start by developing some of the API for *groups* and their subgroups

-- For the same reason that a subset is not a type, a subgroup is not a group.
-- If `G` is a group -- i.e.

variable (G : Type) [Group G]


-- then the type of all subgroups of `G` is written `Subgroup G`. Thus
-- to specify a subgroup `H` of `G` one says:

variable (H : Subgroup G)

-- Now, the group `G` is written multiplicatively, otherwise, you'd
-- specify `AdditiveGroup` like this (I'm including a `CommGroup`
-- instance because to me additive groups should be commutative...).

variable (A : Type) [AddGroup A] [CommGroup A]

variable (B : Subgroup A)

-- now the multiplicative group `G` has a *multiplicative 


