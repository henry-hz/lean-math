import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import MIL.Common

-- https://leanprover.github.io/theorem_proving_in_lean4/
-- https://leanprover-community.github.io/mathematics_in_lean/C01_Introduction.html#getting-started

open Nat

-- There are no exercises in this section.

-- ¬ \not ∧ \and ∨ \or
-- → \-> ↔ \<-> ∀ \fo
-- ∃ \ex ≤ \<= ≥ \>=
-- 6= \neq ≈ \~~ × \x
-- ◦ \circ ∅ \empty ∪ \union
-- ∩ \intersect ∈ \in  \downleftharpoon
-- # \bigcirc ← \<- 7→ \mapsto
-- ⇒ \=> ⇒⇒ \==> J \[[
-- K \]] N \N Z \Z
-- Q \Q R \R α \a
-- β \b γ \g δ \de
-- ε \e λ \la σ \s
-- 0 \0 1 \1 2 \2
-- 3 \3 4 \4 5 \5
-- 6 \6 7 \7 8 \8
-- 9 \9

#check 2 + 2


def f (x : ℕ) :=
  x + 3

#check f
#eval f 100


-- constant f : ℤ → ℤ

inductive nat : Type
| zero : nat
| succ : nat → nat

#check 2 + 2     -- type ℕ
#check 2 + 2 = 4 -- type Prop

-- type Prop are mathematical statements

def FermaTheorem :=
  ∀ x y z n : ℕ, n > 2 && x * y * z != 0 ⟶ x ^ n + y ^ n != z ^ n

#check FermaTheorem

theorem easy : 2 + 2 = 4 :=
  rfl

#check easy

theorem hard : FermaTheorem :=
  sorry

#check hard


example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩

example : ∀ m n : Nat, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩

example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- Say m and n are natural numbers, and assume n=2*k.
  rintro m n ⟨k, hk⟩
  -- We need to prove m*n is twice a natural number. Let's show it's twice m*k.
  use m * k
  -- Substitute for n,
  rw [hk]
  -- and now it's obvious.
  ring