import Auto.Tactic
import Mathlib

-- Standard Preprocessing Configs
set_option auto.redMode "reducible"
-- Standard SMT Configs
set_option trace.debug true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option auto.smt.solver.name "cvc5"
set_option auto.smt true
set_option auto.smt.trust true
-- set_option auto.tptp true
set_option auto.tptp.premiseSelection true
set_option auto.tptp.solver.name "zipperposition"
set_option trace.auto.tptp.result true
set_option trace.auto.tptp.printQuery true

-- set_option auto.tptp true
-- set_option trace.auto.tptp.printProof true

-- emulate native solver
-- set_option auto.native true
-- attribute [rebind Auto.Native.solverFunc] Auto.Solver.Native.emulateNative

#eval ((5 : ℤ) : ℝ)

example (x y z : Int) (h1 : x > y + 5) (h2 : y > z) : x ≠ z := by
  auto

example (x y z : Int) (h1 : x - 5 > y) (h2 : y > z) : x ≠ z := by
  auto

example (x y z : Rat) (h1 : x > y) (h2 : y > z) : x ≠ z := by
  auto

example (x y z : Real) (h1 : x > y) (h2 : y > z) : x ≠ z := by
  auto

example (x y z : Rat) (h1 : x > y + 5) (h2 : y > z) : x ≠ z := by
  auto

example (x : Rat × Rat) : x.1 ≤ x.2 ∨ x.1 > x.2 := by
  auto

#eval (5 / 3 : Rat) / 0

#eval (5.0 : Rat) / 0

#eval (OfScientific.ofScientific 5 False 5) / 0

example : 2.4 = (2.4 : Rat) := by
  auto

example : 1 + (2.4 : Rat) = 3.4 := by
  auto

example : 1 + (24 / 10 : Rat) = 17 / 5 := by
  auto

example : 1 + 5 * 3 = 16 := by
  auto

example : 0 = 10 / 0 := by
  auto

example : (1 : Rat) + 2.4 * 1 = 34 / 10 := by
  auto

example : 1 + (0.24 * 10 : Rat) = 34 / 10 := by
  auto

example (x y z : Rat) (h1 : x > y + (5 / 3)) (h2 : y > z) : x ≠ z := by
  auto

example (f : Int -> Int) (h1 : ∀ x y, x > y -> f x > f y) : ∀ x y, x ≠ y -> f x ≠ f y := by
  auto

example (f : Rat -> Rat) (h1 : ∀ x y, x > y -> f x > f y) : ∀ x y, x ≠ y -> f x ≠ f y := by
  auto

example (f : Nat → Nat) (h1 : ∀ x y, x < y → f x < y) : f 0 = 0 := by
  auto

-- Old QuerySMT Tests
-- Simple Int Inequalities
example (x y z : Rat) : x < y → y < z → x < z := by
  auto

example (x y z : Rat) : x < y → z < x → ¬z = y := by
  auto

example (w x : Int) (y z : Rat) : w <= x → x <= y → y <= z → z <= w → w = y := by
  auto

example (x : Int) (y z : Rat) : x <= y → y <= z → x = z → x = y ∧ y = z := by
  auto

example (x y z : Rat) : x > y + z → x < y → z < 0 := by
  auto

example (f : Int → Rat) (h1 : ∀ x y : Int, x < y → f x < f y) : ∀ x y : Int, x ≠ y → f x ≠ f y := by
  auto

example (f : Rat → Rat) (h1 : ∀ x y : Rat, f x + f y ≤ x + y) (h2 : f 0 = 0) : ∀ x : Rat, f x ≤ x := by
  auto

example (f : Rat → Rat) (h1 : ∀ x y : Rat, f x = f y → x = y) : ∀ x y : Rat, x ≠ y → f x ≠ f y := by
  auto

example (f : Rat → Int) (h1 : ∀ x y : Rat, x < y → f x < f y) : ∀ x y : Rat, f x = f y → x = y := by
 auto

example (f g : Rat → Rat) (h1 : ∀ x : Rat, f (g x) = x) : (∀ x y : Rat, x ≠ y → g x ≠ g y) ∧ (∀ y : Rat, ∃ x : Rat, f x = y) := by
  auto

-- Complex Algebraic Inequalities

example : ∀ y z w : Rat, ∃ x : Rat, x * y > z ∧ x * w < z → y > w  := by
  auto

example (a b c d : Rat) (h1 : a ≤ b) (h2 : c < d) : a + c < b + d := by
  auto

example (x y : Rat) (h : 2 * x + 1 < 2 * y) : x < y := by
  auto
