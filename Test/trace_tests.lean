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

example (x y z : Real) (h1 : x > y) (h2 : y > z) : x ≠ z := by
  auto

example (x y : Nat) (h1 : x * x > y * y) : x > y := by
  auto

example (x y z : Real) (h1 : x > y) (h2 : y > z) : x ≠ z := by
  auto

example (x y z : Real) (h1 : x > y + 5) (h2 : y > z) : x ≠ z := by
  auto

example (x : Real × Real) : x.1 ≤ x.2 ∨ x.1 > x.2 := by
  auto

example : (10 : Int) / (0 : Int) = 0 := by
  auto

example : 10 / 0 = (0 : Int) := by
  auto

example : 10 * 0 = (0 : Int) := by
  auto

example : 10 % 0 = (10 : Int) := by
  auto

example : 10 / 0 = (0 : Real) := by
  auto

example (h1 : ∀ x : Real, Real.sqrt x * Real.sqrt x = x) : Real.sqrt 4.0 = 2 := by
  auto

example : 10 / 0 = (0 : Real) := by
  auto

example : 10 % (0 : Real) = 10 := by
  simp

-- div by 0 is always 0, x % 0 is always x?

#eval (5 / 3 : Real) / 0

#eval (5.0 : Real) / 0

#eval (OfScientific.ofScientific 5 False 5) / 0

example : 2.4 = (2.4 : Real) := by
  auto

example : 1 + (2.4 : Real) = 3.4 := by
  auto

example : 1 + (2.4 : Real) = 3.4 := by
  auto

example : 1 + (2 : Real) = 3 := by
  auto

example : 1 + (-1 : Real) = 0 := by
  auto

example : (0 : Real) = 0 := by
  auto

example : (1 + (2.4 : Real) : Real) = ((3.4 : Real) : Real) := by
  auto

example : 1 + (24 / 10 : Real) = 17 / 5 := by
  auto

example : 1 + 5 * 3 = 16 := by
  auto

example : 0 = 10 / 0 := by
  auto

example : (1 : Real) + 2.4 * 1 = 34 / 10 := by
  auto

example : 1 + (0.24 * 10 : Real) = (34 / 10 : Real) := by
  auto

example (x y z : Real) (h1 : x > y + (5 / 3)) (h2 : y > z) : x ≠ z := by
  auto

example (f : Int -> Int) (h1 : ∀ x y, x > y -> f x > f y) : ∀ x y, x ≠ y -> f x ≠ f y := by
  auto

example (f : Real -> Real) (h1 : ∀ x y, x > y -> f x > f y) : ∀ x y, x ≠ y -> f x ≠ f y := by
  auto

example (f : Nat → Nat) (h1 : ∀ x y, x < y → f x < y) : f 0 = 0 := by
  auto

-- Old QuerySMT Tests
-- Simple Int Inequalities
example (x y z : Real) : x < y → y < z → x < z := by
  auto

example (x y z : Real) : x < y → z < x → ¬z = y := by
  auto

example (w x : Int) (y z : Real) : w <= x → x <= y → y <= z → z <= w → w = y := by
  auto

example (x : Int) (y z : Real) : x <= y → y <= z → x = z → x = y ∧ y = z := by
  auto

example (x y z : Real) : x > y + z → x < y → z < 0 := by
  auto

example (f : Int → Real) (h1 : ∀ x y : Int, x < y → f x < f y) : ∀ x y : Int, x ≠ y → f x ≠ f y := by
  auto

example (f : Real → Real) (h1 : ∀ x y : Real, f x + f y ≤ x + y) (h2 : f 0 = 0) : ∀ x : Real, f x ≤ x := by
  auto

example (f : Real → Real) (h1 : ∀ x y : Real, f x = f y → x = y) : ∀ x y : Real, x ≠ y → f x ≠ f y := by
  auto

example (f : Real → Int) (h1 : ∀ x y : Real, x < y → f x < f y) : ∀ x y : Real, f x = f y → x = y := by
 auto

example (f g : Real → Real) (h1 : ∀ x : Real, f (g x) = x) : (∀ x y : Real, x ≠ y → g x ≠ g y) ∧ (∀ y : Real, ∃ x : Real, f x = y) := by
  auto

-- Complex Algebraic Inequalities

example : ∀ y z w : Real, ∃ x : Real, x * y > z ∧ x * w < z → y > w  := by
  auto

example : ∀ y z w : Real, ∃ x : Real, x * y > z ∧ x * w < z → y > w  := by
  auto

example (a b c d : Real) (h1 : a ≤ b) (h2 : c < d) : a + c < b + d := by
  auto

example (a b c d : Real) (h1 : a ≤ b) (h2 : c < d) : a + c < b + d := by
  auto

example (x y : Real) (h : 2 * x + 1 < 2 * y - 2) : x < y := by
  auto

example (x y : Real) (h : 2 * x + 1 < 2 * y - (2 : Int)) : x < y := by  -- remove nat cast
  auto

-- [debug] not atomized: 1
-- [debug] process app @OfNat.ofNat ℚ 1, Real.instOfNat, 1
-- [debug] process app more: [ℚ, 1, Real.instOfNat] @OfNat.ofNat OfNat.ofNat [0]
-- [debug] otherProcess 1
-- [debug] processComplexTermExpr: 1, 0, @OfNat.ofNat, [ℚ, 1, Real.instOfNat]
-- [debug] happened : 1 @OfNat.ofNat ℚ 1 Real.instOfNat

example (x y : Real) (h : 2 * x + 1 < 2 * y - 2) : x < y := by
  auto
