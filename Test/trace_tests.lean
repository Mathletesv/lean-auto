import Auto.Tactic
import Auto.MathlibReal

-- Standard Preprocessing Configs
set_option auto.redMode "reducible"
-- Standard SMT Configs
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option auto.smt.solver.name "cvc5"
set_option auto.smt true
set_option auto.smt.trust true

example (x y z : Real) (h1 : x > y) (h2 : y > z) : x ≠ z := by
  auto

example (x : Real) : max x (-x) ≥ 0 := by
  auto

example (x : Real) : min x (-x) ≤ 0 := by
  auto

example (x y z : Real) (h1 : x > y) (h2 : y > z) : x ≠ z := by
  auto

example (x y z : Real) (h1 : x > y + 5) (h2 : y > z) : x ≠ z := by
  auto

example (x : Real × Real) : x.1 ≤ x.2 ∨ x.1 > x.2 := by
  auto

example : 0.123124 = (0.123124 : Real) := by
  auto

example : 1.0 + (2.40 : Real) = 3.40 := by
  auto

example : (5.00000000000001 + 10) = (15.00000000000001 : Real) := by
  auto

example : 123400500 + -123400500 = (0 : Real) := by
  auto

example : (1 + (2.4 : Real) : Real) = ((3.4 : Real) : Real) := by
  auto

example : 1 + (24 / 10 : Real) = 17 / 5 := by
  auto

example : 1 + (0.24 * 10 : Real) = (34 / 10 : Real) := by
  auto

example (x y z : Real) (h1 : x > y + (5 / 3)) (h2 : y > z) : x ≠ z := by
  auto

example (f : Real -> Real) (h1 : ∀ x y, x > y -> f x > f y) : ∀ x y, x ≠ y -> f x ≠ f y := by
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

example (x y : Real) (h : 2 * x + 1 < 2 * y - 2) : x < y := by
  auto
