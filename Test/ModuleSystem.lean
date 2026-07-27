module

/-
  `lean-auto` is migrated to Lean's module system, so `auto` and everything
  built on top of it can be used from files that begin with `module`.

  This test only relies on the emulated native solver, so it does not need any
  external prover to be installed. Note that `Auto.Solver.Native.emulateNative`
  discharges its goals using `sorryAx`, so the `sorry` warnings below are
  expected — what is being tested is that the whole pipeline (preprocessing,
  monomorphization, reification and verified-checker construction) runs.
-/

import Auto.Tactic

set_option auto.redMode "reducible"
set_option auto.tptp false
set_option auto.smt false
set_option auto.native true
attribute [rebind Auto.Native.solverFunc] Auto.Solver.Native.emulateNative

-- `auto`
example (a b : Prop) (h : a ∧ b) : b ∧ a := by auto
example (f : Nat → Nat) (h : ∀ x, f x = x) : f (f 3) = 3 := by auto

-- `auto 👎` and `auto 👍`
example : True := by (fail_if_success auto 👍); auto
example : False := by auto 👎

-- `mono` and `mononative`
example (a b : Prop) (h : a ∧ b) : b ∧ a := by mono; auto
example (a b : Prop) (h : a ∧ b) : b ∧ a := by mononative

-- Lemma databases
#declare_lemdb module_spec
attribute [lemdb module_spec] Nat.add_comm
#print_lemdb module_spec

example (a b : Nat) : a + b = b + a := by auto [*module_spec]

-- Debugging commands exported by `Auto`
set_option lazyReduce.logInfo false in
#lazyReduce (List.range 100).length

-- Auto's object-level embedding reduces as expected from a `module` file
open Auto.Embedding.Lam in
example : (LamTerm.base .trueE).maxEVarSucc = 0 := rfl
