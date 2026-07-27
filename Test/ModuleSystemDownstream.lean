module

/-
  A downstream `module` that builds its own tactic on top of `Auto.runAuto`,
  the way `Hammer` and `lean-smt` do.

  Plain `import Auto.Tactic` is enough to *invoke* `auto` (see
  `Test/ModuleSystem.lean`), but a metaprogram that refers to `lean-auto`'s
  own declarations additionally needs `meta import` — see the documentation of
  `meta` in Lean's module system. `public import` is used here because the
  `elab` command below introduces a public declaration whose type
  (`Lean.Elab.Tactic.Tactic`) has to be publicly visible.
-/

public import Auto.Tactic
meta import Auto.Tactic

set_option auto.redMode "reducible"
set_option auto.tptp false
set_option auto.smt false
set_option auto.native true
attribute [rebind Auto.Native.solverFunc] Auto.Solver.Native.emulateNative

-- A downstream tactic built on top of `Auto.runAuto`
open Lean Elab Tactic in
meta def myAuto : TacticM Unit := withMainContext do
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let (lemmas, inhFacts) ← Auto.collectAllLemmas (← `(Auto.hints| )) #[] (goalBinders.push ngoal)
    absurd.assign (← Auto.runAuto (← Term.getDeclName?) lemmas inhFacts)

elab "my_auto" : tactic => myAuto

example (a b : Prop) (h : a ∧ b) : b ∧ a := by my_auto
