import Auto.Lib.RealType

/-!
# `UnitReal` — a Mathlib-free placeholder real carrier

`DefaultReal` exists only to fill the `R` type parameter of `LamValuation R`
(and the reconstruction proof terms built over it) for goals that do **not**
reason about reals — e.g. pure `Nat`/`Int`/`Bool`/`BitVec` goals.

Soundness argument: such proofs mention `R` in their *type* but never force any
`RealTy` operation, so the junk operations defined below are never evaluated.
The carrier is `Unit`, so every operation is total and computable (no
`noncomputable`, no `Classical`).

When `Auto.Reals` is imported, the registry overrides `R` with Mathlib's `ℝ`,
and real *recognition* (the forward reification handler) only fires there — so a
goal that genuinely reasons about reals never receives `DefaultReal` as its
carrier. `DefaultReal` is purely the type-slot filler for the real-free path.

NOTE ON THE CLASS NAME: this file assumes the carrier class is `Auto.RealTy`.
If yours is still named `Auto.Real`, replace `RealTy` with `Real` below.
-/

namespace Auto

/-- Mathlib-free placeholder real carrier. Defined as `Unit`, but kept as a
    `def` (not `abbrev`) so instance search does not see through it to `Unit`'s
    own instances — only the explicit instances below apply. -/
def DefaultReal : Type := Unit

namespace DefaultReal

/-- The single inhabitant, written once so the instances below read uniformly. -/
@[reducible] def star : DefaultReal := (() : Unit)

end DefaultReal

instance : Inhabited DefaultReal := ⟨DefaultReal.star⟩

-- Value-producing operations: every result is the unique inhabitant.
instance : Zero DefaultReal := ⟨DefaultReal.star⟩
instance : One  DefaultReal := ⟨DefaultReal.star⟩
instance : Add  DefaultReal := ⟨fun _ _ => DefaultReal.star⟩
instance : Sub  DefaultReal := ⟨fun _ _ => DefaultReal.star⟩
instance : Neg  DefaultReal := ⟨fun _   => DefaultReal.star⟩
instance : Mul  DefaultReal := ⟨fun _ _ => DefaultReal.star⟩
instance : Div  DefaultReal := ⟨fun _ _ => DefaultReal.star⟩
instance : Inv  DefaultReal := ⟨fun _   => DefaultReal.star⟩
instance : Max  DefaultReal := ⟨fun _ _ => DefaultReal.star⟩
instance : Min  DefaultReal := ⟨fun _ _ => DefaultReal.star⟩

-- Casts.
instance : NatCast DefaultReal := ⟨fun _ => DefaultReal.star⟩
instance : IntCast DefaultReal := ⟨fun _ => DefaultReal.star⟩

-- Scientific literals: `OfScientific.ofScientific : Nat → Bool → Nat → α`.
instance : OfScientific DefaultReal := ⟨fun _ _ _ => DefaultReal.star⟩

-- Order relations are `Prop`-valued; pick the trivially-true relation.
instance : LE DefaultReal := ⟨fun _ _ => True⟩
instance : LT DefaultReal := ⟨fun _ _ => True⟩

/-- Assemble the carrier class from the parent instances above.
    If `RealTy`'s `extends` does not auto-gather every parent through `{}`,
    fill the fields explicitly with `toZero := inferInstance`, etc. -/
instance : RealTy DefaultReal := {}

end Auto
