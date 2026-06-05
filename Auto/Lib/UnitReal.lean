import Auto.Lib.RealType

namespace Auto

def UnitReal : Type := Unit

namespace UnitReal

def elem : UnitReal := (() : Unit)

end UnitReal

instance : Inhabited UnitReal := ⟨UnitReal.elem⟩

instance : Zero UnitReal := ⟨UnitReal.elem⟩
instance : One  UnitReal := ⟨UnitReal.elem⟩
instance : Add  UnitReal := ⟨fun _ _ => UnitReal.elem⟩
instance : Sub  UnitReal := ⟨fun _ _ => UnitReal.elem⟩
instance : Neg  UnitReal := ⟨fun _   => UnitReal.elem⟩
instance : Mul  UnitReal := ⟨fun _ _ => UnitReal.elem⟩
instance : Div  UnitReal := ⟨fun _ _ => UnitReal.elem⟩
instance : Inv  UnitReal := ⟨fun _   => UnitReal.elem⟩
instance : Max  UnitReal := ⟨fun _ _ => UnitReal.elem⟩
instance : Min  UnitReal := ⟨fun _ _ => UnitReal.elem⟩
instance : LE UnitReal := ⟨fun _ _ => True⟩
instance : LT UnitReal := ⟨fun _ _ => True⟩

instance : NatCast UnitReal := ⟨fun _ => UnitReal.elem⟩
instance : IntCast UnitReal := ⟨fun _ => UnitReal.elem⟩
instance : OfScientific UnitReal := ⟨fun _ _ _ => UnitReal.elem⟩

instance : RealTy UnitReal := {}

end Auto
