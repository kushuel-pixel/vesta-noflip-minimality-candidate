import Mathlib

open FreeGroup

namespace Verify

/-- Free group on two generators `x = 0`, `y = 1`. -/
abbrev F := FreeGroup (Fin 2)

def x : F := FreeGroup.of 0
def y : F := FreeGroup.of 1
def X : F := x⁻¹
def Y : F := y⁻¹

/-- u = X y³ x Y⁴ -/
def u : F := X * y ^ 3 * x * Y ^ 4
/-- v = x Y³ -/
def v : F := x * Y ^ 3

/-- v · u · v⁻¹ = x Y³ X y³ x Y X -/
theorem conj_example : v * u * v⁻¹ = x * Y ^ 3 * X * y ^ 3 * x * Y * X := by
  decide +kernel

end Verify

#print axioms Verify.conj_example
