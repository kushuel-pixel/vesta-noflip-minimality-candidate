import Verify.ResearchWords

/-!
The integral three-coordinate group with multiplication
`(a,b,c) * (a',b',c') = (a+a', b+b', c+c'-b*a')`.
This file establishes a group and a free-group homomorphism without assuming
reachability or any contribution condition. Static research reviews are source
scope references, not proof assumptions.
-/

namespace Verify.QModel

@[ext]
structure Q where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq

/-- Explicit identification with the stated underlying set `ℤ³`. -/
def coordinates : Q ≃ ℤ × ℤ × ℤ where
  toFun p := (p.a, p.b, p.c)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instMulQ : Mul Q :=
  ⟨fun p q => ⟨p.a + q.a, p.b + q.b, p.c + q.c - p.b * q.a⟩⟩
instance instOneQ : One Q := ⟨⟨0, 0, 0⟩⟩
instance instInvQ : Inv Q := ⟨fun p => ⟨-p.a, -p.b, -p.c - p.a * p.b⟩⟩

instance instGroupQ : Group Q where
  mul := instMulQ.mul
  one := instOneQ.one
  inv := instInvQ.inv
  mul_assoc p q r := by
    apply Q.ext
    · change (p.a + q.a) + r.a = p.a + (q.a + r.a)
      ring
    · change (p.b + q.b) + r.b = p.b + (q.b + r.b)
      ring
    · change (p.c + q.c - p.b * q.a) + r.c - (p.b + q.b) * r.a =
        p.c + (q.c + r.c - q.b * r.a) - p.b * (q.a + r.a)
      ring
  one_mul p := by
    apply Q.ext
    · change 0 + p.a = p.a
      ring
    · change 0 + p.b = p.b
      ring
    · change 0 + p.c - 0 * p.a = p.c
      ring
  mul_one p := by
    apply Q.ext
    · change p.a + 0 = p.a
      ring
    · change p.b + 0 = p.b
      ring
    · change p.c + 0 - p.b * 0 = p.c
      ring
  inv_mul_cancel p := by
    apply Q.ext
    · change -p.a + p.a = 0
      ring
    · change -p.b + p.b = 0
      ring
    · change (-p.c - p.a * p.b) + p.c - (-p.b) * p.a = 0
      ring

@[simp] theorem mul_a (p q : Q) : (p * q).a = p.a + q.a := rfl
@[simp] theorem mul_b (p q : Q) : (p * q).b = p.b + q.b := rfl
@[simp] theorem mul_c (p q : Q) : (p * q).c = p.c + q.c - p.b * q.a := rfl
@[simp] theorem one_a : (1 : Q).a = 0 := rfl
@[simp] theorem one_b : (1 : Q).b = 0 := rfl
@[simp] theorem one_c : (1 : Q).c = 0 := rfl
@[simp] theorem inv_a (p : Q) : p⁻¹.a = -p.a := rfl
@[simp] theorem inv_b (p : Q) : p⁻¹.b = -p.b := rfl
@[simp] theorem inv_c (p : Q) : p⁻¹.c = -p.c - p.a * p.b := rfl

theorem mul_coordinates (p q : Q) :
    p * q = ⟨p.a + q.a, p.b + q.b, p.c + q.c - p.b * q.a⟩ := rfl

theorem inv_coordinates (p : Q) :
    p⁻¹ = ⟨-p.a, -p.b, -p.c - p.a * p.b⟩ := rfl

@[simp] theorem conj_a (h w : Q) : (h * w * h⁻¹).a = w.a := by simp
@[simp] theorem conj_b (h w : Q) : (h * w * h⁻¹).b = w.b := by simp
theorem conj_c (h w : Q) :
    (h * w * h⁻¹).c = w.c + h.a * w.b - h.b * w.a := by
  simp only [mul_b, mul_c, inv_a, inv_c]
  ring

theorem conj_c_sub (h w : Q) :
    (h * w * h⁻¹).c - w.c = h.a * w.b - h.b * w.a := by
  rw [conj_c]
  ring

theorem conj_coordinates (h w : Q) :
    h * w * h⁻¹ = ⟨w.a, w.b, w.c + h.a * w.b - h.b * w.a⟩ := by
  apply Q.ext
  · exact conj_a h w
  · exact conj_b h w
  · exact conj_c h w

/-- The first two coordinates determine conjugation; a zero pair is central. -/
theorem conj_eq_of_ab_zero (h w : Q) (ha : h.a = 0) (hb : h.b = 0) :
    h * w * h⁻¹ = w := by
  rw [conj_coordinates]
  apply Q.ext <;> simp [ha, hb]

def qx : Q := ⟨1, 0, 0⟩
def qy : Q := ⟨0, 1, 0⟩

/-- The two free generators map to `qx` and `qy`. -/
def toQ : Verify.F →* Q :=
  FreeGroup.lift (fun i : Fin 2 => if i = 0 then qx else qy)

@[simp] theorem toQ_x : toQ Verify.x = qx := by simp [toQ, Verify.x]
@[simp] theorem toQ_y : toQ Verify.y = qy := by simp [toQ, Verify.y]
@[simp] theorem toQ_X : toQ Verify.X = qx⁻¹ := by simp [Verify.X]
@[simp] theorem toQ_Y : toQ Verify.Y = qy⁻¹ := by simp [Verify.Y]

@[simp] theorem toQ_x_a : (toQ Verify.x).a = 1 := by rw [toQ_x]; rfl
@[simp] theorem toQ_x_b : (toQ Verify.x).b = 0 := by rw [toQ_x]; rfl
@[simp] theorem toQ_x_c : (toQ Verify.x).c = 0 := by rw [toQ_x]; rfl
@[simp] theorem toQ_y_a : (toQ Verify.y).a = 0 := by rw [toQ_y]; rfl
@[simp] theorem toQ_y_b : (toQ Verify.y).b = 1 := by rw [toQ_y]; rfl
@[simp] theorem toQ_y_c : (toQ Verify.y).c = 0 := by rw [toQ_y]; rfl
@[simp] theorem toQ_X_a : (toQ Verify.X).a = -1 := by simp [qx]
@[simp] theorem toQ_X_b : (toQ Verify.X).b = 0 := by simp [qx]
@[simp] theorem toQ_X_c : (toQ Verify.X).c = 0 := by simp [qx]
@[simp] theorem toQ_Y_a : (toQ Verify.Y).a = 0 := by simp [qy]
@[simp] theorem toQ_Y_b : (toQ Verify.Y).b = -1 := by simp [qy]
@[simp] theorem toQ_Y_c : (toQ Verify.Y).c = 0 := by simp [qy]

theorem qy_pow (n : ℕ) : qy ^ n = ⟨0, (n : ℤ), 0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    apply Q.ext <;> simp [qy, Nat.cast_add, Nat.cast_one]

theorem qy_inv_pow (n : ℕ) : qy⁻¹ ^ n = ⟨0, -(n : ℤ), 0⟩ := by
  rw [inv_pow, qy_pow]
  apply Q.ext <;> simp

/-- Both initial images are valid for every natural `n`; no lower bound is used. -/
theorem toQ_uFamily (n : ℕ) :
    toQ (Verify.ResearchWords.uFamily n) = ⟨0, -1, -(n : ℤ)⟩ := by
  simp only [Verify.ResearchWords.uFamily, map_mul, map_pow, toQ_X, toQ_y, toQ_x,
    toQ_Y, qy_pow, qy_inv_pow]
  apply Q.ext <;> simp [qx, Nat.cast_add, Nat.cast_one]

theorem toQ_vFamily (n : ℕ) :
    toQ (Verify.ResearchWords.vFamily n) = ⟨1, -(n : ℤ), 0⟩ := by
  simp only [Verify.ResearchWords.vFamily, map_mul, map_pow, toQ_x, toQ_Y, qy_inv_pow]
  apply Q.ext <;> simp [qx]

end Verify.QModel

#print axioms Verify.QModel.Q
#print axioms Verify.QModel.coordinates
#print axioms Verify.QModel.instMulQ
#print axioms Verify.QModel.instOneQ
#print axioms Verify.QModel.instInvQ
#print axioms Verify.QModel.instGroupQ
#print axioms Verify.QModel.mul_a
#print axioms Verify.QModel.mul_b
#print axioms Verify.QModel.mul_c
#print axioms Verify.QModel.one_a
#print axioms Verify.QModel.one_b
#print axioms Verify.QModel.one_c
#print axioms Verify.QModel.inv_a
#print axioms Verify.QModel.inv_b
#print axioms Verify.QModel.inv_c
#print axioms Verify.QModel.mul_coordinates
#print axioms Verify.QModel.inv_coordinates
#print axioms Verify.QModel.conj_a
#print axioms Verify.QModel.conj_b
#print axioms Verify.QModel.conj_c
#print axioms Verify.QModel.conj_c_sub
#print axioms Verify.QModel.conj_coordinates
#print axioms Verify.QModel.conj_eq_of_ab_zero
#print axioms Verify.QModel.qx
#print axioms Verify.QModel.qy
#print axioms Verify.QModel.toQ
#print axioms Verify.QModel.toQ_x
#print axioms Verify.QModel.toQ_y
#print axioms Verify.QModel.toQ_X
#print axioms Verify.QModel.toQ_Y
#print axioms Verify.QModel.toQ_x_a
#print axioms Verify.QModel.toQ_x_b
#print axioms Verify.QModel.toQ_x_c
#print axioms Verify.QModel.toQ_y_a
#print axioms Verify.QModel.toQ_y_b
#print axioms Verify.QModel.toQ_y_c
#print axioms Verify.QModel.toQ_X_a
#print axioms Verify.QModel.toQ_X_b
#print axioms Verify.QModel.toQ_X_c
#print axioms Verify.QModel.toQ_Y_a
#print axioms Verify.QModel.toQ_Y_b
#print axioms Verify.QModel.toQ_Y_c
#print axioms Verify.QModel.qy_pow
#print axioms Verify.QModel.qy_inv_pow
#print axioms Verify.QModel.toQ_uFamily
#print axioms Verify.QModel.toQ_vFamily
#print axioms Verify.QModel.Q.a
#print axioms Verify.QModel.Q.b
#print axioms Verify.QModel.Q.c
#print axioms Verify.QModel.Q.casesOn
#print axioms Verify.QModel.Q.ctorIdx
#print axioms Verify.QModel.Q.ext
#print axioms Verify.QModel.Q.ext_iff
#print axioms Verify.QModel.Q.mk
#print axioms Verify.QModel.Q.mk.inj
#print axioms Verify.QModel.Q.mk.injEq
#print axioms Verify.QModel.Q.mk.noConfusion
#print axioms Verify.QModel.Q.mk.sizeOf_spec
#print axioms Verify.QModel.Q.noConfusion
#print axioms Verify.QModel.Q.noConfusionType
#print axioms Verify.QModel.Q.rec
#print axioms Verify.QModel.Q.recOn
#print axioms Verify.QModel.instDecidableEqQ
#print axioms Verify.QModel.instDecidableEqQ.decEq

/-! Exact interface types are emitted for downstream evidence. -/
set_option pp.fullNames true
#check Verify.QModel.Q
#check Verify.QModel.coordinates
#check Verify.QModel.instMulQ
#check Verify.QModel.instOneQ
#check Verify.QModel.instInvQ
#check Verify.QModel.instGroupQ
#check Verify.QModel.mul_a
#check Verify.QModel.mul_b
#check Verify.QModel.mul_c
#check Verify.QModel.one_a
#check Verify.QModel.one_b
#check Verify.QModel.one_c
#check Verify.QModel.inv_a
#check Verify.QModel.inv_b
#check Verify.QModel.inv_c
#check Verify.QModel.mul_coordinates
#check Verify.QModel.inv_coordinates
#check Verify.QModel.conj_a
#check Verify.QModel.conj_b
#check Verify.QModel.conj_c
#check Verify.QModel.conj_c_sub
#check Verify.QModel.conj_coordinates
#check Verify.QModel.conj_eq_of_ab_zero
#check Verify.QModel.qx
#check Verify.QModel.qy
#check Verify.QModel.toQ
#check Verify.QModel.toQ_x
#check Verify.QModel.toQ_y
#check Verify.QModel.toQ_X
#check Verify.QModel.toQ_Y
#check Verify.QModel.toQ_x_a
#check Verify.QModel.toQ_x_b
#check Verify.QModel.toQ_x_c
#check Verify.QModel.toQ_y_a
#check Verify.QModel.toQ_y_b
#check Verify.QModel.toQ_y_c
#check Verify.QModel.toQ_X_a
#check Verify.QModel.toQ_X_b
#check Verify.QModel.toQ_X_c
#check Verify.QModel.toQ_Y_a
#check Verify.QModel.toQ_Y_b
#check Verify.QModel.toQ_Y_c
#check Verify.QModel.qy_pow
#check Verify.QModel.qy_inv_pow
#check Verify.QModel.toQ_uFamily
#check Verify.QModel.toQ_vFamily
#print prefix Verify.QModel
