import Verify.RCoreObstruction

/-! Typed chronological fragment of fixed062 §2/§8, reviewed063 §5.
Only the eight used official IDs are represented. No full gap/classification
or equivalence to the Python word evaluator is claimed. -/

namespace Verify.ROperationConnection

abbrev State := Verify.F × Verify.F

inductive Move where
  | m2 | m3 | m4 | m5 | m6 | m8 | m10 | m13
  deriving DecidableEq

def moveId : Move → ℕ
  | .m2 => 2 | .m3 => 3 | .m4 => 4 | .m5 => 5
  | .m6 => 6 | .m8 => 8 | .m10 => 10 | .m13 => 13

def step : Move → State → State
  | .m2, (r, s) => (r * s, s)
  | .m3, (r, s) => (r * s⁻¹, s)
  | .m4, (r, s) => (r, s * r)
  | .m5, (r, s) => (r, s * r⁻¹)
  | .m6, (r, s) => (Verify.x * r * Verify.X, s)
  | .m8, (r, s) => (Verify.y * r * Verify.Y, s)
  | .m10, (r, s) => (r, Verify.x * s * Verify.X)
  | .m13, (r, s) => (r, Verify.Y * s * Verify.y)

def run : List Move → State → State
  | [], state => state
  | m :: ms, state => run ms (step m state)

def initial (n : ℕ) : State :=
  (ResearchWords.uFamily n, ResearchWords.vFamily n)

def cTwo : Verify.F := Verify.x ^ 2 * Verify.Y * Verify.X ^ 2

inductive Critical where
  | r8 | r13
  deriving DecidableEq

def criticalSeq : Critical → List Move
  | .r8 => [.m3, .m8, .m4]
  | .r13 => [.m3, .m13, .m4]

def preCritical (n : ℕ) (J K : List Move) : State :=
  run K (run [.m4, .m3] (run J (run [.m3, .m6, .m4] (initial n))))

def branch (n : ℕ) (J K F : List Move) (b : Critical) : State :=
  run F (run (criticalSeq b) (preCritical n J K))

theorem run_append (A B : List Move) (s : State) :
    run (A ++ B) s = run B (run A s) := by
  induction A generalizing s with
  | nil => rfl
  | cons m A ih => simpa only [List.cons_append, run] using ih (step m s)

theorem run_snd_fixed (moves : List Move) (s : State)
    (h : ∀ m ∈ moves, m = .m2 ∨ m = .m6) :
    (run moves s).2 = s.2 := by
  induction moves generalizing s with
  | nil => rfl
  | cons m ms ih =>
    have hm := h m (by simp)
    have ht : ∀ a ∈ ms, a = .m2 ∨ a = .m6 := fun a ha => h a (by simp [ha])
    rw [run, ih (step m s) ht]
    rcases hm with rfl | rfl <;> rfl

theorem run_fst_fixed (moves : List Move) (s : State)
    (h : ∀ m ∈ moves, m = .m5 ∨ m = .m10) :
    (run moves s).1 = s.1 := by
  induction moves generalizing s with
  | nil => rfl
  | cons m ms ih =>
    have hm := h m (by simp)
    have ht : ∀ a ∈ ms, a = .m5 ∨ a = .m10 := fun a ha => h a (by simp [ha])
    rw [run, ih (step m s) ht]
    rcases hm with rfl | rfl <;> rfl

theorem prefix_snd (n : ℕ) (hn : 6 ≤ n) :
    (run [.m3, .m6, .m4] (initial n)).2 = cTwo := by
  have hc := ResearchWords.c_expansion n 1 (by omega) (by decide)
  simp only [pow_one, Nat.sub_self, pow_zero, one_mul] at hc
  dsimp [initial, run, step]
  rw [hc]
  simp [ResearchWords.vFamily, cTwo, Verify.X, Verify.Y, pow_two, mul_assoc]

theorem middle43_fst (T C : Verify.F) :
    (run [.m4, .m3] (T, C)).1 = C⁻¹ := by
  dsimp [run, step]
  group

theorem cTwo_inv : cTwo⁻¹ = RCoreObstruction.rP := by
  dsimp [cTwo, RCoreObstruction.rP, Verify.X, Verify.Y]
  group

theorem preCritical_fst (n : ℕ) (J K : List Move) (hn : 6 ≤ n)
    (hJ : ∀ m ∈ J, m = .m2 ∨ m = .m6)
    (hK : ∀ m ∈ K, m = .m5 ∨ m = .m10) :
    (preCritical n J K).1 = RCoreObstruction.rP := by
  unfold preCritical
  rw [run_fst_fixed K _ hK]
  have hC := (run_snd_fixed J (run [.m3, .m6, .m4] (initial n)) hJ).trans
    (prefix_snd n hn)
  have hm := middle43_fst
    (run J (run [.m3, .m6, .m4] (initial n))).1
    (run J (run [.m3, .m6, .m4] (initial n))).2
  change (run [.m4, .m3] _).1 = _ at hm
  rw [hm, hC, cTwo_inv]

theorem r8_snd (P Q : Verify.F) :
    (run (criticalSeq .r8) (P, Q)).2 = Q * Verify.y * P * Q⁻¹ * Verify.Y := by
  dsimp [criticalSeq, run, step]
  simp only [mul_assoc]

theorem r13_snd (P Q : Verify.F) :
    (run (criticalSeq .r13) (P, Q)).2 = Verify.Y * Q * Verify.y * P * Q⁻¹ := by
  dsimp [criticalSeq, run, step]
  simp only [mul_assoc]

theorem required_equation (b : Critical) (P Q : Verify.F)
    (h : (run (criticalSeq b) (P, Q)).2 = Verify.y) :
    Q * (Verify.y * P) * Q⁻¹ = Verify.y ^ 2 := by
  cases b with
  | r8 =>
    rw [r8_snd] at h
    have hh := congrArg (fun z : Verify.F => z * Verify.y) h
    simpa [Verify.Y, pow_two, mul_assoc] using hh
  | r13 =>
    rw [r13_snd] at h
    have hh := congrArg (fun z : Verify.F => Verify.y * z) h
    simpa [Verify.Y, pow_two, mul_assoc] using hh

theorem branch_eq_run (n : ℕ) (J K F : List Move) (b : Critical) :
    branch n J K F b =
      run ([.m3, .m6, .m4] ++ J ++ [.m4, .m3] ++ K ++ criticalSeq b ++ F)
        (initial n) := by
  simp only [run_append, branch, preCritical]

theorem branch_required (n : ℕ) (J K F : List Move) (b : Critical) (hn : 6 ≤ n)
    (hJ : ∀ m ∈ J, m = .m2 ∨ m = .m6)
    (hK : ∀ m ∈ K, m = .m5 ∨ m = .m10)
    (hF : ∀ m ∈ F, m = .m2 ∨ m = .m6)
    (h : (branch n J K F b).2 = Verify.y) :
    (preCritical n J K).2 * RCoreObstruction.rStem * (preCritical n J K).2⁻¹ =
      Verify.y ^ 2 := by
  unfold branch at h
  rw [run_snd_fixed F _ hF] at h
  have hp := preCritical_fst n J K hn hJ hK
  have pair : preCritical n J K = (RCoreObstruction.rP, (preCritical n J K).2) :=
    Prod.ext hp rfl
  rw [pair] at h
  exact required_equation b RCoreObstruction.rP (preCritical n J K).2 h

theorem branch_excluded (n : ℕ) (J K F : List Move) (b : Critical) (hn : 6 ≤ n)
    (hJ : ∀ m ∈ J, m = .m2 ∨ m = .m6)
    (hK : ∀ m ∈ K, m = .m5 ∨ m = .m10)
    (hF : ∀ m ∈ F, m = .m2 ∨ m = .m6) :
    (branch n J K F b).2 ≠ Verify.y := by
  intro h
  exact RCoreObstruction.no_r_conjugator (preCritical n J K).2
    (branch_required n J K F b hn hJ hK hF h)

end Verify.ROperationConnection

#print axioms Verify.ROperationConnection.run_append
#print axioms Verify.ROperationConnection.run_snd_fixed
#print axioms Verify.ROperationConnection.run_fst_fixed
#print axioms Verify.ROperationConnection.prefix_snd
#print axioms Verify.ROperationConnection.middle43_fst
#print axioms Verify.ROperationConnection.cTwo_inv
#print axioms Verify.ROperationConnection.preCritical_fst
#print axioms Verify.ROperationConnection.r8_snd
#print axioms Verify.ROperationConnection.r13_snd
#print axioms Verify.ROperationConnection.required_equation
#print axioms Verify.ROperationConnection.branch_eq_run
#print axioms Verify.ROperationConnection.branch_required
#print axioms Verify.ROperationConnection.branch_excluded
