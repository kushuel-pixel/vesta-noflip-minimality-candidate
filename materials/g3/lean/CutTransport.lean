import RawDeletionCriterion

namespace Candidate.CutTransport
open Verify.AtomicSemantics Candidate.RawDeletionCriterion

def Compatible (d : Move) (oldState newState : GroupState) : Prop :=
  newState = groupStep d oldState

def CommutesAt (d m : Move) (s : GroupState) : Prop :=
  groupStep m (groupStep d s) = groupStep d (groupStep m s)

theorem compatible_step_iff {d m : Move} {s t : GroupState}
    (h : Compatible d s t) :
    Compatible d (groupStep m s) (groupStep m t) ↔ CommutesAt d m s := by
  unfold Compatible at h ⊢
  rw [h]
  rfl

theorem same_axis_iff (d : Move) (s t : GroupState) :
    Compatible d (groupStep d s) (groupStep d t) ↔ Compatible d s t := by
  unfold Compatible
  exact (groupStep_injective d).eq_iff

theorem repeat_axis_iff (d : Move) (k : ℕ) (s t : GroupState) :
    Compatible d (groupRun (List.replicate k d) s)
      (groupRun (List.replicate k d) t) ↔ Compatible d s t := by
  induction k generalizing s t with
  | zero => rfl
  | succ k ih =>
    simpa only [List.replicate_succ,groupRun,ih] using same_axis_iff d s t

def CommutesAlong (d : Move) : List Move → GroupState → Prop
  | [], _ => True
  | m :: ms, s => CommutesAt d m s ∧ CommutesAlong d ms (groupStep m s)

theorem compatible_run {d : Move} (ms : List Move) {s t : GroupState}
    (hc : Compatible d s t) (ha : CommutesAlong d ms s) :
    Compatible d (groupRun ms s) (groupRun ms t) := by
  induction ms generalizing s t with
  | nil => exact hc
  | cons m ms ih =>
    exact ih ((compatible_step_iff hc).mpr ha.1) ha.2

def conjFirst (g : Verify.F) (s : GroupState) : GroupState :=
  (g*s.1*g⁻¹,s.2)
def conjSecond (g : Verify.F) (s : GroupState) : GroupState :=
  (s.1,g*s.2*g⁻¹)

theorem m2_conjFirst_iff (g : Verify.F) (s : GroupState) :
    conjFirst g (groupStep .m2 s) = groupStep .m2 (conjFirst g s) ↔
    g*s.2 = s.2*g := by
  rcases s with ⟨r,s⟩
  simp only [conjFirst,groupStep,Prod.mk.injEq,and_true]
  constructor
  · intro h
    have he := congrArg (fun z => (g*r)⁻¹*z*g) h
    simp only [mul_inv_rev,inv_mul_cancel_left,mul_assoc] at he
    group at he
    have hf := congrArg (fun z => g*z) he
    simpa [mul_assoc] using hf
  · intro h
    have he : g*s*g⁻¹ = s := by rw [h]; group
    calc
      g*(r*s)*g⁻¹ = (g*r*g⁻¹)*(g*s*g⁻¹) := by group
      _ = g*r*g⁻¹*s := by rw [he]

theorem m2_conjSecond_iff (g : Verify.F) (s : GroupState) :
    conjSecond g (groupStep .m2 s) = groupStep .m2 (conjSecond g s) ↔
    g*s.2 = s.2*g := by
  rcases s with ⟨r,s⟩
  simp only [conjSecond,groupStep,Prod.mk.injEq,and_true,mul_right_inj]
  constructor
  · intro h
    have he := congrArg (fun z => z*g) h
    simpa [mul_assoc] using he.symm
  · intro h
    calc
      s = (s*g)*g⁻¹ := by group
      _ = g*s*g⁻¹ := by rw [h]

theorem m5_conjFirst_iff (g : Verify.F) (s : GroupState) :
    conjFirst g (groupStep .m5 s) = groupStep .m5 (conjFirst g s) ↔
    g*s.1 = s.1*g := by
  rcases s with ⟨r,s⟩
  simp only [conjFirst,groupStep,Prod.mk.injEq,true_and,mul_right_inj]
  constructor
  · intro h
    have he := congrArg (fun z => z⁻¹*g) h
    simpa [mul_assoc] using he.symm
  · intro h
    have he : g*r*g⁻¹ = r := by rw [h]; group
    rw [he]

theorem m5_conjSecond_iff (g : Verify.F) (s : GroupState) :
    conjSecond g (groupStep .m5 s) = groupStep .m5 (conjSecond g s) ↔
    g*s.1 = s.1*g := by
  rcases s with ⟨r,s⟩
  simp only [conjSecond,groupStep,Prod.mk.injEq,true_and]
  constructor
  · intro h
    have he := congrArg (fun z => ((g*s)⁻¹*z)⁻¹) h
    simp only [mul_inv_rev] at he
    group at he
    exact he
  · intro h
    have he : g*r⁻¹*g⁻¹ = r⁻¹ := by
      have hh : g*r*g⁻¹ = r := by rw [h]; group
      simpa [mul_assoc] using congrArg Inv.inv hh
    calc
      g*(s*r⁻¹)*g⁻¹ = (g*s*g⁻¹)*(g*r⁻¹*g⁻¹) := by group
      _ = g*s*g⁻¹*r⁻¹ := by rw [he]

/-- Exact effect of one noncommuting conjugation persists across any same-axis run.
This is a local-state example, not a counterexample to the short successful-family conjecture. -/
theorem one_conjugation_breaks :
    ¬ Compatible .m2 (groupStep .m6 (Verify.x,Verify.y))
      (groupStep .m6 (groupStep .m2 (Verify.x,Verify.y))) := by
  unfold Compatible
  decide +kernel

theorem one_conjugation_breaks_all (k : ℕ) :
    ¬ Compatible .m2
      (groupRun (List.replicate k .m2) (groupStep .m6 (Verify.x,Verify.y)))
      (groupRun (List.replicate k .m2)
        (groupStep .m6 (groupStep .m2 (Verify.x,Verify.y)))) := by
  rw [repeat_axis_iff]
  exact one_conjugation_breaks

end Candidate.CutTransport
