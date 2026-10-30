import Verify.QGroup
import Verify.AtomicSemantics

/-! Exact quotient replay and central-coordinate perturbation transport.
No success-to-skeleton classification or numerical B baseline is assumed. -/

namespace Verify.QDynamics

open QModel
abbrev Move := AtomicSemantics.Move
abbrev QState := Q × Q
abbrev Delta := ℤ × ℤ

def mapState (s : AtomicSemantics.GroupState) : QState := (toQ s.1, toQ s.2)

def qStep : Move → QState → QState
  | .m0, (r,s) => (r⁻¹,s)
  | .m1, (r,s) => (r,s⁻¹)
  | .m2, (r,s) => (r*s,s)
  | .m3, (r,s) => (r*s⁻¹,s)
  | .m4, (r,s) => (r,s*r)
  | .m5, (r,s) => (r,s*r⁻¹)
  | .m6, (r,s) => (qx*r*qx⁻¹,s)
  | .m7, (r,s) => (qx⁻¹*r*qx,s)
  | .m8, (r,s) => (qy*r*qy⁻¹,s)
  | .m9, (r,s) => (qy⁻¹*r*qy,s)
  | .m10, (r,s) => (r,qx*s*qx⁻¹)
  | .m11, (r,s) => (r,qx⁻¹*s*qx)
  | .m12, (r,s) => (r,qy*s*qy⁻¹)
  | .m13, (r,s) => (r,qy⁻¹*s*qy)

def qRun : List Move → QState → QState
  | [],s => s
  | m::ms,s => qRun ms (qStep m s)

theorem mapState_step (m : Move) (s : AtomicSemantics.GroupState) :
    mapState (AtomicSemantics.groupStep m s) = qStep m (mapState s) := by
  rcases s with ⟨r,s⟩
  cases m <;> apply Prod.ext <;>
    simp [mapState, AtomicSemantics.groupStep, qStep, Verify.X, Verify.Y]

theorem mapState_run (ms : List Move) (s : AtomicSemantics.GroupState) :
    mapState (AtomicSemantics.groupRun ms s) = qRun ms (mapState s) := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih =>
    simpa only [AtomicSemantics.groupRun, qRun, mapState_step] using
      ih (AtomicSemantics.groupStep m s)

def shiftQ (d : ℤ) (q : Q) : Q := ⟨q.a,q.b,q.c+d⟩
def shift (d : Delta) (s : QState) : QState := (shiftQ d.1 s.1,shiftQ d.2 s.2)
def third (s : QState) : Delta := (s.1.c,s.2.c)
def difference (s t : QState) : Delta := third s - third t
def SameAB (s t : QState) : Prop :=
  s.1.a=t.1.a ∧ s.1.b=t.1.b ∧ s.2.a=t.2.a ∧ s.2.b=t.2.b

theorem shift_zero (s : QState) : shift 0 s = s := by
  apply Prod.ext <;> apply Q.ext <;> simp [shift,shiftQ]

theorem shift_add (d e : Delta) (s : QState) :
    shift d (shift e s) = shift (d+e) s := by
  apply Prod.ext <;> apply Q.ext <;> simp [shift,shiftQ]
  all_goals ring

theorem third_shift (d : Delta) (s : QState) : third (shift d s) = third s + d := by
  rfl

theorem eq_shift_difference (s t : QState) (h : SameAB s t) :
    s = shift (difference s t) t := by
  rcases h with ⟨ha,hb,hc,hd⟩
  apply Prod.ext <;> apply Q.ext <;>
    simp [shift,shiftQ,difference,third,ha,hb,hc,hd]
  all_goals ring

def linearStep : Move → Delta → Delta
  | .m0,d => (-d.1,d.2)
  | .m1,d => (d.1,-d.2)
  | .m2,d => (d.1+d.2,d.2)
  | .m3,d => (d.1-d.2,d.2)
  | .m4,d => (d.1,d.2+d.1)
  | .m5,d => (d.1,d.2-d.1)
  | _,d => d

def linearRun : List Move → Delta → Delta
  | [],d => d
  | m::ms,d => linearRun ms (linearStep m d)

theorem linearStep_zero (m : Move) : linearStep m 0 = 0 := by
  cases m <;> simp [linearStep]

theorem linearStep_add (m : Move) (d e : Delta) :
    linearStep m (d+e) = linearStep m d + linearStep m e := by
  cases m <;> apply Prod.ext <;> simp [linearStep]
  all_goals ring

theorem linearRun_zero (ms : List Move) : linearRun ms 0 = 0 := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simpa only [linearRun,linearStep_zero] using ih

theorem linearRun_add (ms : List Move) (d e : Delta) :
    linearRun ms (d+e) = linearRun ms d + linearRun ms e := by
  induction ms generalizing d e with
  | nil => rfl
  | cons m ms ih =>
    simpa only [linearRun,linearStep_add] using ih (linearStep m d) (linearStep m e)

theorem qStep_shift (m : Move) (d : Delta) (s : QState) :
    qStep m (shift d s) = shift (linearStep m d) (qStep m s) := by
  rcases s with ⟨r,s⟩
  cases m <;> apply Prod.ext <;> apply Q.ext <;>
    simp [qStep,shift,shiftQ,linearStep,qx,qy]
  all_goals ring

theorem qRun_shift (ms : List Move) (d : Delta) (s : QState) :
    qRun ms (shift d s) = shift (linearRun ms d) (qRun ms s) := by
  induction ms generalizing d s with
  | nil => rfl
  | cons m ms ih =>
    simpa only [qRun,linearRun,qStep_shift] using ih (linearStep m d) (qStep m s)

theorem difference_transport (ms : List Move) (s t : QState) (h : SameAB s t) :
    difference (qRun ms s) (qRun ms t) = linearRun ms (difference s t) := by
  have hr := qRun_shift ms (difference s t) t
  rw [← eq_shift_difference s t h] at hr
  rw [hr]
  simp only [difference,third_shift]
  abel

def Conjugation (m : Move) : Prop := m ∈ [.m6,.m7,.m8,.m9,.m10,.m11,.m12,.m13]

def increment : Move → QState → Delta
  | .m6,s => (s.1.b,0)
  | .m7,s => (-s.1.b,0)
  | .m8,s => (-s.1.a,0)
  | .m9,s => (s.1.a,0)
  | .m10,s => (0,s.2.b)
  | .m11,s => (0,-s.2.b)
  | .m12,s => (0,-s.2.a)
  | .m13,s => (0,s.2.a)
  | _,_ => 0

theorem increment_shift (m : Move) (d : Delta) (s : QState) :
    increment m (shift d s) = increment m s := by
  cases m <;> rfl

theorem linearStep_conjugation (m : Move) (hm : Conjugation m) (d : Delta) :
    linearStep m d = d := by
  cases m <;> simp_all [Conjugation,linearStep]

theorem qStep_conjugation (m : Move) (hm : Conjugation m) (s : QState) :
    qStep m s = shift (increment m s) s := by
  cases m <;> (try {simp [Conjugation] at hm})
  all_goals apply Prod.ext <;> apply Q.ext <;>
    simp [qStep,increment,shift,shiftQ,qx,qy]
  all_goals ring

theorem qStep_conjugation_shift (m : Move) (hm : Conjugation m)
    (d : Delta) (s : QState) :
    qStep m (shift d s) = shift (d+increment m s) s := by
  rw [qStep_shift,linearStep_conjugation m hm,qStep_conjugation m hm,shift_add]

inductive Event where
  | base (move : Move)
  | atom (move : Move)
  deriving DecidableEq

def validEvent : Event → Prop
  | .base _ => True
  | .atom m => Conjugation m

def ValidEvents (events : List Event) : Prop := ∀ e ∈ events, validEvent e

def actualMoves : List Event → List Move
  | [] => []
  | .base m::es => m::actualMoves es
  | .atom m::es => m::actualMoves es

def baseMoves : List Event → List Move
  | [] => []
  | .base m::es => m::baseMoves es
  | .atom _::es => baseMoves es

def accumulatedDelta : List Event → QState → Delta → Delta
  | [],_,d => d
  | .base m::es,s,d => accumulatedDelta es (qStep m s) (linearStep m d)
  | .atom m::es,s,d => accumulatedDelta es s (d+increment m s)

theorem event_run_shift (events : List Event) (hv : ValidEvents events)
    (s : QState) (d : Delta) :
    qRun (actualMoves events) (shift d s) =
      shift (accumulatedDelta events s d) (qRun (baseMoves events) s) := by
  induction events generalizing s d with
  | nil => rfl
  | cons event es ih =>
    have ht : ValidEvents es := by
      intro e he
      exact hv e (by simp [he])
    cases event with
    | base m =>
      simpa only [actualMoves,baseMoves,qRun,accumulatedDelta,qStep_shift] using
        ih ht (qStep m s) (linearStep m d)
    | atom m =>
      have hm : Conjugation m := hv (.atom m) (by simp)
      simpa only [actualMoves,baseMoves,qRun,accumulatedDelta,
        qStep_conjugation_shift m hm] using ih ht s (d+increment m s)

theorem event_run (events : List Event) (hv : ValidEvents events) (s : QState) :
    qRun (actualMoves events) s =
      shift (accumulatedDelta events s 0) (qRun (baseMoves events) s) := by
  simpa only [shift_zero] using event_run_shift events hv s 0

theorem accumulatedDelta_affine (events : List Event) (s : QState) (d e : Delta) :
    accumulatedDelta events s (d+e) =
      linearRun (baseMoves events) d + accumulatedDelta events s e := by
  induction events generalizing s d e with
  | nil => rfl
  | cons event es ih =>
    cases event with
    | base m =>
      simpa only [accumulatedDelta,baseMoves,linearRun,linearStep_add] using
        ih (qStep m s) (linearStep m d) (linearStep m e)
    | atom m =>
      simpa only [accumulatedDelta,baseMoves,add_assoc] using ih s d (e+increment m s)

theorem event_actual_third (events : List Event) (hv : ValidEvents events)
    (s : AtomicSemantics.GroupState) :
    third (mapState (AtomicSemantics.groupRun (actualMoves events) s)) =
      third (mapState (AtomicSemantics.groupRun (baseMoves events) s)) +
        accumulatedDelta events (mapState s) 0 := by
  rw [mapState_run,mapState_run,event_run events hv,third_shift]

theorem success_necessary_delta (events : List Event) (hv : ValidEvents events)
    (s : AtomicSemantics.GroupState)
    (hs : AtomicSemantics.groupRun (actualMoves events) s = (Verify.x,Verify.y)) :
    accumulatedDelta events (mapState s) 0 =
      -third (mapState (AtomicSemantics.groupRun (baseMoves events) s)) := by
  have h := event_actual_third events hv s
  rw [hs] at h
  have hz : third (mapState (Verify.x,Verify.y)) = 0 := by
    simp [third,mapState,qx,qy]
  rw [hz] at h
  exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans h.symm)

/-- Each atom is transported through the remaining baseline, with all
earlier atoms erased only in the quotient perturbation calculation. -/
def contributions : List Event → QState → List Delta
  | [],_ => []
  | .base m::es,s => contributions es (qStep m s)
  | .atom m::es,s =>
      linearRun (baseMoves es) (increment m s) :: contributions es s

theorem accumulatedDelta_sum (events : List Event) (s : QState) :
    accumulatedDelta events s 0 = (contributions events s).sum := by
  induction events generalizing s with
  | nil => rfl
  | cons event es ih =>
    cases event with
    | base m =>
      simpa only [accumulatedDelta,contributions,linearStep_zero] using ih (qStep m s)
    | atom m =>
      simp only [accumulatedDelta,zero_add,contributions,List.sum_cons]
      have h := accumulatedDelta_affine es s (increment m s) 0
      simpa only [add_zero,ih] using h

theorem event_actual_third_sum (events : List Event) (hv : ValidEvents events)
    (s : AtomicSemantics.GroupState) :
    third (mapState (AtomicSemantics.groupRun (actualMoves events) s)) =
      third (mapState (AtomicSemantics.groupRun (baseMoves events) s)) +
        (contributions events (mapState s)).sum := by
  rw [event_actual_third events hv,accumulatedDelta_sum]

theorem success_necessary_sum (events : List Event) (hv : ValidEvents events)
    (s : AtomicSemantics.GroupState)
    (hs : AtomicSemantics.groupRun (actualMoves events) s = (Verify.x,Verify.y)) :
    (contributions events (mapState s)).sum =
      -third (mapState (AtomicSemantics.groupRun (baseMoves events) s)) := by
  rw [← accumulatedDelta_sum]
  exact success_necessary_delta events hv s hs

end Verify.QDynamics

#print axioms Verify.QDynamics.mapState_step
#print axioms Verify.QDynamics.mapState_run
#print axioms Verify.QDynamics.shift_zero
#print axioms Verify.QDynamics.shift_add
#print axioms Verify.QDynamics.third_shift
#print axioms Verify.QDynamics.eq_shift_difference
#print axioms Verify.QDynamics.linearStep_zero
#print axioms Verify.QDynamics.linearStep_add
#print axioms Verify.QDynamics.linearRun_zero
#print axioms Verify.QDynamics.linearRun_add
#print axioms Verify.QDynamics.qStep_shift
#print axioms Verify.QDynamics.qRun_shift
#print axioms Verify.QDynamics.difference_transport
#print axioms Verify.QDynamics.increment_shift
#print axioms Verify.QDynamics.linearStep_conjugation
#print axioms Verify.QDynamics.qStep_conjugation
#print axioms Verify.QDynamics.qStep_conjugation_shift
#print axioms Verify.QDynamics.event_run_shift
#print axioms Verify.QDynamics.event_run
#print axioms Verify.QDynamics.accumulatedDelta_affine
#print axioms Verify.QDynamics.event_actual_third
#print axioms Verify.QDynamics.success_necessary_delta
#print axioms Verify.QDynamics.accumulatedDelta_sum
#print axioms Verify.QDynamics.event_actual_third_sum
#print axioms Verify.QDynamics.success_necessary_sum
