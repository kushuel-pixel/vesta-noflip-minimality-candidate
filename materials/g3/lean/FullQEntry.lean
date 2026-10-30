import NegativeNielsenCount
import ShortBudget
import Verify.QDynamics

/-! F-0 and F-T1 for the fixed original fourteen-move semantics.
No finite classification, global minimality, or static acceptance is assumed. -/
namespace Candidate.FullQEntry
open Candidate.ShortWordDelete Candidate.ShortWordRecovery Candidate.ShortWordMatrix
open Candidate.ShortWordCounts Candidate.ShortWordSuccessBridge
open Candidate.NegativeNielsenCount Candidate.ShortBudget
open Verify.QModel Verify.QDynamics

def PureMove (m : Verify.AtomicSemantics.Move) : Prop :=
  m = .m2 ∨ m = .m3 ∨ m = .m4 ∨ m = .m5

def qDet (s : QState) : ℤ := s.1.a * s.2.b - s.1.b * s.2.a

def qW (s : QState) : Delta :=
  (2*s.1.c + s.1.a*s.1.b - 1, 2*s.2.c + s.2.a*s.2.b + 1)

theorem pure_of_noFlip_c0 {ms : List Verify.AtomicSemantics.Move}
    (hn : NoFlip ms) (hc : conjugationCount ms = 0) :
    ∀ m ∈ ms, PureMove m := by
  intro m hm
  have hf : ms.filter isConjugation = [] := List.length_eq_zero_iff.mp hc
  have hm' := hn m hm
  have hnconj : isConjugation m = false := by
    by_contra h
    have htrue : isConjugation m = true := by cases hval : isConjugation m <;> simp_all
    have : m ∈ ms.filter isConjugation := List.mem_filter.mpr ⟨hm,htrue⟩
    rw [hf] at this
    exact List.not_mem_nil this
  cases m <;> simp_all [PureMove,isConjugation]

theorem qDet_step (m : Verify.AtomicSemantics.Move) (s : QState)
    (hm : PureMove m) : qDet (qStep m s) = qDet s := by
  rcases hm with rfl | rfl | rfl | rfl <;>
    simp [qDet,qStep] <;> ring

/-- General-variable covariance for all four original Nielsen moves. -/
theorem qW_step (m : Verify.AtomicSemantics.Move) (s : QState)
    (hm : PureMove m) (hd : qDet s = 1) :
    qW (qStep m s) = linearStep m (qW s) := by
  rcases hm with rfl | rfl | rfl | rfl <;>
    apply Prod.ext <;> simp [qW,qStep,linearStep,qDet] at * <;> nlinarith

def WRelation (s : QState) (C D : ℤ) : Prop :=
  (qW s).1 = s.1.a*C+s.1.b*D ∧
  (qW s).2 = s.2.a*C+s.2.b*D

theorem relation_step (m : Verify.AtomicSemantics.Move) (s : QState)
    (C D : ℤ) (hm : PureMove m) (hd : qDet s = 1)
    (hw : WRelation s C D) : WRelation (qStep m s) C D := by
  have he := qW_step m s hm hd
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  rcases hm with rfl | rfl | rfl | rfl <;>
    simp only [WRelation] at hw ⊢ <;>
    simp [linearStep,qStep] at h1 h2 ⊢ <;>
    constructor <;> nlinarith [hw.1,hw.2]

theorem relation_run (ms : List Verify.AtomicSemantics.Move) (s : QState)
    (C D : ℤ) (hp : ∀ m ∈ ms, PureMove m)
    (hd : qDet s = 1) (hw : WRelation s C D) :
    qDet (qRun ms s) = 1 ∧ WRelation (qRun ms s) C D := by
  induction ms generalizing s with
  | nil => exact ⟨hd,hw⟩
  | cons m ms ih =>
    have hm := hp m (by simp)
    exact ih (qStep m s) (by intro k hk; exact hp k (by simp [hk]))
      ((qDet_step m s hm).trans hd) (relation_step m s C D hm hd hw)

theorem initial_relation (n : ℕ) :
    qDet (mapState (Verify.ROperationConnection.initial n)) = 1 ∧
    WRelation (mapState (Verify.ROperationConnection.initial n))
      (2*(n:ℤ)^2+1) (2*(n:ℤ)+1) := by
  constructor
  · simp [mapState,Verify.ROperationConnection.initial,toQ_uFamily,toQ_vFamily,qDet]
  · constructor <;>
      simp [mapState,Verify.ROperationConnection.initial,toQ_uFamily,toQ_vFamily,
        WRelation,qW] <;> ring

/-- F-0's terminal coefficient identity, with arbitrary central coordinates. -/
theorem pure_terminal_centers (ms : List Verify.AtomicSemantics.Move) (n : ℕ)
    (hn : NoFlip ms) (hc : conjugationCount ms = 0)
    (c f : ℤ)
    (he : qRun ms (mapState (Verify.ROperationConnection.initial n)) =
      (Q.mk 1 0 c, Q.mk 0 1 f)) :
    c = (n:ℤ)^2+1 ∧ f = (n:ℤ) := by
  have hi := initial_relation n
  have hr := relation_run ms (mapState (Verify.ROperationConnection.initial n))
    (2*(n:ℤ)^2+1) (2*(n:ℤ)+1) (pure_of_noFlip_c0 hn hc) hi.1 hi.2
  rw [he] at hr
  simp [WRelation,qW] at hr
  constructor <;> nlinarith [hr.2.1,hr.2.2]

/-- F-0: every n, no length bound, original strict ordered target. -/
theorem noFlip_c0_nonarrival (ms : List Verify.AtomicSemantics.Move) (n : ℕ)
    (hn : NoFlip ms) (hc : conjugationCount ms = 0) :
    Verify.AtomicSemantics.groupRun ms (Verify.ROperationConnection.initial n) ≠
      (Verify.x,Verify.y) := by
  intro hs
  have he := congrArg mapState hs
  rw [mapState_run] at he
  have hq : qRun ms (mapState (Verify.ROperationConnection.initial n)) =
      (Q.mk 1 0 0, Q.mk 0 1 0) := by simpa [mapState,qx,qy] using he
  have hh := pure_terminal_centers ms n hn hc 0 0 hq
  nlinarith [sq_nonneg (n:ℤ)]

theorem success_q_balance (ms : List Verify.AtomicSemantics.Move) (n : ℕ)
    (hn : NoFlip ms)
    (hs : Verify.AtomicSemantics.groupRun ms (Verify.ROperationConnection.initial n) =
      (Verify.x,Verify.y)) :
    ∃ t : ℕ, (ms.filterMap nielsenAtom).length = n+1+2*t := by
  obtain ⟨rs,h,f,ht,he⟩ := group_success_trace_terminal hn hs
  have hb := trace_balance ht
  have hi := initial_counts (numberFrom 0 (ms.filterMap nielsenAtom))
  have hf := terminal_counts he
  simp only [numberFrom_length] at hi
  exact ⟨rs.count .t,by omega⟩

theorem matrix_q1_impossible (atoms : List Atom) (n : ℕ)
    (hq : atoms.length = n+1) : atomRun atoms ≠ -H n := by
  intro hend
  have hs : SignedEq (tokenEval (expandChronological (numberFrom 0 atoms))) (H n) :=
    (numbered_expansion_signed atoms 0).trans (by rw [hend]; exact Or.inr rfl)
  obtain ⟨rs,h,f,ht,he⟩ := Candidate.ShortWordNormalize.exists_terminal_trace hs
  have hb := numbered_balance ht he hq
  have hc := negative_trace_balance ht he hq
  have ht0 : rs.count .t = 0 := by omega
  have hk2 : negativeCount atoms = 2 := by omega
  have hsign := trace_exact_sign ht
  have hterm : tokenEval f = H n := by rw [tokenEval,he,eval_terminal]
  rw [expansion_exact_sign,hk2,hend,ht0,hterm] at hsign
  have hx := congrArg (fun m : Mat => m 0 1) hsign
  norm_num [twist,H] at hx

/-- F-T1: the requested unconditional all-q entrance theorem. -/
theorem short_success_q3_or_q5
    (ms : List Verify.AtomicSemantics.Move) (n : ℕ)
    (hno : NoFlip ms) (hlen : ms.length ≤ n+7)
    (hs : Verify.AtomicSemantics.groupRun ms (Verify.ROperationConnection.initial n) =
      (Verify.x,Verify.y)) :
    (ms.filterMap nielsenAtom).length = n+3 ∨
    (ms.filterMap nielsenAtom).length = n+5 := by
  obtain ⟨t,ht⟩ := success_q_balance ms n hno hs
  have hl := noFlip_length_split hno
  have hq1 : (ms.filterMap nielsenAtom).length ≠ n+1 := by
    intro hq
    apply matrix_q1_impossible (ms.filterMap nielsenAtom) n hq
    rw [← noFlip_run_extraction ms hno,success_matrix hs]
  have hc : conjugationCount ms ≠ 0 := by
    intro hc
    exact noFlip_c0_nonarrival ms n hno hc hs
  omega

end Candidate.FullQEntry
