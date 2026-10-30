import BadCleanCounterexample

namespace Candidate.BoundScope
open Verify.AtomicSemantics Candidate.ShortWordDelete Candidate.ShortWordRecovery
open Candidate.ShortBudget Candidate.FiniteCut
open Candidate.BadCleanCounterexample

/-- False if asserted for all successful sequences and every terminal Trace,
without the shortness and Nielsen-excess restrictions. -/
theorem not_unrestricted_trace_bound : ¬ (∀ (ms : List Move) (n : ℕ)
    (rs : List Rule) (history : List Leaf) (finish : List Token),
    Candidate.ShortWordSuccessBridge.NoFlip ms →
    groupRun ms (Verify.ROperationConnection.initial n) = (Verify.x,Verify.y) →
    Trace (expandChronological (numberFrom 0 (ms.filterMap nielsenAtom))) rs history finish →
    values finish = terminal n → (bad ms n history).card ≤ conjugationCount ms) := by
  intro h
  have hle := h original 6 rightRules rightHistory rightFinish original_noFlip
    original_group_success right_trace right_terminal
  exact (Nat.not_le_of_gt Candidate.BadCleanCounterexample.right_bad_exceeds_conjugations) hle

/-- Conditional reduction only. A good terminal Trace is supplied as an explicit
input, not derived from success or the short budget in this theorem. -/
theorem short_descent_of_exists_good_trace {ms : List Move} {n : ℕ}
    (hn : Candidate.ShortWordSuccessBridge.NoFlip ms) (hn8 : 8 ≤ n)
    (hl : ms.length ≤ n+7)
    (hs : groupRun ms (Verify.ROperationConnection.initial n) = (Verify.x,Verify.y))
    (hq : (ms.filterMap nielsenAtom).length = n+5 ∨ (ms.filterMap nielsenAtom).length = n+3)
    (hgood : ∃ rs history finish,
      Trace (expandChronological (numberFrom 0 (ms.filterMap nielsenAtom))) rs history finish ∧
      values finish = terminal n ∧ (bad ms n history).card ≤ conjugationCount ms) :
    ∃ e p m s, ms = p ++ m :: s ∧ (p.filterMap nielsenAtom).length = e ∧
      (m = .m2 ∨ m = .m5) ∧ Candidate.ShortWordSuccessBridge.NoFlip (p ++ s) ∧
      groupRun (p ++ s) (Verify.ROperationConnection.initial (n-1)) = (Verify.x,Verify.y) ∧
      (p ++ s).length ≤ (n-1)+7 ∧ 7 ≤ n-1 := by
  obtain ⟨rs,history,finish,ht,he,hb⟩ := hgood
  have hcover : ∀ e < (ms.filterMap nielsenAtom).length, clean e history = true →
      e ∉ bad ms n history → Candidate.CompatibleSelection.CutAt ms n e := by
    intro e hei hc hnot
    by_contra hfail
    exact hnot ((mem_bad ms n e history).mpr ⟨hei,hc,hfail⟩)
  obtain ⟨e,p,m,s,hms,hi,_,hm,hno,hsuc,hlen,hbase⟩ :=
    conditional_short_descent hn hn8 hl hs ht he hq (bad ms n history) hcover hb
  exact ⟨e,p,m,s,hms,hi,hm,hno,hsuc,hlen,hbase⟩

end Candidate.BoundScope
