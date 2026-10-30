import ShortBudget

namespace Candidate.FiniteCut
open Verify.AtomicSemantics Candidate.CompatibleSelection Candidate.CutTransport
open Candidate.ShortWordDelete

/-- Finite, decidable presentation of the existing state-matching cut predicate. -/
def Test (ms : List Move) (n e : ℕ) : Prop :=
  ∃ i : Fin ms.length,
    ((ms.take i.val).filterMap nielsenAtom).length = e ∧
    (ms[i.val] = .m2 ∨ ms[i.val] = .m5) ∧
    groupRun (ms.take i.val) (Verify.ROperationConnection.initial (n-1)) =
      groupStep ms[i.val] (groupRun (ms.take i.val) (Verify.ROperationConnection.initial n))

instance (ms : List Move) (n e : ℕ) : Decidable (Test ms n e) := by
  unfold Test
  infer_instance

theorem test_iff_cutAt (ms : List Move) (n e : ℕ) : Test ms n e ↔ CutAt ms n e := by
  constructor
  · rintro ⟨i,hi,hm,hc⟩
    refine ⟨ms.take i.val, ms[i.val], ms.drop (i.val+1), ?_, hi, hm, hc⟩
    rw [List.getElem_cons_drop, List.take_append_drop]
  · rintro ⟨p,m,s,he,hi,hm,hc⟩
    subst ms
    have hlen : p.length < (p ++ m :: s).length := by simp
    refine ⟨⟨p.length,hlen⟩, ?_, ?_, ?_⟩
    · simpa using hi
    · simpa using hm
    · simpa [Compatible] using hc

def bad (ms : List Move) (n : ℕ) (history : List Leaf) : Finset ℕ :=
  (Finset.range (ms.filterMap nielsenAtom).length).filter
    (fun e => clean e history = true ∧ ¬ Test ms n e)

theorem mem_bad (ms : List Move) (n e : ℕ) (history : List Leaf) :
    e ∈ bad ms n history ↔
      e < (ms.filterMap nielsenAtom).length ∧ clean e history = true ∧ ¬ CutAt ms n e := by
  simp [bad, test_iff_cutAt]

end Candidate.FiniteCut
