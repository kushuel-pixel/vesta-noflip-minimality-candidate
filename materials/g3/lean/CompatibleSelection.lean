import CutTransport

namespace Candidate.CompatibleSelection
open Verify.AtomicSemantics Candidate.RawDeletionCriterion Candidate.CutTransport
open Candidate.ShortWordDelete Candidate.ShortWordRecovery Candidate.ShortWordTerminalDelete
open Candidate.ShortWordMarkBound Candidate.ShortWordSelection

/-- Owner is the chronological Nielsen index, not the raw move index. -/
def CutAt (ms : List Move) (n e : ℕ) : Prop :=
  ∃ p m s, ms = p ++ m :: s ∧ (p.filterMap nielsenAtom).length = e ∧
    (m = .m2 ∨ m = .m5) ∧
    Compatible m (groupRun p (Verify.ROperationConnection.initial n))
      (groupRun p (Verify.ROperationConnection.initial (n-1)))

theorem cutAt_success {ms : List Move} {n e : ℕ} (hc : CutAt ms n e)
    (hs : groupRun ms (Verify.ROperationConnection.initial n) = (Verify.x,Verify.y)) :
    ∃ p m s, ms = p ++ m :: s ∧ (p.filterMap nielsenAtom).length = e ∧
      (m = .m2 ∨ m = .m5) ∧
      groupRun (p ++ s) (Verify.ROperationConnection.initial (n-1)) = (Verify.x,Verify.y) ∧
      (p ++ s).length + 1 = ms.length := by
  obtain ⟨p,m,s,he,hi,hm,hc⟩ := hc
  refine ⟨p,m,s,he,hi,hm,?_,?_⟩
  · apply (family_deletion_success_iff p s m n (by simpa [he] using hs)).mpr
    exact hc
  · simp [he,List.length_append,Nat.add_assoc]

/-- The missing global input is an upper bound on the number of incompatible owners.
This theorem does not derive that bound from the conjugation budget. -/
theorem exists_clean_cut_of_bad_bound {ms : List Move} {n : ℕ}
    {history : List Leaf} (bad : Finset ℕ)
    (hcover : ∀ e < (ms.filterMap nielsenAtom).length, clean e history = true → e ∉ bad → CutAt ms n e)
    (hcount : (allMarks history).card + bad.card < (ms.filterMap nielsenAtom).length) :
    ∃ e, e < (ms.filterMap nielsenAtom).length ∧ clean e history = true ∧ CutAt ms n e := by
  have hu : (allMarks history ∪ bad).card < (ms.filterMap nielsenAtom).length :=
    lt_of_le_of_lt (Finset.card_union_le _ _) hcount
  obtain ⟨e,he,hm⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := allMarks history ∪ bad) (t := Finset.range (ms.filterMap nielsenAtom).length)
    (by simpa using hu)
  have hei := Finset.mem_range.mp he
  have hn : e ∉ allMarks history ∧ e ∉ bad := by simpa using hm
  exact ⟨e,hei,(clean_iff_not_marked e history).mpr hn.1,hcover e hei ((clean_iff_not_marked e history).mpr hn.1) hn.2⟩

theorem exists_clean_cut_nplus5 {ms : List Move} {n : ℕ}
    {rs : List Rule} {history : List Leaf} {finish : List Token}
    (ht : Trace (expandChronological (numberFrom 0 (ms.filterMap nielsenAtom))) rs history finish)
    (he : values finish = terminal n) (hq : (ms.filterMap nielsenAtom).length = n+5)
    (bad : Finset ℕ)
    (hcover : ∀ e < (ms.filterMap nielsenAtom).length, clean e history = true → e ∉ bad → CutAt ms n e)
    (hb : bad.card + 5 < n) :
    ∃ e, e < (ms.filterMap nielsenAtom).length ∧ clean e history = true ∧ CutAt ms n e := by
  apply exists_clean_cut_of_bad_bound bad hcover
  have hm := marks_le_ten ht he hq
  omega

theorem exists_clean_cut_nplus3 {ms : List Move} {n : ℕ}
    {rs : List Rule} {history : List Leaf} {finish : List Token}
    (ht : Trace (expandChronological (numberFrom 0 (ms.filterMap nielsenAtom))) rs history finish)
    (he : values finish = terminal n) (hq : (ms.filterMap nielsenAtom).length = n+3)
    (bad : Finset ℕ)
    (hcover : ∀ e < (ms.filterMap nielsenAtom).length, clean e history = true → e ∉ bad → CutAt ms n e)
    (hb : bad.card + 3 < n) :
    ∃ e, e < (ms.filterMap nielsenAtom).length ∧ clean e history = true ∧ CutAt ms n e := by
  apply exists_clean_cut_of_bad_bound bad hcover
  have hm := marks_le_six ht he hq
  omega

theorem clean_cut_raw_success {ms : List Move} {n : ℕ} {history : List Leaf}
    (hs : groupRun ms (Verify.ROperationConnection.initial n) = (Verify.x,Verify.y))
    (hc : ∃ e, e < (ms.filterMap nielsenAtom).length ∧ clean e history = true ∧ CutAt ms n e) :
    ∃ e p m s, ms = p ++ m :: s ∧ (p.filterMap nielsenAtom).length = e ∧
      clean e history = true ∧ (m = .m2 ∨ m = .m5) ∧
      groupRun (p ++ s) (Verify.ROperationConnection.initial (n-1)) = (Verify.x,Verify.y) ∧
      (p ++ s).length + 1 = ms.length := by
  obtain ⟨e,_,hclean,hcut⟩ := hc
  obtain ⟨p,m,s,he,hi,hm,hgood,hlen⟩ := cutAt_success hcut hs
  exact ⟨e,p,m,s,he,hi,hclean,hm,hgood,hlen⟩

end Candidate.CompatibleSelection
