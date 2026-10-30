import CompatibleSelection

namespace Candidate.ShortBudget
open Verify.AtomicSemantics Candidate.ShortWordDelete Candidate.ShortWordRecovery
open Candidate.CompatibleSelection

def isConjugation : Move → Bool
  | .m0 | .m1 | .m2 | .m3 | .m4 | .m5 => false
  | _ => true

def conjugationCount (ms : List Move) : ℕ := (ms.filter isConjugation).length

theorem noFlip_length_split {ms : List Move}
    (hn : Candidate.ShortWordSuccessBridge.NoFlip ms) :
    (ms.filterMap nielsenAtom).length + conjugationCount ms = ms.length := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    have hm := hn m (by simp)
    have ht : Candidate.ShortWordSuccessBridge.NoFlip ms := by
      intro k hk
      exact hn k (by simp [hk])
    have hi := ih ht
    cases m <;> simp_all [List.filterMap_cons,List.filter_cons,nielsenAtom,conjugationCount,isConjugation] <;> omega

theorem budget_nplus5 {ms : List Move} {n : ℕ}
    (hn : Candidate.ShortWordSuccessBridge.NoFlip ms)
    (hl : ms.length ≤ n+7) (hq : (ms.filterMap nielsenAtom).length = n+5) :
    conjugationCount ms ≤ 2 := by
  have := noFlip_length_split hn
  omega

theorem budget_nplus3 {ms : List Move} {n : ℕ}
    (hn : Candidate.ShortWordSuccessBridge.NoFlip ms)
    (hl : ms.length ≤ n+7) (hq : (ms.filterMap nielsenAtom).length = n+3) :
    conjugationCount ms ≤ 4 := by
  have := noFlip_length_split hn
  omega

/-- CONDITIONAL: the global bad-owner bound is an explicit unproved input.
The shortness and conjugation budget alone are not claimed to establish it. -/
theorem conditional_clean_cut {ms : List Move} {n : ℕ}
    {rs : List Rule} {history : List Leaf} {finish : List Token}
    (hn : Candidate.ShortWordSuccessBridge.NoFlip ms) (hn8 : 8 ≤ n)
    (hl : ms.length ≤ n+7)
    (ht : Trace (expandChronological (numberFrom 0 (ms.filterMap nielsenAtom))) rs history finish)
    (he : values finish = terminal n)
    (hq : (ms.filterMap nielsenAtom).length = n+5 ∨ (ms.filterMap nielsenAtom).length = n+3)
    (bad : Finset ℕ)
    (hcover : ∀ e < (ms.filterMap nielsenAtom).length,
      clean e history = true → e ∉ bad → CutAt ms n e)
    (hbad : bad.card ≤ conjugationCount ms) :
    ∃ e, e < (ms.filterMap nielsenAtom).length ∧ clean e history = true ∧ CutAt ms n e := by
  rcases hq with hq | hq
  · have hb := budget_nplus5 hn hl hq
    exact exists_clean_cut_nplus5 ht he hq bad hcover (by omega)
  · have hb := budget_nplus3 hn hl hq
    exact exists_clean_cut_nplus3 ht he hq bad hcover (by omega)

theorem conditional_short_descent {ms : List Move} {n : ℕ}
    {rs : List Rule} {history : List Leaf} {finish : List Token}
    (hn : Candidate.ShortWordSuccessBridge.NoFlip ms) (hn8 : 8 ≤ n)
    (hl : ms.length ≤ n+7)
    (hs : groupRun ms (Verify.ROperationConnection.initial n) = (Verify.x,Verify.y))
    (ht : Trace (expandChronological (numberFrom 0 (ms.filterMap nielsenAtom))) rs history finish)
    (he : values finish = terminal n)
    (hq : (ms.filterMap nielsenAtom).length = n+5 ∨ (ms.filterMap nielsenAtom).length = n+3)
    (bad : Finset ℕ)
    (hcover : ∀ e < (ms.filterMap nielsenAtom).length,
      clean e history = true → e ∉ bad → CutAt ms n e)
    (hbad : bad.card ≤ conjugationCount ms) :
    ∃ e p m s, ms = p ++ m :: s ∧ (p.filterMap nielsenAtom).length = e ∧
      clean e history = true ∧ (m = .m2 ∨ m = .m5) ∧
      Candidate.ShortWordSuccessBridge.NoFlip (p ++ s) ∧
      groupRun (p ++ s) (Verify.ROperationConnection.initial (n-1)) = (Verify.x,Verify.y) ∧
      (p ++ s).length ≤ (n-1)+7 ∧ 7 ≤ n-1 := by
  have hc := conditional_clean_cut hn hn8 hl ht he hq bad hcover hbad
  obtain ⟨e,p,m,s,hms,hi,hclean,hm,hgood,hlen⟩ := clean_cut_raw_success hs hc
  refine ⟨e,p,m,s,hms,hi,hclean,hm,?_,hgood,?_,by omega⟩
  · intro k hk
    apply hn k
    rw [hms]
    simp only [List.mem_append,List.mem_cons] at hk ⊢
    rcases hk with hk | hk
    · exact Or.inl hk
    · exact Or.inr (Or.inr hk)
  · omega

/-- This abstracts the remaining descent obligation. No base result is imported. -/
theorem no_success_of_descent (Success : ℕ → Prop)
    (base : ¬ Success 7)
    (descend : ∀ n, 8 ≤ n → Success n → Success (n-1)) :
    ∀ n, 7 ≤ n → ¬ Success n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hs
    by_cases he : n=7
    · exact base (he ▸ hs)
    · have hn8 : 8 ≤ n := by omega
      exact ih (n-1) (by omega) (by omega) (descend n hn8 hs)

end Candidate.ShortBudget
