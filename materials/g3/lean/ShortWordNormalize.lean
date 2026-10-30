import ShortWordNormalForm

namespace Candidate.ShortWordNormalize
open Candidate.ShortWordDelete Candidate.ShortWordRecovery
open Candidate.ShortWordMatrix Candidate.ShortWordNormalForm

def Supported (w : List Token) : Prop := ∀ a ∈ w, a.support ≠ []

def NoRedex (w : List Token) : Prop :=
  ∀ (p s : List Token) (a b : Token) (r : Rule),
    w = p ++ [a,b] ++ s → ¬ Legal r a b

theorem supported_tail {a : Token} {w : List Token} (h : Supported (a :: w)) :
    Supported w := by
  intro b hb
  exact h b (List.mem_cons_of_mem _ hb)

theorem noRedex_tail {a : Token} {w : List Token} (h : NoRedex (a :: w)) :
    NoRedex w := by
  intro p s b c r he
  exact h (a :: p) s b c r (by simp [he])

theorem noRedex_alternating (w : List Token) (hs : Supported w) (hn : NoRedex w) :
    Alternating (values w) := by
  induction w with
  | nil => trivial
  | cons a w ih =>
    cases w with
    | nil => trivial
    | cons b rest =>
      have ha := hs a (by simp)
      have hb := hs b (by simp)
      refine ⟨?_, ih (supported_tail hs) (noRedex_tail hn)⟩
      intro hf
      cases hva : a.value <;> cases hvb : b.value <;>
        simp [hva,hvb,family] at hf
      · exact (hn [] rest a b .t rfl) ⟨ha,hb,hva,hvb⟩
      · exact (hn [] rest a b .v rfl) ⟨ha,hb,hva,hvb⟩
      · exact (hn [] rest a b .z rfl) ⟨ha,hb,Or.inl ⟨hva,hvb⟩⟩
      · exact (hn [] rest a b .z rfl) ⟨ha,hb,Or.inr ⟨hva,hvb⟩⟩
      · exact (hn [] rest a b .u rfl) ⟨ha,hb,hva,hvb⟩

theorem supported_rewrite {p s : List Token} {a b : Token} {r : Rule}
    (hs : Supported (p ++ [a,b] ++ s)) : Supported (p ++ output r a b ++ s) := by
  intro t ht
  have ha := hs a (by simp)
  have hb := hs b (by simp)
  simp only [List.mem_append] at ht
  rcases ht with (hp | ho) | ht
  · exact hs t (by simp [hp])
  · cases r <;> simp [output] at ho
    all_goals subst t; simp_all
  · exact hs t (by simp [ht])

theorem rewrite_shorter (p s : List Token) (a b : Token) (r : Rule) :
    (p ++ output r a b ++ s).length < (p ++ [a,b] ++ s).length := by
  cases r <;> simp [output]

theorem exists_normalizing_trace (w : List Token) (hs : Supported w) :
    ∃ rs h f, ShortWordDelete.Trace w rs h f ∧ Alternating (values f) := by
  classical
  by_cases hn : NoRedex w
  · exact ⟨[],[],w,ShortWordDelete.Trace.nil w,noRedex_alternating w hs hn⟩
  · simp only [NoRedex, not_forall, not_not] at hn
    obtain ⟨p,s,a,b,r,he,hl⟩ := hn
    have hsmall : (p ++ output r a b ++ s).length < w.length := by
      rw [he]; exact rewrite_shorter p s a b r
    obtain ⟨rs,h,f,ht,hf⟩ := exists_normalizing_trace (p ++ output r a b ++ s)
      (supported_rewrite (he ▸ hs))
    exact ⟨r :: rs,a.support ++ b.support ++ h,f,
      he.symm ▸ ShortWordDelete.Trace.step p s a b r hl ht,hf⟩
termination_by w.length
decreasing_by simpa only [List.length_append] using hsmall

theorem expand_supported (atoms : List (ℕ × Atom)) :
    Supported (expandChronological atoms) := by
  intro t ht
  simp only [expandChronological, List.mem_flatMap] at ht
  obtain ⟨⟨k,kind⟩,_,ht⟩ := ht
  cases kind <;> simp [expandAtom,leafToken] at ht <;>
    rcases ht with rfl | rfl <;> simp

theorem exists_terminal_trace {atoms : List Atom} {n : ℕ}
    (he : SignedEq (tokenEval (expandChronological (numberFrom 0 atoms))) (H n)) :
    ∃ rs h f, ShortWordDelete.Trace (expandChronological (numberFrom 0 atoms)) rs h f ∧
      values f = terminal n := by
  obtain ⟨rs,h,f,ht,ha⟩ := exists_normalizing_trace _ (expand_supported _)
  exact ⟨rs,h,f,ht,alternating_terminal_unique ha ((trace_signed ht).symm.trans he)⟩

end Candidate.ShortWordNormalize
