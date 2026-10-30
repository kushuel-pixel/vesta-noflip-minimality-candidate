import ShortWordMarkAccounting
import ShortWordSelection
namespace Candidate.ShortWordLineage
open Candidate.ShortWordDelete Candidate.ShortWordRecovery Candidate.ShortWordTerminalDelete
open Candidate.ShortWordSelection Candidate.ShortWordCounts Candidate.ShortWordMarkAccounting

@[simp] theorem leaves_append (xs ys : List Token) : leaves (xs ++ ys) = leaves xs ++ leaves ys := by
  simp [leaves]

theorem initial_leaf_owner (k : ℕ) (atoms : List Atom) (l : Leaf)
    (hl : l ∈ leaves (expandChronological (numberFrom k atoms))) :
    k ≤ l.owner ∧ l.owner < k + atoms.length := by
  obtain ⟨t, ht, hl⟩ := List.mem_flatMap.mp hl
  obtain ⟨item, hi, ht⟩ := List.mem_flatMap.mp ht
  have hb := numberFrom_owner_bounds k atoms item (List.mem_reverse.mp hi)
  rcases item with ⟨e,kind⟩
  cases kind <;> simp [expandAtom, leafToken] at ht <;>
    rcases ht with rfl | rfl <;> simp only [List.mem_singleton] at hl <;>
    subst l <;> exact hb

theorem initial_nodup (k : ℕ) (atoms : List Atom) :
    (leaves (expandChronological (numberFrom k atoms))).Nodup := by
  induction atoms generalizing k with
  | nil => simp [numberFrom, expandChronological, leaves]
  | cons kind atoms ih =>
    have he : expandChronological (numberFrom k (kind :: atoms)) =
        expandChronological (numberFrom (k+1) atoms) ++ expandAtom k kind := by
      simp [numberFrom, expandChronological]
    rw [he, leaves_append, List.nodup_append]
    refine ⟨ih _, ?_, ?_⟩
    · cases kind <;> simp [leaves, expandAtom, leafToken]
    · intro l hl m hm
      have hb := (initial_leaf_owner (k+1) atoms l hl).1
      have hm' : m.owner = k := by
        cases kind <;> simp [leaves, expandAtom, leafToken] at hm <;>
          rcases hm with rfl | rfl <;> rfl
      intro eq
      subst m
      omega

def SigmaSingleton (w : List Token) : Prop :=
  ∀ t ∈ w, t.value = .sigma → ∃ e, t = leafToken e .sigma .sigma

theorem initial_sigma_singleton (atoms : List (ℕ × Atom)) :
    SigmaSingleton (expandChronological atoms) := by
  intro t ht hv
  obtain ⟨item, _, ht⟩ := List.mem_flatMap.mp ht
  rcases item with ⟨e,kind⟩
  cases kind <;> simp [expandAtom, leafToken] at ht <;> rcases ht with rfl | rfl
  all_goals first | exact ⟨e, rfl⟩ | cases hv

theorem sigma_singleton_step {p s : List Token} {a b : Token} (r : Rule)
    (h : SigmaSingleton (p ++ [a,b] ++ s)) : SigmaSingleton (p ++ output r a b ++ s) := by
  intro t ht hv
  simp only [List.mem_append] at ht
  rcases ht with (hp | ho) | hs
  · exact h t (by simp [hp]) hv
  · cases r <;> simp only [output, List.mem_singleton, List.not_mem_nil] at ho
    all_goals subst t; cases hv
  · exact h t (by simp [hs]) hv

theorem Trace.sigma_singleton {start finish : List Token} {rules : List Rule} {history : List Leaf}
    (ht : ShortWordDelete.Trace start rules history finish) (hs : SigmaSingleton start) :
    SigmaSingleton finish := by
  induction ht with
  | nil => exact hs
  | step p s a b r hl tail ih => exact ih (sigma_singleton_step r hs)

theorem typed_step {p s : List Token} {a b : Token} {r : Rule}
    (hl : Legal r a b) (hw : TypedState (p ++ [a,b] ++ s)) :
    TypedState (p ++ output r a b ++ s) := by
  intro t ht
  simp only [List.mem_append] at ht
  rcases ht with (hp | ho) | hs
  · exact hw t (by simp [hp])
  · exact typed_output r a b hl (hw a (by simp)) (hw b (by simp)) t ho
  · exact hw t (by simp [hs])

theorem sigma_input_absent_output {p s : List Token} {a b : Token} {r : Rule}
    (hl : Legal r a b) (hw : TypedState (p ++ [a,b] ++ s))
    (hd : (leaves (p ++ [a,b] ++ s)).Nodup)
    (l : Leaf) (htag : l.tag = .sigma) (hin : l ∈ a.support ++ b.support) :
    l ∉ leaves (p ++ output r a b ++ s) := by
  have hab : leaves (p ++ [a,b] ++ s) = leaves p ++ (a.support ++ b.support) ++ leaves s := by
    simp [leaves, List.append_assoc]
  rw [hab] at hd
  have hnp : l ∉ leaves p := by
    intro hp
    have hd' := (List.nodup_append.mp (List.nodup_append.mp hd).1).2.2
    exact hd' l hp l hin rfl
  have hns : l ∉ leaves s := by
    intro hs
    have hd' := (List.nodup_append.mp hd).2.2
    exact hd' l (List.mem_append_right _ hin) l hs rfl
  have ho : l ∉ leaves (output r a b) := by
    have ha := hw a (by simp)
    have hb := hw b (by simp)
    cases r <;> simp only [output, leaves, List.flatMap_nil, List.not_mem_nil,
      not_false_eq_true, List.flatMap_cons, List.append_nil]
    all_goals
      intro hm
      obtain ⟨_, _, hva, hvb⟩ := hl
      rcases List.mem_append.mp hm with hm | hm
      · have h := ha.2 l hm; simp [hva, factorTag, htag] at h
      · have h := hb.2 l hm; simp [hvb, factorTag, htag] at h
  simpa only [leaves_append, List.mem_append, not_or] using And.intro (And.intro hnp ho) hns

theorem Trace.live_sigma_not_history {start finish : List Token} {rules : List Rule} {history : List Leaf}
    (ht : ShortWordDelete.Trace start rules history finish) (hw : TypedState start)
    (hd : (leaves start).Nodup) (l : Leaf) (htag : l.tag = .sigma)
    (hf : l ∈ leaves finish) : l ∉ history := by
  induction ht with
  | nil => simp
  | step p s a b r hl tail ih =>
    have hs := tail.leaves_sublist.subset hf
    have hnot : l ∉ a.support ++ b.support := by
      intro hin
      exact sigma_input_absent_output hl hw hd l htag hin hs
    have hd' := hd.sublist (leaves_step_sublist p s a b r)
    have hi := ih (typed_step hl hw) hd' hf
    simpa only [List.mem_append, not_or] using And.intro hnot hi
end Candidate.ShortWordLineage
