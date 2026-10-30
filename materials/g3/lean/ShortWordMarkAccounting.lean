import ShortWordCounts
namespace Candidate.ShortWordMarkAccounting
open Candidate.ShortWordDelete Candidate.ShortWordRecovery Candidate.ShortWordCounts

@[simp] theorem marks_append (tag : Tag) (xs ys : List Leaf) :
    marks tag (xs ++ ys) = marks tag xs ∪ marks tag ys := by
  ext e; simp only [mem_marks_iff, List.mem_append, Finset.mem_union]; aesop

/-- A live support either remains a single original leaf or was already read.
The set parameter records the past; it never reconstructs erased history. -/
def Covered (past : Finset ℕ) (w : List Token) : Prop :=
  ∀ t ∈ w, (marks .rho t.support ⊆ past) ∨ t.support.length = 1

theorem marks_card_le_one {ls : List Leaf} (h : ls.length = 1) :
    (marks .rho ls).card ≤ 1 := by
  obtain ⟨l, rfl⟩ := List.length_eq_one_iff.mp h
  cases l with | mk e tag => cases tag <;> simp [marks]

theorem card_union_le_add_one {past : Finset ℕ} {ls : List Leaf}
    (h : marks .rho ls ⊆ past ∨ ls.length = 1) :
    (past ∪ marks .rho ls).card ≤ past.card + 1 := by
  rcases h with h | h
  · rw [Finset.union_eq_left.mpr h]; omega
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left (marks_card_le_one h) _)

theorem covered_step {past : Finset ℕ} {p s : List Token} {a b : Token} (r : Rule)
    (hw : Covered past (p ++ [a,b] ++ s)) :
    Covered (past ∪ (marks .rho a.support ∪ marks .rho b.support))
      (p ++ output r a b ++ s) := by
  intro t ht
  have hsub : past ⊆ past ∪ (marks .rho a.support ∪ marks .rho b.support) :=
    Finset.subset_union_left
  simp only [List.mem_append] at ht
  rcases ht with (hp | ho) | hs
  · rcases hw t (by simp [hp]) with h | h
    · exact Or.inl (h.trans hsub)
    · exact Or.inr h
  · cases r <;> simp only [output, List.mem_singleton, List.not_mem_nil] at ho
    all_goals subst t; left; simp only [marks_append]; exact Finset.subset_union_right
  · rcases hw t (by simp [hs]) with h | h
    · exact Or.inl (h.trans hsub)
    · exact Or.inr h

theorem rho_marks_bound {start finish : List Token} {rules : List Rule} {history : List Leaf}
    (ht : ShortWordDelete.Trace start rules history finish) (past : Finset ℕ)
    (hw : Covered past start) (hwt : TypedState start) :
    (past ∪ marks .rho history).card ≤
      past.card + 2 * (rules.count .u + rules.count .v + rules.count .z) := by
  induction ht generalizing past with
  | nil w => simp [marks]
  | step p s a b r hl tail ih =>
    have ha := hw a (by simp)
    have hb := hw b (by simp)
    have haT := hwt a (by simp)
    have hbT := hwt b (by simp)
    have hw' := covered_step r hw
    have ht' : TypedState (p ++ output r a b ++ s) := by
      intro t ht
      simp only [List.mem_append] at ht
      rcases ht with (hp | ho) | hs
      · exact hwt t (by simp [hp])
      · exact typed_output r a b hl haT hbT t ho
      · exact hwt t (by simp [hs])
    have hi := ih _ hw' ht'
    have hcard : (past ∪ (marks .rho a.support ∪ marks .rho b.support)).card ≤ past.card + 2 := by
      have hc1 := card_union_le_add_one ha
      have hb' : marks .rho b.support ⊆ past ∪ marks .rho a.support ∨ b.support.length = 1 :=
        hb.imp (fun h => h.trans Finset.subset_union_left) id
      have hc2 := card_union_le_add_one hb'
      rw [Finset.union_assoc] at hc2
      omega
    simp only [marks_append, ← Finset.union_assoc] at hi ⊢
    cases r with
    | t =>
      have hva := hl.2.2.1
      have hvb := hl.2.2.2
      have empty_of_sigma (t : Token) (h : TypedToken t) (hv : t.value = .sigma) :
          marks .rho t.support = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e hm
        obtain ⟨l, hm, _, htag⟩ := (mem_marks_iff e .rho t.support).mp hm
        have h' := h.2 l hm
        simp [hv, factorTag, htag] at h'
      have ea := empty_of_sigma a haT hva
      have eb := empty_of_sigma b hbT hvb
      simpa [ea, eb] using hi
    | u => simp only [List.count_cons] at hi ⊢; simp at *; omega
    | v => simp only [List.count_cons] at hi ⊢; simp at *; omega
    | z => simp only [List.count_cons] at hi ⊢; simp at *; omega

theorem initial_covered (atoms : List (ℕ × Atom)) : Covered ∅ (expandChronological atoms) := by
  intro t ht
  obtain ⟨item, _, hm⟩ := List.mem_flatMap.mp ht
  rcases item with ⟨e,kind⟩
  right
  cases kind <;> simp [expandAtom, leafToken] at hm <;>
    rcases hm with rfl | rfl <;> rfl

theorem numbered_rho_marks_bound {atoms : List Atom} {rules : List Rule}
    {history : List Leaf} {finish : List Token}
    (ht : ShortWordDelete.Trace (expandChronological (numberFrom 0 atoms)) rules history finish) :
    (marks .rho history).card ≤ 2 * (rules.count .u + rules.count .v + rules.count .z) := by
  simpa using rho_marks_bound ht ∅ (initial_covered _) (expandChronological_typed _)
end Candidate.ShortWordMarkAccounting
