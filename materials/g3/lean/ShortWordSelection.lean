import ShortWordTerminalDelete

/-! Whole-history finite selection and its non-circular terminal-deletion adapter.
The cardinality hypothesis in these generic helpers is discharged by the mark
bound module; it is not an asserted proof of either numerical mark bound. -/
namespace Candidate.ShortWordSelection
open Candidate.ShortWordDelete Candidate.ShortWordRecovery Candidate.ShortWordTerminalDelete

theorem exists_clean_of_card_lt (atoms : List Atom) (history : List Leaf)
    (h : (allMarks history).card < atoms.length) :
    ∃ e, e < atoms.length ∧ clean e history = true := by
  obtain ⟨e, he, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := allMarks history) (t := Finset.range atoms.length) (by simpa using h)
  exact ⟨e, Finset.mem_range.mp he, (clean_iff_not_marked e history).mpr hm⟩

theorem split_at_position (atoms : List Atom) (e : ℕ) (he : e < atoms.length) :
    ∃ pre kind post, atoms = pre ++ kind :: post ∧ pre.length = e := by
  induction atoms generalizing e with
  | nil => simp at he
  | cons first atoms ih =>
    cases e with
    | zero => exact ⟨[], first, atoms, rfl, rfl⟩
    | succ e =>
      obtain ⟨pre, kind, post, hsplit, hlen⟩ := ih e (by simpa using he)
      exact ⟨first :: pre, kind, post, by simp [hsplit], by simp [hlen]⟩

theorem terminal_deletion_of_card_lt {atoms : List Atom} {n : ℕ}
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (ht : ShortWordDelete.Trace (expandChronological (numberFrom 0 atoms)) rules history finish)
    (he : values finish = terminal n) (hb : (allMarks history).card < atoms.length) :
    ∃ (e : ℕ) (pre : List Atom) (kind : Atom) (post : List Atom),
      e < atoms.length ∧ atoms = pre ++ kind :: post ∧ pre.length = e ∧
      clean e history = true ∧ (kind = .a ∨ kind = .b) ∧
      ShortWordDelete.Trace (expandChronological (numberFrom 0 (pre ++ post))) rules
        (history.map (relabelLeaf e)) (eraseOwner e finish) ∧
      values (eraseOwner e finish) = terminal (n - 1) := by
  obtain ⟨e, hei, hc⟩ := exists_clean_of_card_lt atoms history hb
  obtain ⟨pre, kind, post, hs, hp⟩ := split_at_position atoms e hei
  have ht' := ht
  rw [hs] at ht'
  have hc' : clean pre.length history = true := by simpa [hp] using hc
  have hk := (numbered_recovery pre post n kind ht' hc' he).1
  have hd := numbered_terminal_deletion pre post n kind ht' hc' he
  rw [hp] at hd
  exact ⟨e, pre, kind, post, hei, hs, hp, hc, hk, hd⟩

theorem research_deletion_of_card_lt {atoms : List Atom} {n : ℕ}
    {rules : List Rule} {history : List Leaf} {finish : List Token} (hn : 7 ≤ n)
    (ht : ShortWordDelete.Trace (expandChronological (numberFrom 0 atoms)) rules history finish)
    (he : values finish = terminal n) (hb : (allMarks history).card < atoms.length) :
    ∃ (e : ℕ) (pre : List Atom) (kind : Atom) (post : List Atom),
      e < atoms.length ∧ atoms = pre ++ kind :: post ∧ pre.length = e ∧
      clean e history = true ∧ 6 ≤ n - 1 ∧
      ShortWordDelete.Trace (expandChronological (numberFrom 0 (pre ++ post))) rules
        (history.map (relabelLeaf e)) (eraseOwner e finish) ∧
      values (eraseOwner e finish) = terminal (n - 1) := by
  obtain ⟨e, hei, hc⟩ := exists_clean_of_card_lt atoms history hb
  obtain ⟨pre, kind, post, hs, hp⟩ := split_at_position atoms e hei
  have ht' := ht
  rw [hs] at ht'
  have hc' : clean pre.length history = true := by simpa [hp] using hc
  have hd := numbered_terminal_deletion_research pre post n kind hn ht' hc' he
  rw [hp] at hd
  exact ⟨e, pre, kind, post, hei, hs, hp, hc, hd⟩
end Candidate.ShortWordSelection
