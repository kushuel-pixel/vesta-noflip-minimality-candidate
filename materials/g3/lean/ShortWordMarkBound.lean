import ShortWordNoZ

/-! Arbitrary-trace whole-history mark bounds and original-position deletion.
No normalization, greediness, PSL/SL interpretation or edited-trace premise.
The sufficient accounting bound used here is |R| ≤ 2(U+V+Z), together with
|S\R| ≤ T and Z=0 ⇒ S⊆R. It avoids needing the sharper processed-output count. -/
namespace Candidate.ShortWordMarkBound
open Candidate.ShortWordDelete Candidate.ShortWordRecovery Candidate.ShortWordTerminalDelete
open Candidate.ShortWordSelection Candidate.ShortWordCounts Candidate.ShortWordMarkAccounting
open Candidate.ShortWordLineage Candidate.ShortWordOverlap Candidate.ShortWordNoZ

theorem numbered_marks_general {atoms : List Atom} {n : ℕ}
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (ht : ShortWordDelete.Trace (expandChronological (numberFrom 0 atoms)) rules history finish)
    (he : values finish = terminal n) :
    (allMarks history).card ≤ 2 * (rules.count .u + rules.count .v + rules.count .z) + rules.count .t := by
  have hs := sigma_outside_bound ht (Finset.Subset.refl _) he (expandChronological_typed _)
    (initial_nodup 0 atoms) (initial_sigma_singleton _) (initial_companions atoms _)
  have hr := numbered_rho_marks_bound ht
  rw [allMarks_union, ← Finset.card_sdiff_add_card]
  omega

theorem numbered_marks_no_z {atoms : List Atom} {n : ℕ}
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (ht : ShortWordDelete.Trace (expandChronological (numberFrom 0 atoms)) rules history finish)
    (he : values finish = terminal n) (hz : Rule.z ∉ rules) :
    (allMarks history).card ≤ 2 * (rules.count .u + rules.count .v + rules.count .z) := by
  have hs := sigma_subset_rho_no_z ht hz he (expandChronological_typed _)
    (initial_nodup 0 atoms) (initial_sigma_singleton _) (initial_companions atoms ∅)
  rw [allMarks_union, Finset.union_eq_right.mpr hs]
  exact numbered_rho_marks_bound ht

/-- L1: whole-history bound, for any valid Trace and every natural n. -/
theorem marks_le_ten {atoms : List Atom} {n : ℕ}
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (ht : ShortWordDelete.Trace (expandChronological (numberFrom 0 atoms)) rules history finish)
    (he : values finish = terminal n) (hq : atoms.length = n + 5) :
    (allMarks history).card ≤ 10 := by
  have hb := numbered_balance ht he hq
  by_cases hz : Rule.z ∈ rules
  · have hc : 0 < rules.count Rule.z := List.count_pos_iff.mpr hz
    have hm := numbered_marks_general ht he
    omega
  · have hc : rules.count Rule.z = 0 := List.count_eq_zero.mpr hz
    have hm := numbered_marks_no_z ht he hz
    omega

/-- L2: whole-history bound, for any valid Trace and every natural n. -/
theorem marks_le_six {atoms : List Atom} {n : ℕ}
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (ht : ShortWordDelete.Trace (expandChronological (numberFrom 0 atoms)) rules history finish)
    (he : values finish = terminal n) (hq : atoms.length = n + 3) :
    (allMarks history).card ≤ 6 := by
  have hb := numbered_balance ht he hq
  by_cases hz : Rule.z ∈ rules
  · have hc : 0 < rules.count Rule.z := List.count_pos_iff.mpr hz
    have hm := numbered_marks_general ht he
    omega
  · have hc : rules.count Rule.z = 0 := List.count_eq_zero.mpr hz
    have hm := numbered_marks_no_z ht he hz
    omega

theorem marks_card_lt_length {atoms : List Atom} {n : ℕ}
    {rules : List Rule} {history : List Leaf} {finish : List Token} (hn : 6 ≤ n)
    (ht : ShortWordDelete.Trace (expandChronological (numberFrom 0 atoms)) rules history finish)
    (he : values finish = terminal n) (hq : atoms.length = n + 5 ∨ atoms.length = n + 3) :
    (allMarks history).card < atoms.length := by
  rcases hq with hq | hq
  · have := marks_le_ten ht he hq; omega
  · have := marks_le_six ht he hq; omega

/-- L3 includes n=6; the position refers to the original chronological list. -/
theorem exists_clean_original {atoms : List Atom} {n : ℕ}
    {rules : List Rule} {history : List Leaf} {finish : List Token} (hn : 6 ≤ n)
    (ht : ShortWordDelete.Trace (expandChronological (numberFrom 0 atoms)) rules history finish)
    (he : values finish = terminal n) (hq : atoms.length = n + 5 ∨ atoms.length = n + 3) :
    ∃ e, e < atoms.length ∧ clean e history = true :=
  exists_clean_of_card_lt atoms history (marks_card_lt_length hn ht he hq)

/-- L4: positivity, edited Trace and terminal decrement are all conclusions. -/
theorem exists_terminal_deletion {atoms : List Atom} {n : ℕ}
    {rules : List Rule} {history : List Leaf} {finish : List Token} (hn : 6 ≤ n)
    (ht : ShortWordDelete.Trace (expandChronological (numberFrom 0 atoms)) rules history finish)
    (he : values finish = terminal n) (hq : atoms.length = n + 5 ∨ atoms.length = n + 3) :
    ∃ (e : ℕ) (pre : List Atom) (kind : Atom) (post : List Atom),
      e < atoms.length ∧ atoms = pre ++ kind :: post ∧ pre.length = e ∧
      clean e history = true ∧ (kind = .a ∨ kind = .b) ∧
      ShortWordDelete.Trace (expandChronological (numberFrom 0 (pre ++ post))) rules
        (history.map (relabelLeaf e)) (eraseOwner e finish) ∧
      values (eraseOwner e finish) = terminal (n - 1) :=
  terminal_deletion_of_card_lt ht he (marks_card_lt_length hn ht he hq)

/-- Research-domain deletion requires n≥7, separately from n=6 existence. -/
theorem exists_research_terminal_deletion {atoms : List Atom} {n : ℕ}
    {rules : List Rule} {history : List Leaf} {finish : List Token} (hn : 7 ≤ n)
    (ht : ShortWordDelete.Trace (expandChronological (numberFrom 0 atoms)) rules history finish)
    (he : values finish = terminal n) (hq : atoms.length = n + 5 ∨ atoms.length = n + 3) :
    ∃ (e : ℕ) (pre : List Atom) (kind : Atom) (post : List Atom),
      e < atoms.length ∧ atoms = pre ++ kind :: post ∧ pre.length = e ∧
      clean e history = true ∧ 6 ≤ n - 1 ∧
      ShortWordDelete.Trace (expandChronological (numberFrom 0 (pre ++ post))) rules
        (history.map (relabelLeaf e)) (eraseOwner e finish) ∧
      values (eraseOwner e finish) = terminal (n - 1) :=
  research_deletion_of_card_lt hn ht he (marks_card_lt_length (by omega) ht he hq)
end Candidate.ShortWordMarkBound
