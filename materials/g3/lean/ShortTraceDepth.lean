import BoundScope

namespace Candidate.ShortTraceDepth
open Candidate.ShortWordDelete Candidate.ShortWordRecovery Candidate.ShortWordCounts

theorem rule_count_partition (rs : List Rule) :
    rs.length = rs.count .t + rs.count .u + rs.count .v + rs.count .z := by
  induction rs with
  | nil => rfl
  | cons r rs ih => cases r <;> simp_all <;> omega

theorem depth_nplus5 {atoms : List Atom} {n : ℕ}
    {rs : List Rule} {h : List Leaf} {f : List Token}
    (ht : Trace (expandChronological (numberFrom 0 atoms)) rs h f)
    (he : values f = terminal n) (hq : atoms.length = n+5) :
    rs.length + rs.count .z = 7 := by
  have hb := numbered_balance ht he hq
  have hc := rule_count_partition rs
  omega

theorem depth_nplus3 {atoms : List Atom} {n : ℕ}
    {rs : List Rule} {h : List Leaf} {f : List Token}
    (ht : Trace (expandChronological (numberFrom 0 atoms)) rs h f)
    (he : values f = terminal n) (hq : atoms.length = n+3) :
    rs.length + rs.count .z = 4 := by
  have hb := numbered_balance ht he hq
  have hc := rule_count_partition rs
  omega

theorem depth_le_seven {atoms : List Atom} {n : ℕ}
    {rs : List Rule} {h : List Leaf} {f : List Token}
    (ht : Trace (expandChronological (numberFrom 0 atoms)) rs h f)
    (he : values f = terminal n) (hq : atoms.length = n+5 ∨ atoms.length = n+3) :
    rs.length ≤ 7 := by
  rcases hq with hq | hq
  · have := depth_nplus5 ht he hq; omega
  · have := depth_nplus3 ht he hq; omega

end Candidate.ShortTraceDepth
