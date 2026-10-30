import ShortWordDelete
import ShortWordRecovery
namespace Candidate.ShortWordCounts
open Candidate.ShortWordDelete Candidate.ShortWordRecovery

def sigmaCount (w : List Token) : ℕ := (w.map (fun t => if t.value = .sigma then 1 else 0)).sum
def rhoCount (w : List Token) : ℕ := (w.map (fun t => if t.value = .sigma then 0 else 1)).sum

@[simp] theorem sigmaCount_append (p s : List Token) :
    sigmaCount (p ++ s) = sigmaCount p + sigmaCount s := by simp [sigmaCount]
@[simp] theorem rhoCount_append (p s : List Token) :
    rhoCount (p ++ s) = rhoCount p + rhoCount s := by simp [rhoCount]

theorem trace_balance {start finish : List Token} {rules : List Rule} {history : List Leaf}
    (ht : ShortWordDelete.Trace start rules history finish) :
    sigmaCount start = sigmaCount finish + 2 * rules.count .t ∧
    rhoCount start = rhoCount finish + rules.count .u + rules.count .v + 2 * rules.count .z := by
  induction ht with
  | nil w => simp
  | step p s a b r hl tail ih =>
    cases r <;> simp only [Legal] at hl
    all_goals obtain ⟨ha, hb, hv⟩ := hl
    case t =>
      obtain ⟨hva,hvb⟩ := hv
      simp [sigmaCount, rhoCount, output, hva, hvb] at ih ⊢
      omega
    case u =>
      obtain ⟨hva,hvb⟩ := hv
      simp [sigmaCount, rhoCount, output, hva, hvb] at ih ⊢
      omega
    case v =>
      obtain ⟨hva,hvb⟩ := hv
      simp [sigmaCount, rhoCount, output, hva, hvb] at ih ⊢
      omega
    case z =>
      rcases hv with ⟨hva,hvb⟩ | ⟨hva,hvb⟩ <;>
        simp [sigmaCount, rhoCount, output, hva, hvb] at ih ⊢ <;> omega

theorem initial_counts (atoms : List (ℕ × Atom)) :
    sigmaCount (expandChronological atoms) = atoms.length ∧
    rhoCount (expandChronological atoms) = atoms.length := by
  induction atoms with
  | nil => simp [expandChronological, sigmaCount, rhoCount]
  | cons a atoms ih =>
    rcases a with ⟨e,kind⟩
    have h : expandChronological ((e,kind) :: atoms) =
        expandChronological atoms ++ expandAtom e kind := by simp [expandChronological]
    rw [h, sigmaCount_append, rhoCount_append, ih.1, ih.2]
    cases kind <;> simp [expandAtom, leafToken, sigmaCount, rhoCount]

theorem terminal_counts {finish : List Token} {n : ℕ}
    (he : values finish = terminal n) : sigmaCount finish = n + 1 ∧ rhoCount finish = n := by
  have hs : ∀ n, ((terminal n).map (fun v => if v = Factor.sigma then 1 else 0)).sum = n+1 := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => simp [terminal, ih]; omega
  have hr : ∀ n, ((terminal n).map (fun v => if v = Factor.sigma then 0 else 1)).sum = n := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => simp [terminal, ih, Nat.add_comm]
  have hs' := hs n
  have hr' := hr n
  rw [← he] at hs' hr'
  exact ⟨by simpa [values, sigmaCount, List.map_map, Function.comp_def] using hs',
    by simpa [values, rhoCount, List.map_map, Function.comp_def] using hr'⟩

theorem numbered_balance {atoms : List Atom} {n d : ℕ}
    {rules : List Rule} {history : List Leaf} {finish : List Token}
    (ht : ShortWordDelete.Trace (expandChronological (numberFrom 0 atoms)) rules history finish)
    (he : values finish = terminal n) (hq : atoms.length = n + d) :
    2 * rules.count .t + 1 = d ∧
    rules.count .u + rules.count .v + 2 * rules.count .z = d := by
  have hb := trace_balance ht
  have hi := initial_counts (numberFrom 0 atoms)
  have hf := terminal_counts he
  simp only [numberFrom_length] at hi
  omega
end Candidate.ShortWordCounts
