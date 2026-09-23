import Spec

/-!
π(n) by least-prime test: `p` is prime iff `2 ≤ p` and `minFac p = p`.
Count with a successor recurrence instead of `List.range`.
-/

namespace Submission

def isPrime (p : Nat) : Bool := decide (2 ≤ p) && (Nat.minFac p == p)

theorem isPrime_eq (p : Nat) : isPrime p = decide (Nat.Prime p) := by
  apply Bool.eq_iff_iff.mpr
  simp [isPrime, Nat.prime_def_minFac]

def impl : Nat → Nat
  | 0 => 0
  | n + 1 => impl n + if isPrime (n + 1) then 1 else 0

theorem impl_eq_count : ∀ n, impl n = Nat.count Nat.Prime (n + 1) := by
  intro n
  induction n with
  | zero =>
    simp [impl, Nat.count, Nat.not_prime_zero]
  | succ n ih =>
    simp [impl, ih, Nat.count_succ, isPrime_eq]

theorem impl_correct : ∀ n, impl n = primeCountSpec n := by
  intro n
  simp [impl_eq_count, primeCountSpec, Nat.primeCounting, Nat.primeCounting']

end Submission
