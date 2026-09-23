import Spec

/-!
Fibonacci experiment: structural recursion with explicit pair matching.
The halving recurrence and proof structure are adapted from the challenge's
Apache-2.0-licensed worked Fibonacci example. The odd branch instead uses
F(2m+2) = F(m+1) * (2*F(m) + F(m+1)), as in Mathlib's fastFib.

The recursion budget is the bit length of the input, rather than its value.
The proof establishes correctness whenever n < 2^fuel.
-/

namespace Submission

def pair : Nat → Nat → Nat × Nat
  | 0, _ => (0, 1)
  | _ + 1, 0 => (0, 1)
  | fuel + 1, n + 1 =>
    match pair fuel ((n + 1) / 2) with
    | (a, b) =>
      if (n + 1) % 2 = 0 then
        (a * (2 * b - a), b * b + a * a)
      else
        (b * b + a * a, b * (2 * a + b))

theorem pair_correct : (fuel n : Nat) → n < 2 ^ fuel →
    pair fuel n = (Nat.fib n, Nat.fib (n + 1))
  | 0, n, h => by
    have hn : n = 0 := Nat.lt_one_iff.mp (by simpa using h)
    subst n
    rfl
  | _ + 1, 0, _ => rfl
  | fuel + 1, n + 1, h => by
    have hdiv : (n + 1) / 2 < 2 ^ fuel := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
      simpa only [Nat.pow_succ] using h
    have ih := pair_correct fuel ((n + 1) / 2) hdiv
    simp only [pair, ih]
    by_cases hp : (n + 1) % 2 = 0
    · rw [if_pos hp]
      have e0 : 2 * ((n + 1) / 2) = n + 1 := by omega
      have e1 : 2 * ((n + 1) / 2) + 1 = n + 2 := by omega
      have he := Nat.fib_two_mul ((n + 1) / 2)
      have ho := Nat.fib_two_mul_add_one ((n + 1) / 2)
      rw [e0] at he
      rw [e1] at ho
      simpa only [pow_two] using congrArg₂ Prod.mk he.symm ho.symm
    · rw [if_neg hp]
      have e1 : 2 * ((n + 1) / 2) + 1 = n + 1 := by omega
      have e2 : 2 * ((n + 1) / 2) + 2 = n + 2 := by omega
      have ho := Nat.fib_two_mul_add_one ((n + 1) / 2)
      have hn := Nat.fib_two_mul_add_two ((n + 1) / 2)
      rw [e1] at ho
      rw [e2] at hn
      simpa only [pow_two] using congrArg₂ Prod.mk ho.symm hn.symm

def impl (n : Nat) : Nat := (pair (n.log2 + 1) n).1

theorem impl_correct : ∀ n, impl n = Nat.fib n := by
  intro n
  show (pair (n.log2 + 1) n).1 = Nat.fib n
  rw [pair_correct (n.log2 + 1) n Nat.lt_log2_self]

end Submission
