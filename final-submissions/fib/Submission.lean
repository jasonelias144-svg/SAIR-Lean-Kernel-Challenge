import Spec

/-!
# Fibonacci by fast doubling in continuation-passing style

`pk fuel m k` calls `k (fib m) (fib (m + 1))`. For `m > 0` it recurses on
`h = m / 2`, receives `a = fib h`, `b = fib (h + 1)`, and continues with

* `fib (2h) = a * (2b - a)` and `fib (2h + 1) = a² + b²` if `m` is even,
* `fib (2h + 1)` and `fib (2h + 2) = fib (2h) + fib (2h + 1)` if `m` is odd.

The loop is a `Nat.rec` on `fuel = n`, but each level only unfolds when the
previous one asks for it, so about `log₂ n` levels run. Values are passed to a
continuation rather than packed in a pair, and the top-level continuation
ignores `fib (n + 1)`, so that value is never computed. Word operations call
`Nat.*` directly.

The fast-doubling identities are Mathlib's `Nat.fib_two_mul` and
`Nat.fib_two_mul_add_one`. (The published Contributor Network package
"Fibonacci-sol" by shalashaska117 uses the same fast doubling with a pair
structure.)
-/

namespace Submission

/-- `pk fuel m k = k (fib m) (fib (m + 1))` whenever `m ≤ fuel`. -/
def pk (fuel : Nat) : Nat → (Nat → Nat → Nat) → Nat :=
  Nat.rec (motive := fun _ => Nat → (Nat → Nat → Nat) → Nat) (fun _ k => k 0 1)
    (fun _ ih m k => cond (Nat.beq m 0) (k 0 1)
      (ih (Nat.div m 2) (fun a b =>
        (fun c d => cond (Nat.beq (Nat.mod m 2) 0) (k c d) (k d (Nat.add c d)))
          (Nat.mul a (Nat.sub (Nat.mul 2 b) a)) (Nat.add (Nat.mul a a) (Nat.mul b b))))) fuel

def impl (n : Nat) : Nat := pk n n (fun a _ => a)

theorem pk_eq : ∀ fuel m, m ≤ fuel → ∀ k : Nat → Nat → Nat,
    pk fuel m k = k (Nat.fib m) (Nat.fib (m + 1))
  | 0, m, hm, k => by
    have : m = 0 := by omega
    subst this; rfl
  | fuel + 1, m, hm, k => by
    show cond (Nat.beq m 0) (k 0 1) (pk fuel (Nat.div m 2) (fun a b =>
        (fun c d => cond (Nat.beq (Nat.mod m 2) 0) (k c d) (k d (Nat.add c d)))
          (Nat.mul a (Nat.sub (Nat.mul 2 b) a)) (Nat.add (Nat.mul a a) (Nat.mul b b)))) = _
    by_cases hm0 : m = 0
    · subst hm0; rfl
    · have hb : Nat.beq m 0 = false := by
        rw [Bool.eq_false_iff]; intro h; rw [Nat.beq_eq] at h; exact hm0 h
      rw [hb, cond_false, pk_eq fuel (Nat.div m 2) (by show m / 2 ≤ fuel; omega)]
      show cond (Nat.beq (m % 2) 0)
        (k (Nat.fib (m / 2) * (2 * Nat.fib (m / 2 + 1) - Nat.fib (m / 2)))
          (Nat.fib (m / 2) * Nat.fib (m / 2) + Nat.fib (m / 2 + 1) * Nat.fib (m / 2 + 1)))
        (k (Nat.fib (m / 2) * Nat.fib (m / 2) + Nat.fib (m / 2 + 1) * Nat.fib (m / 2 + 1))
          (Nat.fib (m / 2) * (2 * Nat.fib (m / 2 + 1) - Nat.fib (m / 2)) +
            (Nat.fib (m / 2) * Nat.fib (m / 2) + Nat.fib (m / 2 + 1) * Nat.fib (m / 2 + 1)))) = _
      have h2 : Nat.fib (m / 2) * (2 * Nat.fib (m / 2 + 1) - Nat.fib (m / 2)) =
          Nat.fib (2 * (m / 2)) := (Nat.fib_two_mul _).symm
      have h1 : Nat.fib (m / 2) * Nat.fib (m / 2) + Nat.fib (m / 2 + 1) * Nat.fib (m / 2 + 1) =
          Nat.fib (2 * (m / 2) + 1) := by
        rw [Nat.fib_two_mul_add_one, Nat.pow_two, Nat.pow_two, Nat.add_comm]
      rw [h1, h2]
      rcases Nat.mod_two_eq_zero_or_one m with he | ho
      · rw [show Nat.beq (m % 2) 0 = true by rw [he]; rfl, cond_true,
          show 2 * (m / 2) = m by omega]
      · rw [show Nat.beq (m % 2) 0 = false by rw [ho]; rfl, cond_false,
          ← Nat.fib_add_two, show 2 * (m / 2) + 1 = m by omega,
          show 2 * (m / 2) + 2 = m + 1 by omega]

theorem impl_correct : ∀ n, impl n = fibSpec n := by
  intro n
  exact pk_eq n n (Nat.le_refl n) (fun a _ => a)

end Submission
