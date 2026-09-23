import Spec

/-!
Fibonacci optimization visit 1: two-square doubling.
The implied triple (a,b,a+b) gives Cassini's alternating invariant.
It replaces the extra large multiplication in a full doubling step with
two shared squares and small-coefficient arithmetic. The recursion budget
and proof skeleton follow our accepted bit-length baseline, adapted from
the Apache-2.0 SAIR worked example.
-/

namespace Submission

theorem cassini (n : Nat) :
    if n % 2 = 0 then
      Nat.fib (n + 1) ^ 2 = Nat.fib n ^ 2 + Nat.fib n * Nat.fib (n + 1) + 1
    else
      Nat.fib n ^ 2 + Nat.fib n * Nat.fib (n + 1) = Nat.fib (n + 1) ^ 2 + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    change if (n + 1) % 2 = 0 then
      Nat.fib (n + 2) ^ 2 = Nat.fib (n + 1) ^ 2 + Nat.fib (n + 1) * Nat.fib (n + 2) + 1
      else Nat.fib (n + 1) ^ 2 + Nat.fib (n + 1) * Nat.fib (n + 2) = Nat.fib (n + 2) ^ 2 + 1
    rw [Nat.fib_add_two]
    by_cases h : n % 2 = 0
    · have hs : (n + 1) % 2 ≠ 0 := by omega
      simp only [if_pos h] at ih
      simp only [if_neg hs]
      ring_nf at ih ⊢
      omega
    · have hs : (n + 1) % 2 = 0 := by omega
      simp only [if_neg h] at ih
      simp only [if_pos hs]
      ring_nf at ih ⊢
      omega

def step (k a b : Nat) (odd : Bool) : Nat × Nat :=
  let u := a * a
  let v := b * b
  let correction := if k % 2 = 0 then 0 else 4
  if odd then
    (u + v, 3 * v + correction - (2 * u + 2))
  else
    (2 * v + correction - (3 * u + 2), u + v)

theorem square_forms (k : Nat) :
    let u := Nat.fib k * Nat.fib k
    let v := Nat.fib (k + 1) * Nat.fib (k + 1)
    let correction := if k % 2 = 0 then 0 else 4
    (2 * v + correction - (3 * u + 2) = Nat.fib (2 * k)) ∧
    (u + v = Nat.fib (2 * k + 1)) ∧
    (3 * v + correction - (2 * u + 2) = Nat.fib (2 * k + 2)) := by
  have hc := cassini k
  have ho := Nat.fib_two_mul_add_one k
  have hn := Nat.fib_two_mul_add_two k
  have hr := Nat.fib_add_two (n := 2 * k)
  dsimp only
  by_cases h : k % 2 = 0
  · simp only [if_pos h] at hc ⊢
    ring_nf at hc ho hn hr ⊢
    constructor <;> (try constructor) <;> omega
  · simp only [if_neg h] at hc ⊢
    ring_nf at hc ho hn hr ⊢
    constructor <;> (try constructor) <;> omega

theorem step_even (k : Nat) :
    step k (Nat.fib k) (Nat.fib (k + 1)) false =
      (Nat.fib (2 * k), Nat.fib (2 * k + 1)) := by
  have h := square_forms k
  simp only [step, Bool.false_eq_true, ↓reduceIte]
  exact congrArg₂ Prod.mk h.1 h.2.1

theorem step_odd (k : Nat) :
    step k (Nat.fib k) (Nat.fib (k + 1)) true =
      (Nat.fib (2 * k + 1), Nat.fib (2 * k + 2)) := by
  have h := square_forms k
  simp only [step, ↓reduceIte]
  exact congrArg₂ Prod.mk h.2.1 h.2.2

def pair : Nat → Nat → Nat × Nat
  | 0, _ => (0, 1)
  | _ + 1, 0 => (0, 1)
  | fuel + 1, n + 1 =>
    match pair fuel ((n + 1) / 2) with
    | (a, b) => step ((n + 1) / 2) a b (decide ((n + 1) % 2 ≠ 0))

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
    · have e0 : 2 * ((n + 1) / 2) = n + 1 := by omega
      have e1 : 2 * ((n + 1) / 2) + 1 = n + 2 := by omega
      simp only [hp, ne_eq, not_true_eq_false, decide_false]
      rw [step_even, e0]
    · have e1 : 2 * ((n + 1) / 2) + 1 = n + 1 := by omega
      have e2 : 2 * ((n + 1) / 2) + 2 = n + 2 := by omega
      have hd : decide ((n + 1) % 2 ≠ 0) = true := by simp [hp]
      rw [hd, step_odd, e1, e2]

def impl (n : Nat) : Nat := (pair (n.log2 + 1) n).1

theorem impl_correct : ∀ n, impl n = Nat.fib n := by
  intro n
  show (pair (n.log2 + 1) n).1 = Nat.fib n
  rw [pair_correct (n.log2 + 1) n Nat.lt_log2_self]

end Submission
