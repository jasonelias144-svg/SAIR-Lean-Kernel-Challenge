import Spec

/-!
Least-prime recurrence for μ, then the inclusive sum M(n).
-/

namespace Submission

open Nat
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

def moebiusRec (n : Nat) : Int :=
  if n = 0 then 0
  else if n = 1 then 1
  else
    let p := n.minFac
    if p * p ∣ n then 0
    else -moebiusRec (n / p)
termination_by n
decreasing_by
  have hne1 : n ≠ 1 := by
    intro h; subst h; contradiction
  have hp : Nat.Prime n.minFac := Nat.minFac_prime hne1
  have hnpos : 0 < n := by
    match n with
    | 0 => contradiction
    | n + 1 => exact Nat.succ_pos _
  exact Nat.div_lt_self hnpos hp.one_lt

theorem moebiusRec_eq : ∀ n, moebiusRec n = moebius n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h0 : n = 0
    · subst n
      simp [moebiusRec]
    · by_cases h1 : n = 1
      · subst n
        simp [moebiusRec]
      · set p := n.minFac
        have hp : Nat.Prime p := Nat.minFac_prime h1
        have hdiv : p ∣ n := Nat.minFac_dvd n
        have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hlt : n / p < n := Nat.div_lt_self hnpos hp.one_lt
        by_cases hsq : p * p ∣ n
        · have hns : ¬ Squarefree n := by
            intro hs
            exact (Nat.squarefree_iff_prime_squarefree.1 hs p hp) hsq
          have : moebiusRec n = 0 := by
            rw [moebiusRec, if_neg h0, if_neg h1, if_pos hsq]
          simp [this, moebius_eq_zero_of_not_squarefree hns]
        · have hform : moebiusRec n = -moebiusRec (n / p) := by
            rw [moebiusRec, if_neg h0, if_neg h1, if_neg hsq]
          have hih : moebiusRec (n / p) = moebius (n / p) := ih (n / p) hlt
          have hprod : p * (n / p) = n := Nat.mul_div_cancel' hdiv
          have hcop : Nat.Coprime p (n / p) := by
            rw [hp.coprime_iff_not_dvd]
            intro hd
            exact hsq ((Nat.dvd_div_iff_mul_dvd hdiv).1 hd)
          calc
            moebiusRec n = -moebiusRec (n / p) := hform
            _ = -moebius (n / p) := by rw [hih]
            _ = moebius p * moebius (n / p) := by
              rw [moebius_apply_prime hp]; norm_num
            _ = moebius (p * (n / p)) :=
              (isMultiplicative_moebius.map_mul_of_coprime hcop).symm
            _ = moebius n := by rw [hprod]

def impl (n : Nat) : Int :=
  ∑ k ∈ Finset.range (n + 1), moebiusRec k

theorem impl_correct : ∀ n, impl n = mertensSpec n := by
  intro n
  simp only [impl, mertensSpec, moebiusRec_eq]

end Submission
