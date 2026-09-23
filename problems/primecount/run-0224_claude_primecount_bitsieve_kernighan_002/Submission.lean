import Spec

/-!
# Prime counting with a bit-packed sieve

The numbers `0 … n` are the bits of one natural number. Start with bits
`2 … n` set. For every `d` from `2` up to `D + 1`, where
`D = 2 ^ (log₂ n / 2 + 1)` (so `D * D > n`), clear the bits `2d, 3d, …`. The
pattern of those bits is one closed-form number,
`((2^{dK} - 1) / (2^d - 1)) <<< 2d` with `K = n / d + 1`, so each `d` costs a few
big-number operations. Clearing multiples of any `d ≥ 2` only removes
composites, and every composite `k ≤ n` has its least prime factor `p` with
`p * p ≤ n < D * D`, so the surviving bits are exactly the primes. The answer is
the number of surviving bits, counted one set bit at a time.

Loops are `Nat.rec`, word operations call `Nat.*` directly, and the numbers
used repeatedly (`2^(n+1) - 1` and the sieve) are forced to literals once with
`forceN`.
-/

namespace Submission

/-! ## Implementation -/

/-- Evaluate `x` before continuing (so it is computed once, not per use). -/
def forceN (x : Nat) (k : Nat → Nat) : Nat :=
  Nat.casesOn (motive := fun _ => Nat) x (k 0) (fun m => k (Nat.succ m))

/-- Bits `2d, 3d, …, (K + 1) d` with `K = n / d + 1`. -/
def mults (n d : Nat) : Nat :=
  Nat.shiftLeft
    (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul d (Nat.add (Nat.div n d) 1))) 1)
      (Nat.sub (Nat.shiftLeft 1 d) 1)) (Nat.mul 2 d)

/-- Bits `0 … n` of `all` set; clear `0`, `1`, then multiples of `2 … D + 1`. -/
def sieve (n all D : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.land all (Nat.xor all 3))
    (fun j S => forceN S fun S => Nat.land S (Nat.xor all (Nat.land (mults n (Nat.add j 2)) all)))
    D

/-- Number of set bits among bits `0 … m - 1` of `S`. -/
def count (S m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Nat.add acc (Nat.land (Nat.shiftRight S k) 1)) m

/-- Number of set bits of `x`, clearing the lowest set bit each step (`x &&& (x - 1)`),
so the loop runs once per set bit; `fuel` only bounds it. -/
def pop (fuel x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih x => cond (Nat.beq x 0) 0 (Nat.add (ih (Nat.land x (Nat.sub x 1))) 1)) fuel x

/-- Sieve bound `D = 2 ^ (log₂ n / 2 + 1)`. -/
def bound (n : Nat) : Nat := Nat.shiftLeft 1 (Nat.add (Nat.div (Nat.log2 n) 2) 1)

/-- `2 ^ (n + 1) - 1`: bits `0 … n`. -/
def allOf (n : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 (Nat.add n 1)) 1

def impl (n : Nat) : Nat :=
  forceN (allOf n) fun all =>
  forceN (sieve n all (bound n)) fun S =>
  pop (Nat.add n 1) S

/-! ## Correctness -/

theorem forceN_eq (x : Nat) (k : Nat → Nat) : forceN x k = k x := by
  cases x <;> rfl

/-- `pk X f L = f 0 + f 1 * X + … + f (L - 1) * X ^ (L - 1)`. -/
def pk (X : Nat) : (Nat → Nat) → Nat → Nat
  | _, 0 => 0
  | f, L + 1 => f 0 + X * pk X (fun i => f (i + 1)) L

/-- Bits of a packed vector with `2 ^ W`-sized fields. -/
theorem testBit_pk (W : Nat) (hW : 0 < W) : ∀ (L : Nat) (f : Nat → Nat),
    (∀ u, u < L → f u < 2 ^ W) → ∀ i,
    (pk (2 ^ W) f L).testBit i = (decide (i < W * L) && (f (i / W)).testBit (i % W))
  | 0, f, _, i => by simp [pk]
  | L + 1, f, hf, i => by
    simp only [pk]
    rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ (hf 0 (by omega))]
    by_cases hi : i < W
    · rw [if_pos hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
      have : i < W * (L + 1) := by
        have := Nat.mul_le_mul_left W (show 1 ≤ L + 1 by omega)
        omega
      simp [this]
    · rw [if_neg hi, testBit_pk W hW L (fun i => f (i + 1)) (fun u hu => hf (u + 1) (by omega))]
      have hge : W ≤ i := by omega
      rw [Nat.div_eq_sub_div hW hge, Nat.mod_eq_sub_mod hge]
      rw [show decide (i - W < W * L) = decide (i < W * (L + 1)) from
        decide_eq_decide.mpr (by rw [Nat.mul_succ]; omega)]

/-- `(2^d - 1) * (1 + 2^d + … + 2^{d(K-1)}) = 2^{dK} - 1`. -/
theorem geom (d : Nat) : ∀ K, (2 ^ d - 1) * pk (2 ^ d) (fun _ => 1) K = 2 ^ (d * K) - 1
  | 0 => by simp [pk]
  | K + 1 => by
    simp only [pk]
    have ih := geom d K
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (d * K) := Nat.one_le_two_pow
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, ih, Nat.mul_succ, Nat.pow_add,
      Nat.mul_sub, Nat.mul_one, Nat.mul_comm (2 ^ (d * K))]
    have h3 : 2 ^ d ≤ 2 ^ d * 2 ^ (d * K) := Nat.le_mul_of_pos_right _ (by omega)
    omega

theorem testBit_mults (n d k : Nat) (hd : 2 ≤ d) (hk : k ≤ n) :
    (mults n d).testBit k = decide (2 * d ≤ k ∧ d ∣ k) := by
  have hdpos : 0 < d := by omega
  have hsub : 0 < 2 ^ d - 1 := by
    have : 2 ≤ 2 ^ d := by
      have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show 1 ≤ d by omega)
      simpa using this
    omega
  have hG : Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul d (Nat.add (Nat.div n d) 1))) 1)
      (Nat.sub (Nat.shiftLeft 1 d) 1) = pk (2 ^ d) (fun _ => 1) (n / d + 1) := by
    show (1 <<< (d * (n / d + 1)) - 1) / (1 <<< d - 1) = _
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul, ← geom d (n / d + 1),
      Nat.mul_div_cancel_left _ hsub]
  have hone : ∀ u, u < n / d + 1 → (fun _ => 1) u < 2 ^ d := by
    intro u _
    exact Nat.one_lt_two_pow (by omega)
  show (Nat.shiftLeft _ (Nat.mul 2 d)).testBit k = _
  rw [hG]
  show (pk (2 ^ d) (fun _ => 1) (n / d + 1) <<< (2 * d)).testBit k = _
  rw [Nat.testBit_shiftLeft, testBit_pk d hdpos _ _ hone]
  have hlt : n < d * (n / d + 1) := by
    have := Nat.lt_div_mul_add (a := n) hdpos
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]; exact this
  by_cases h2 : 2 * d ≤ k
  · have hmod : (k - 2 * d) % d = k % d := by
      conv_rhs => rw [show k = (k - 2 * d) + d * 2 by omega]
      rw [Nat.add_mul_mod_self_left]
    have hbit : (Nat.testBit 1 ((k - 2 * d) % d)) = decide ((k - 2 * d) % d = 0) := by
      cases h : (k - 2 * d) % d with
      | zero => simp
      | succ r =>
        simp only [Nat.succ_ne_zero, decide_false]
        exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
    rw [hbit, hmod]
    simp [h2, show k - 2 * d < d * (n / d + 1) by omega, Nat.dvd_iff_mod_eq_zero]
  · simp [h2]

theorem land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

theorem testBit_all (n k : Nat) : (allOf n).testBit k = decide (k < n + 1) := by
  show (1 <<< (n + 1) - 1).testBit k = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]

/-- The sieve after `D` rounds. -/
theorem testBit_sieve (n k : Nat) (hk : k ≤ n) : ∀ D,
    (sieve n (allOf n) D).testBit k = true ↔
      (2 ≤ k ∧ ∀ d, 2 ≤ d → d < D + 2 → ¬ (2 * d ≤ k ∧ d ∣ k))
  | 0 => by
    show (Nat.land (allOf n) (Nat.xor (allOf n) 3)).testBit k = true ↔ _
    simp only [land_eq, xor_eq]
    rw [Nat.testBit_and, Nat.testBit_xor, testBit_all,
      show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.testBit_two_pow_sub_one]
    simp only [show k < n + 1 by omega, decide_true, Bool.true_and, Bool.true_xor,
      Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]
    constructor
    · intro h
      exact ⟨h, fun d hd hd2 _ => by omega⟩
    · exact fun h => h.1
  | D + 1 => by
    have ih := testBit_sieve n k hk D
    show (forceN (sieve n (allOf n) D) fun S =>
      Nat.land S (Nat.xor (allOf n) (Nat.land (mults n (Nat.add D 2)) (allOf n)))).testBit k
      = true ↔ _
    rw [forceN_eq]
    generalize sieve n (allOf n) D = S at ih ⊢
    simp only [land_eq, xor_eq]
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_and, testBit_all,
      show Nat.add D 2 = D + 2 from rfl, testBit_mults n (D + 2) k (by omega) hk]
    simp only [show k < n + 1 by omega, decide_true, Bool.and_true,
      Bool.true_xor, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    rw [ih]
    constructor
    · rintro ⟨⟨h2, hall⟩, hnot⟩
      refine ⟨h2, fun d hd hdD => ?_⟩
      by_cases hdd : d = D + 2
      · subst hdd; exact hnot
      · exact hall d hd (by omega)
    · rintro ⟨h2, hall⟩
      exact ⟨⟨h2, fun d hd hdD => hall d hd (by omega)⟩, hall (D + 2) (by omega) (by omega)⟩

theorem sieve_le (n : Nat) : ∀ D, sieve n (allOf n) D ≤ allOf n
  | 0 => by
    show Nat.land (allOf n) (Nat.xor (allOf n) 3) ≤ allOf n
    rw [land_eq]; exact Nat.and_le_left
  | D + 1 => by
    have ih := sieve_le n D
    show forceN (sieve n (allOf n) D) (fun S =>
      Nat.land S (Nat.xor (allOf n) (Nat.land (mults n (Nat.add D 2)) (allOf n)))) ≤ _
    rw [forceN_eq, land_eq]
    exact Nat.le_trans Nat.and_le_left ih

theorem bound_sq (n : Nat) : n < bound n * bound n := by
  have h := Nat.lt_log2_self (n := n)
  show n < (1 <<< (Nat.log2 n / 2 + 1)) * (1 <<< (Nat.log2 n / 2 + 1))
  rw [Nat.shiftLeft_eq, Nat.one_mul, ← Nat.pow_add]
  have : 2 ^ (Nat.log2 n + 1) ≤ 2 ^ (Nat.log2 n / 2 + 1 + (Nat.log2 n / 2 + 1)) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- Surviving the sieve is being prime. -/
theorem survive_iff_prime (n k : Nat) (hk : k ≤ n) :
    (2 ≤ k ∧ ∀ d, 2 ≤ d → d < bound n + 2 → ¬ (2 * d ≤ k ∧ d ∣ k)) ↔ Nat.Prime k := by
  constructor
  · rintro ⟨h2, hall⟩
    by_contra hnp
    have hk1 : k ≠ 1 := by omega
    have hp := Nat.minFac_prime hk1
    have hsq := Nat.minFac_sq_le_self (by omega) hnp
    have hpd := Nat.minFac_dvd k
    have hp2 := hp.two_le
    have hlt : k.minFac < bound n := by
      have hb := bound_sq n
      rw [Nat.pow_two] at hsq
      exact Nat.mul_self_lt_mul_self_iff.mp (by omega)
    apply hall k.minFac hp2 (by omega)
    refine ⟨?_, hpd⟩
    have : 2 * k.minFac ≤ k.minFac * k.minFac := Nat.mul_le_mul_right _ hp2
    rw [Nat.pow_two] at hsq
    omega
  · intro hp
    refine ⟨hp.two_le, fun d hd _ ⟨h2d, hdvd⟩ => ?_⟩
    rcases hp.eq_one_or_self_of_dvd d hdvd with h | h <;> omega

theorem count_eq (S n : Nat) (hS : ∀ k, k ≤ n → (S.testBit k = true ↔ Nat.Prime k)) :
    ∀ m, m ≤ n + 1 → count S m = Nat.count Nat.Prime m
  | 0, _ => rfl
  | m + 1, hm => by
    show Nat.add (count S m) (Nat.land (Nat.shiftRight S m) 1) = _
    rw [Nat.count_succ, count_eq S n hS m (by omega),
      show ∀ a b : Nat, Nat.add a b = a + b from fun _ _ => rfl]
    congr 1
    rw [show ∀ a b : Nat, Nat.land a b = a &&& b from fun _ _ => rfl,
      show ∀ a b : Nat, Nat.shiftRight a b = a >>> b from fun _ _ => rfl,
      Nat.and_one_is_mod]
    have hb := hS m (by omega)
    have h := Nat.testBit_shiftRight (i := m) (j := 0) S
    rw [Nat.add_zero, Nat.testBit_zero] at h
    have h2 := Nat.mod_two_eq_zero_or_one (S >>> m)
    by_cases hp : Nat.Prime m
    · have : S.testBit m = true := hb.mpr hp
      rw [this] at h
      simp only [decide_eq_true_eq] at h
      simp [hp, h]
    · have : S.testBit m = false := by
        cases hbit : S.testBit m
        · rfl
        · exact absurd (hb.mp hbit) hp
      rw [this] at h
      simp only [decide_eq_false_iff_not] at h
      simp only [hp, if_false]
      omega

/-! ## Counting set bits -/

theorem bitval (S k : Nat) :
    Nat.land (Nat.shiftRight S k) 1 = if S.testBit k then 1 else 0 := by
  rw [land_eq, show Nat.shiftRight S k = S >>> k from rfl, Nat.and_one_is_mod]
  have h := Nat.testBit_shiftRight (i := k) (j := 0) S
  rw [Nat.add_zero, Nat.testBit_zero] at h
  have h2 := Nat.mod_two_eq_zero_or_one (S >>> k)
  cases hb : S.testBit k
  · rw [hb] at h; simp only [decide_eq_false_iff_not] at h; simp; omega
  · rw [hb] at h; simp only [decide_eq_true_eq] at h; simp [h]

theorem count_succ' (S m : Nat) :
    count S (m + 1) = count S m + (if S.testBit m then 1 else 0) := by
  show Nat.add (count S m) (Nat.land (Nat.shiftRight S m) 1) = _
  rw [bitval]; rfl

theorem count_le (S : Nat) : ∀ m, count S m ≤ m
  | 0 => Nat.le_refl 0
  | m + 1 => by
    rw [count_succ']
    have := count_le S m
    split <;> omega

theorem count_zero_val : ∀ m, count 0 m = 0
  | 0 => rfl
  | m + 1 => by rw [count_succ', count_zero_val m]; simp

/-- Two numbers whose bits agree except at `t < m`, where only `x` has a one. -/
theorem count_clear (x y t : Nat) (hx : x.testBit t = true) (hy : y.testBit t = false)
    (hxy : ∀ i, i ≠ t → y.testBit i = x.testBit i) : ∀ m, t < m → count x m = count y m + 1
  | 0, h => absurd h (by omega)
  | m + 1, h => by
    rw [count_succ', count_succ']
    by_cases hmt : m = t
    · subst hmt
      rw [hx, hy]
      have : count x m = count y m := by
        clear h hx hy
        induction m using Nat.strong_induction_on with
        | _ m ih0 => exact (by
          -- counts agree below `m`, where all bits agree
          have key : ∀ j, j ≤ m → count x j = count y j := by
            intro j
            induction j with
            | zero => intro _; rfl
            | succ j ihj =>
              intro hj
              rw [count_succ', count_succ', ihj (by omega), hxy j (by omega)]
          exact key m (Nat.le_refl m))
      simp [this]
    · rw [count_clear x y t hx hy hxy m (by omega), hxy m hmt]
      omega

/-- `x &&& (x - 1)` is `x` with its lowest set bit cleared. -/
theorem lowbit (x : Nat) (hx : x ≠ 0) : ∃ t, x.testBit t = true ∧
    (x &&& (x - 1)).testBit t = false ∧ ∀ i, i ≠ t → (x &&& (x - 1)).testBit i = x.testBit i := by
  obtain ⟨t, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hx
  obtain ⟨v, rfl⟩ := hu
  have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
  have hsub : 2 ^ t * (2 * v + 1) - 1 = 2 ^ t * (2 * v) + (2 ^ t - 1) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  have hx' : 2 ^ t * (2 * v + 1) = 2 ^ t * (2 * v + 1) + 0 := rfl
  have tx : ∀ i, (2 ^ t * (2 * v + 1)).testBit i =
      if i < t then false else (2 * v + 1).testBit (i - t) := by
    intro i
    rw [hx', Nat.testBit_two_pow_mul_add _ hpos]
    simp
  have ty : ∀ i, (2 ^ t * (2 * v + 1) - 1).testBit i =
      if i < t then true else (2 * v).testBit (i - t) := by
    intro i
    rw [hsub, Nat.testBit_two_pow_mul_add _ (by omega)]
    split
    · rw [Nat.testBit_two_pow_sub_one]; simp [*]
    · rfl
  have odd0 : (2 * v + 1).testBit 0 = true := by
    rw [Nat.testBit_zero]; simp
  have even0 : (2 * v).testBit 0 = false := by
    rw [Nat.testBit_zero]; simp
  have oddS : ∀ j, (2 * v + 1).testBit (j + 1) = (2 * v).testBit (j + 1) := by
    intro j
    rw [Nat.testBit_succ, Nat.testBit_succ]
    congr 1; omega
  refine ⟨t, ?_, ?_, ?_⟩
  · rw [tx]; simp [odd0]
  · rw [Nat.testBit_and, tx, ty]; simp [odd0, even0]
  · intro i hi
    rw [Nat.testBit_and, tx, ty]
    split
    · simp
    · have : i - t = (i - t - 1) + 1 := by omega
      rw [this, oddS]; simp

theorem pop_eq (m : Nat) : ∀ fuel x, x < 2 ^ m → count x m ≤ fuel → pop fuel x = count x m
  | 0, x, _, h => by
    show 0 = _
    omega
  | fuel + 1, x, hx, h => by
    show cond (Nat.beq x 0) 0 (Nat.add (pop fuel (Nat.land x (Nat.sub x 1))) 1) = _
    by_cases hx0 : x = 0
    · subst hx0; simp [count_zero_val]
    · have hb : Nat.beq x 0 = false := by
        rw [Bool.eq_false_iff]; intro hb; rw [Nat.beq_eq] at hb; exact hx0 hb
      rw [hb, cond_false, land_eq, show Nat.sub x 1 = x - 1 from rfl]
      obtain ⟨t, h1, h2, h3⟩ := lowbit x hx0
      have ht : t < m := by
        by_contra hge
        rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega)
          (by omega)))] at h1
        exact absurd h1 (by simp)
      have hc := count_clear x (x &&& (x - 1)) t h1 h2 h3 m ht
      have hy : x &&& (x - 1) < 2 ^ m := Nat.lt_of_le_of_lt Nat.and_le_left hx
      rw [pop_eq m fuel (x &&& (x - 1)) hy (by omega)]
      show count (x &&& (x - 1)) m + 1 = _
      omega

theorem impl_correct : ∀ n, impl n = primeCountSpec n := by
  intro n
  unfold impl
  rw [forceN_eq, forceN_eq]
  rw [show Nat.add n 1 = n + 1 from rfl]
  have hS : sieve n (allOf n) (bound n) < 2 ^ (n + 1) := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    cases hb : (sieve n (allOf n) (bound n)).testBit i
    · rfl
    · exfalso
      -- every set bit of the sieve is below `n + 1`
      have : (sieve n (allOf n) (bound n)).testBit i = true → i ≤ n := by
        intro _
        by_contra hin
        have hle : sieve n (allOf n) (bound n) ≤ allOf n := sieve_le n (bound n)
        have hlt : allOf n < 2 ^ (n + 1) := by
          show 1 <<< (n + 1) - 1 < _
          rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.sub_lt (Nat.two_pow_pos _) (by omega)
        rw [Nat.testBit_lt_two_pow (Nat.lt_of_le_of_lt hle (Nat.lt_of_lt_of_le hlt
          (Nat.pow_le_pow_right (by omega) (by omega))))] at hb
        exact absurd hb (by simp)
      have := this hb
      omega
  rw [pop_eq (n + 1) (n + 1) _ hS (count_le _ _)]
  rw [count_eq _ n (fun k hk => (testBit_sieve n k hk (bound n)).trans (survive_iff_prime n k hk))
    (n + 1) (Nat.le_refl _)]
  simp [primeCountSpec, Nat.primeCounting, Nat.primeCounting']

end Submission
