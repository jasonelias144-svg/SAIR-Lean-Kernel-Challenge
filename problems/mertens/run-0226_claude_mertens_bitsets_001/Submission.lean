import Spec

/-!
# The Mertens function with bitsets

Everything is a bitset over `0 … n` held in one natural number:

* `S`: the primes `≤ n` (a bit sieve, as in the prime-counting entry);
* `Q`: the squarefree numbers in `1 … n` (clear the multiples of `d²` for
  `2 ≤ d ≤ D + 1`, where `D * D > n`);
* `P`: bit `k` is the parity of the number of distinct primes dividing `k`.
  Walk the set bits of `S` lowest first (`S &&& (S - 1)` clears the lowest bit,
  and `L = S ^^^ (S &&& (S - 1)) = 2^p`), XOR-ing in the multiples of `p`,
  `(L * (R - 1) / (L - 1)) &&& all` with `R = L^(2^j)` the first repeated square of
  `L` above `2^(n+1) - 1` (so no `log₂` is needed).

For `1 ≤ k ≤ n`, `μ(k)` is `1` if `k` is squarefree with an even number of prime
factors, `-1` if squarefree with an odd number, and `0` otherwise, so
`M(n) = #(Q ∧ ¬P) - #(Q ∧ P)`. Each count clears one set bit per step.

Loops are `Nat.rec`, word operations call `Nat.*` directly, and the bitsets are
forced to literals once.
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

def forceI (x : Nat) (k : Nat → Int) : Int :=
  Nat.casesOn (motive := fun _ => Int) x (k 0) (fun m => k (Nat.succ m))

/-- Bits `s, 2s, …, K s` with `K = n / s + 1`. -/
def multsFrom1 (n s : Nat) : Nat :=
  Nat.shiftLeft
    (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul s (Nat.add (Nat.div n s) 1))) 1)
      (Nat.sub (Nat.shiftLeft 1 s) 1)) s

/-- Squarefree numbers in `1 … n`: clear bit `0`, then multiples of `d²`, `2 ≤ d ≤ D + 1`. -/
def sqfree (n all D : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.land all (Nat.xor all 1))
    (fun j Q => forceN Q fun Q => Nat.land Q (Nat.xor all
      (Nat.land (multsFrom1 n (Nat.mul (Nat.add j 2) (Nat.add j 2))) all))) D

/-- Square `X` until it exceeds `all` (at most `fuel` times). -/
def sqUp (all fuel X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun X => X)
    (fun _ ih X => cond (Nat.ble X all) (ih (Nat.mul X X)) X) fuel X

/-- Multiples `p, 2p, …` of `p` up to `n`, given `L = 2^p`. -/
def patt (n all L : Nat) : Nat :=
  Nat.land (Nat.mul L (Nat.div (Nat.sub (sqUp all (Nat.add n 1) L) 1) (Nat.sub L 1))) all

/-- XOR the multiples of every set bit of `S` into `P`, lowest bit first. -/
def walk (n all fuel S P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ P => P)
    (fun _ ih S P => cond (Nat.beq S 0) P
      ((fun S' => (fun L => ih S' (Nat.xor P (patt n all L))) (Nat.xor S S'))
        (Nat.land S (Nat.sub S 1))))
    fuel S P

def impl (n : Nat) : Int :=
  forceI (allOf n) fun all =>
  forceI (sqfree n all (bound n)) fun Q =>
  forceI (sieve n all (bound n)) fun S =>
  forceI (walk n all (Nat.add n 1) S 0) fun P =>
  Int.sub (Int.ofNat (pop (Nat.add n 1) (Nat.land Q (Nat.xor all P))))
    (Int.ofNat (pop (Nat.add n 1) (Nat.land Q P)))

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


/-! ## Multiples of `s` from `s` on -/

theorem testBit_multsFrom1 (n s k : Nat) (hs : 1 ≤ s) (hk : k ≤ n) :
    (multsFrom1 n s).testBit k = decide (s ≤ k ∧ s ∣ k) := by
  have hsub : 0 < 2 ^ s - 1 := by
    have : 2 ≤ 2 ^ s := by
      have := Nat.pow_le_pow_right (show 0 < 2 by omega) hs
      simpa using this
    omega
  have hG : Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul s (Nat.add (Nat.div n s) 1))) 1)
      (Nat.sub (Nat.shiftLeft 1 s) 1) = pk (2 ^ s) (fun _ => 1) (n / s + 1) := by
    show (1 <<< (s * (n / s + 1)) - 1) / (1 <<< s - 1) = _
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul, ← geom s (n / s + 1),
      Nat.mul_div_cancel_left _ hsub]
  have hone : ∀ u, u < n / s + 1 → (fun _ => 1) u < 2 ^ s := by
    intro u _
    exact Nat.one_lt_two_pow (by omega)
  show (Nat.shiftLeft _ s).testBit k = _
  rw [hG]
  show (pk (2 ^ s) (fun _ => 1) (n / s + 1) <<< s).testBit k = _
  rw [Nat.testBit_shiftLeft, testBit_pk s (by omega) _ _ hone]
  have hlt : n < s * (n / s + 1) := by
    have := Nat.lt_div_mul_add (a := n) (show 0 < s by omega)
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]; exact this
  by_cases h2 : s ≤ k
  · have hmod : (k - s) % s = k % s := by
      conv_rhs => rw [show k = (k - s) + s * 1 by omega]
      rw [Nat.add_mul_mod_self_left]
    have hbit : (Nat.testBit 1 ((k - s) % s)) = decide ((k - s) % s = 0) := by
      cases h : (k - s) % s with
      | zero => simp
      | succ r =>
        simp only [Nat.succ_ne_zero, decide_false]
        exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
    rw [hbit, hmod]
    simp [h2, show k - s < s * (n / s + 1) by omega, Nat.dvd_iff_mod_eq_zero]
  · simp [h2]

/-! ## Squarefree bitset -/

theorem testBit_sqfree (n k : Nat) (hk : k ≤ n) : ∀ D,
    (sqfree n (allOf n) D).testBit k = true ↔
      (1 ≤ k ∧ ∀ d, 2 ≤ d → d < D + 2 → ¬ (d * d ∣ k))
  | 0 => by
    show (Nat.land (allOf n) (Nat.xor (allOf n) 1)).testBit k = true ↔ _
    simp only [land_eq, xor_eq]
    have h1 : Nat.testBit 1 k = decide (k = 0) := by
      cases k with
      | zero => simp
      | succ j =>
        simp only [Nat.succ_ne_zero, decide_false]
        exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
    rw [Nat.testBit_and, Nat.testBit_xor, testBit_all, h1]
    simp only [show k < n + 1 by omega, decide_true, Bool.true_and, Bool.true_xor,
      Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · intro h
      exact ⟨by omega, fun d hd hd2 _ => by omega⟩
    · intro h; omega
  | D + 1 => by
    have ih := testBit_sqfree n k hk D
    show (forceN (sqfree n (allOf n) D) fun Q => Nat.land Q (Nat.xor (allOf n)
      (Nat.land (multsFrom1 n (Nat.mul (Nat.add D 2) (Nat.add D 2))) (allOf n)))).testBit k
      = true ↔ _
    rw [forceN_eq]
    generalize sqfree n (allOf n) D = Q at ih ⊢
    simp only [land_eq, xor_eq]
    have hsq : 1 ≤ (D + 2) * (D + 2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_and, testBit_all,
      show Nat.mul (Nat.add D 2) (Nat.add D 2) = (D + 2) * (D + 2) from rfl,
      testBit_multsFrom1 n _ k hsq hk]
    simp only [show k < n + 1 by omega, decide_true, Bool.and_true,
      Bool.true_xor, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    rw [ih]
    constructor
    · rintro ⟨⟨h1, hall⟩, hnot⟩
      refine ⟨h1, fun d hd hdD hdk => ?_⟩
      by_cases hdd : d = D + 2
      · subst hdd; exact hnot ⟨Nat.le_of_dvd (by omega) hdk, hdk⟩
      · exact hall d hd (by omega) hdk
    · rintro ⟨h1, hall⟩
      exact ⟨⟨h1, fun d hd hdD => hall d hd (by omega)⟩,
        fun h => hall (D + 2) (by omega) (by omega) h.2⟩

theorem sqfree_iff (n k : Nat) (hk : k ≤ n) :
    (1 ≤ k ∧ ∀ d, 2 ≤ d → d < bound n + 2 → ¬ (d * d ∣ k)) ↔ (1 ≤ k ∧ Squarefree k) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  constructor
  · rintro ⟨h1, hall⟩
    refine ⟨h1, fun p hp hpk => ?_⟩
    have hle := Nat.le_of_dvd (by omega) hpk
    have hb := bound_sq n
    have : p < bound n := Nat.mul_self_lt_mul_self_iff.mp (by omega)
    exact hall p hp.two_le (by omega) hpk
  · rintro ⟨h1, hall⟩
    refine ⟨h1, fun d hd _ hdk => ?_⟩
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show d ≠ 1 by omega)
    exact hall p hp (Nat.dvd_trans (Nat.mul_dvd_mul hpd hpd) hdk)

/-! ## The multiples pattern -/

theorem sqUp_spec (all : Nat) : ∀ f X, 2 ≤ X → all < X ^ (2 ^ f) →
    ∃ e, 1 ≤ e ∧ sqUp all f X = X ^ e ∧ all < X ^ e
  | 0, X, _, h => ⟨1, le_refl _, by simp [sqUp], by simpa using h⟩
  | f + 1, X, hX, h => by
    show ∃ e, 1 ≤ e ∧ cond (Nat.ble X all) (sqUp all f (Nat.mul X X)) X = X ^ e ∧ all < X ^ e
    by_cases hle : X ≤ all
    · rw [show Nat.ble X all = true from Nat.ble_eq.mpr hle, cond_true]
      have h2 : all < (X * X) ^ (2 ^ f) := by
        rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ']; exact h
      obtain ⟨e, he, hq, hlt⟩ := sqUp_spec all f (X * X) (by nlinarith) h2
      refine ⟨2 * e, by omega, ?_, ?_⟩
      · rw [show Nat.mul X X = X * X from rfl, hq, ← Nat.pow_two, ← Nat.pow_mul]
      · rw [Nat.pow_mul, Nat.pow_two]; exact hlt
    · rw [show Nat.ble X all = false by
        rw [Bool.eq_false_iff]; intro hb; exact hle (Nat.ble_eq.mp hb), cond_false]
      exact ⟨1, le_refl _, by simp, by simpa using (by omega : all < X)⟩

theorem testBit_patt (n t k : Nat) (ht : 1 ≤ t) (hk1 : 1 ≤ k) (hk : k ≤ n) :
    (patt n (allOf n) (2 ^ t)).testBit k = decide (t ∣ k) := by
  have hall : allOf n = 2 ^ (n + 1) - 1 := by
    show 1 <<< (n + 1) - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have h2t : 2 ≤ 2 ^ t := by
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) ht
    simpa using this
  have hbig : allOf n < (2 ^ t) ^ (2 ^ (n + 1)) := by
    rw [hall]
    have h1 : 2 ^ (n + 1) ≤ (2 ^ t) ^ (2 ^ (n + 1)) := by
      calc 2 ^ (n + 1) ≤ 2 ^ (2 ^ (n + 1)) :=
            Nat.pow_le_pow_right (by omega) (Nat.lt_two_pow_self).le
        _ ≤ (2 ^ t) ^ (2 ^ (n + 1)) := Nat.pow_le_pow_left h2t _
    have : 0 < 2 ^ (n + 1) := Nat.two_pow_pos _
    omega
  obtain ⟨e, he, hR, hlt⟩ := sqUp_spec (allOf n) (n + 1) (2 ^ t) h2t hbig
  have hte : n + 1 ≤ t * e := by
    rw [hall, ← Nat.pow_mul] at hlt
    have : 2 ^ (n + 1) ≤ 2 ^ (t * e) := by omega
    exact (Nat.pow_le_pow_iff_right (by omega)).mp this
  have hsub : 0 < 2 ^ t - 1 := by omega
  have hG : Nat.div (Nat.sub (sqUp (allOf n) (Nat.add n 1) (2 ^ t)) 1) (Nat.sub (2 ^ t) 1) =
      pk (2 ^ t) (fun _ => 1) e := by
    show (sqUp (allOf n) (n + 1) (2 ^ t) - 1) / (2 ^ t - 1) = _
    rw [hR, ← Nat.pow_mul, ← geom t e, Nat.mul_div_cancel_left _ hsub]
  have hone : ∀ u, u < e → (fun _ => 1) u < 2 ^ t := by
    intro u _
    exact Nat.one_lt_two_pow (by omega)
  show (Nat.land (Nat.mul (2 ^ t) (Nat.div _ _)) (allOf n)).testBit k = _
  rw [hG, land_eq, Nat.testBit_and, testBit_all,
    show Nat.mul (2 ^ t) (pk (2 ^ t) (fun _ => 1) e) = pk (2 ^ t) (fun _ => 1) e <<< t by
      rw [Nat.shiftLeft_eq, Nat.mul_comm]; rfl,
    Nat.testBit_shiftLeft, testBit_pk t (by omega) _ _ hone]
  simp only [show k < n + 1 by omega, decide_true, Bool.and_true]
  by_cases h2 : t ≤ k
  · have hmod : (k - t) % t = k % t := by
      conv_rhs => rw [show k = (k - t) + t * 1 by omega]
      rw [Nat.add_mul_mod_self_left]
    have hbit : (Nat.testBit 1 ((k - t) % t)) = decide ((k - t) % t = 0) := by
      cases h : (k - t) % t with
      | zero => simp
      | succ r =>
        simp only [Nat.succ_ne_zero, decide_false]
        exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
    rw [hbit, hmod]
    simp [h2, show k - t < t * e by omega, Nat.dvd_iff_mod_eq_zero]
  · have : ¬ t ∣ k := fun h => h2 (Nat.le_of_dvd (by omega) h)
    simp [h2, this]

/-! ## The parity walk -/

/-- Number of set bits `p < m` of `S` that divide `k`. -/
def cdiv (S k : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => cdiv S k m + if S.testBit m = true ∧ m ∣ k then 1 else 0

theorem cdiv_le_count (S k : Nat) : ∀ m, cdiv S k m ≤ count S m
  | 0 => le_refl _
  | m + 1 => by
    rw [count_succ']
    simp only [cdiv]
    have := cdiv_le_count S k m
    split <;> split <;> first | omega | simp_all

theorem cdiv_clear (x y t k : Nat) (hx : x.testBit t = true) (hy : y.testBit t = false)
    (hxy : ∀ i, i ≠ t → y.testBit i = x.testBit i) : ∀ m, t < m →
    cdiv x k m = cdiv y k m + (if t ∣ k then 1 else 0)
  | 0, h => absurd h (by omega)
  | m + 1, h => by
    simp only [cdiv]
    by_cases hmt : m = t
    · subst hmt
      have : cdiv x k m = cdiv y k m := by
        have key : ∀ j, j ≤ m → cdiv x k j = cdiv y k j := by
          intro j
          induction j with
          | zero => intro _; rfl
          | succ j ihj =>
            intro hj
            simp only [cdiv]
            rw [ihj (by omega), hxy j (by omega)]
        exact key m (le_refl m)
      rw [this, hx, hy]
      by_cases hd : m ∣ k <;> simp [hd]
    · rw [cdiv_clear x y t k hx hy hxy m (by omega), hxy m hmt]
      omega

/-- Odd as a boolean. -/
def odd (a : Nat) : Bool := decide (a % 2 = 1)

theorem odd_add_ite (a : Nat) (c : Prop) [Decidable c] :
    odd (a + if c then 1 else 0) = (odd a ^^ decide c) := by
  unfold odd
  by_cases hc : c
  · simp only [hc, if_true, decide_true]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h, Nat.add_mod]
  · simp [hc]

theorem walk_spec (n : Nat) : ∀ f S P, count S (n + 1) ≤ f → S < 2 ^ (n + 1) →
    (∀ i, S.testBit i = true → 1 ≤ i) → ∀ k, 1 ≤ k → k ≤ n →
    (walk n (allOf n) f S P).testBit k = (P.testBit k ^^ odd (cdiv S k (n + 1)))
  | 0, S, P, hc, hS, _, k, _, _ => by
    have h0 : cdiv S k (n + 1) = 0 := by
      have := cdiv_le_count S k (n + 1); omega
    show P.testBit k = _
    rw [h0]; simp [odd]
  | f + 1, S, P, hc, hS, hb, k, hk1, hk => by
    show (cond (Nat.beq S 0) P ((fun S' => (fun L => walk n (allOf n) f S'
      (Nat.xor P (patt n (allOf n) L))) (Nat.xor S S')) (Nat.land S (Nat.sub S 1)))).testBit k = _
    by_cases hS0 : S = 0
    · subst hS0
      have : ∀ m, cdiv 0 k m = 0 := by
        intro m; induction m with
        | zero => rfl
        | succ m ih => simp [cdiv, ih]
      simp [this, odd]
    · have hbeq : Nat.beq S 0 = false := by
        rw [Bool.eq_false_iff]; intro h; rw [Nat.beq_eq] at h; exact hS0 h
      rw [hbeq, cond_false]
      simp only [land_eq, xor_eq, show Nat.sub S 1 = S - 1 from rfl]
      obtain ⟨t, h1, h2, h3⟩ := lowbit S hS0
      have ht : t < n + 1 := by
        by_contra hge
        rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hS (Nat.pow_le_pow_right (by omega)
          (by omega)))] at h1
        exact absurd h1 (by simp)
      have ht1 : 1 ≤ t := hb t h1
      have hL : S ^^^ (S &&& (S - 1)) = 2 ^ t := by
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        by_cases hi : i = t
        · subst hi; rw [h1, h2]; simp
        · rw [h3 i hi]; simp [Ne.symm hi]
      rw [hL]
      have hcnt := count_clear S (S &&& (S - 1)) t h1 h2 h3 (n + 1) ht
      have hy : S &&& (S - 1) < 2 ^ (n + 1) := Nat.lt_of_le_of_lt Nat.and_le_left hS
      rw [walk_spec n f (S &&& (S - 1)) _ (by omega) hy (fun i hi => by
          by_cases hit : i = t
          · subst hit; rw [h2] at hi; exact absurd hi (by simp)
          · rw [h3 i hit] at hi; exact hb i hi) k hk1 hk,
        Nat.testBit_xor, testBit_patt n t k ht1 hk1 hk,
        cdiv_clear S (S &&& (S - 1)) t k h1 h2 h3 (n + 1) ht, odd_add_ite]
      cases P.testBit k <;> cases odd (cdiv (S &&& (S - 1)) k (n + 1)) <;> cases decide (t ∣ k) <;> rfl

/-! ## Connecting to Mathlib -/

theorem cdiv_sum (S k : Nat) : ∀ m,
    cdiv S k m = ∑ p ∈ Finset.range m, if S.testBit p = true ∧ p ∣ k then 1 else 0
  | 0 => by simp [cdiv]
  | m + 1 => by rw [Finset.sum_range_succ, ← cdiv_sum S k m]; rfl

theorem cdiv_primes (n S k : Nat) (hS : ∀ p, p ≤ n → (S.testBit p = true ↔ Nat.Prime p))
    (hk1 : 1 ≤ k) (hk : k ≤ n) : cdiv S k (n + 1) = k.primeFactorsList.dedup.length := by
  rw [cdiv_sum, ← Finset.card_filter, ← List.card_toFinset]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
  rw [Nat.mem_primeFactorsList (by omega)]
  constructor
  · rintro ⟨hp, hb, hd⟩
    exact ⟨(hS p (by omega)).mp hb, hd⟩
  · rintro ⟨hp, hd⟩
    have := Nat.le_of_dvd (by omega) hd
    exact ⟨by omega, (hS p (by omega)).mpr hp, hd⟩

theorem pop_bits (n x : Nat) (hx : x < 2 ^ (n + 1)) :
    pop (n + 1) x = count x (n + 1) :=
  pop_eq (n + 1) (n + 1) x hx (count_le _ _)

theorem sqfree_le (n : Nat) : ∀ D, sqfree n (allOf n) D ≤ allOf n
  | 0 => by
    show Nat.land (allOf n) (Nat.xor (allOf n) 1) ≤ allOf n
    rw [land_eq]; exact Nat.and_le_left
  | D + 1 => by
    have ih := sqfree_le n D
    show forceN (sqfree n (allOf n) D) (fun Q => Nat.land Q (Nat.xor (allOf n)
      (Nat.land (multsFrom1 n (Nat.mul (Nat.add D 2) (Nat.add D 2))) (allOf n)))) ≤ _
    rw [forceN_eq, land_eq]
    exact Nat.le_trans Nat.and_le_left ih

theorem allOf_lt (n : Nat) : allOf n < 2 ^ (n + 1) := by
  show 1 <<< (n + 1) - 1 < _
  rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.sub_lt (Nat.two_pow_pos _) (by omega)

theorem high_bit (n x i : Nat) (hx : x ≤ allOf n) (hi : n < i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hx (allOf_lt n))
    (Nat.pow_le_pow_right (by omega) (by omega)))

theorem forceI_eq (x : Nat) (k : Nat → Int) : forceI x k = k x := by
  cases x <;> rfl

theorem count_diff (A Q P : Nat) (μ : Nat → Int) : ∀ m,
    (∀ k, k < m → μ k = (if (Q &&& (A ^^^ P)).testBit k then 1 else 0) -
      (if (Q &&& P).testBit k then 1 else 0)) →
    ((count (Q &&& (A ^^^ P)) m : Int) - (count (Q &&& P) m : Int)) =
      ∑ k ∈ Finset.range m, μ k
  | 0, _ => by simp [count]
  | m + 1, h => by
    rw [count_succ', count_succ', Finset.sum_range_succ, ← count_diff A Q P μ m
      (fun k hk => h k (by omega)), h m (by omega)]
    push_cast
    ring

/-- `μ k` in terms of the bitsets, for `k ≤ n`. -/
theorem moebius_bits (n k : Nat) (hk : k ≤ n) :
    (ArithmeticFunction.moebius k : Int) =
      (if (sqfree n (allOf n) (bound n) &&& (allOf n ^^^
          walk n (allOf n) (n + 1) (sieve n (allOf n) (bound n)) 0)).testBit k then 1 else 0) -
      (if (sqfree n (allOf n) (bound n) &&&
          walk n (allOf n) (n + 1) (sieve n (allOf n) (bound n)) 0).testBit k then 1 else 0) := by
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_and, testBit_all]
  simp only [show k < n + 1 by omega, decide_true, Bool.true_xor]
  have hQ := testBit_sqfree n k hk (bound n)
  rw [sqfree_iff n k hk] at hQ
  by_cases hk0 : k = 0
  · subst hk0
    have : (sqfree n (allOf n) (bound n)).testBit 0 = false := by
      cases h : (sqfree n (allOf n) (bound n)).testBit 0
      · rfl
      · exact absurd (hQ.mp h).1 (by omega)
    simp [this]
  have hSprime : ∀ p, p ≤ n → ((sieve n (allOf n) (bound n)).testBit p = true ↔ Nat.Prime p) :=
    fun p hp => (testBit_sieve n p hp (bound n)).trans (survive_iff_prime n p hp)
  have hSlt : sieve n (allOf n) (bound n) < 2 ^ (n + 1) :=
    Nat.lt_of_le_of_lt (sieve_le n (bound n)) (allOf_lt n)
  have hPk := walk_spec n (n + 1) (sieve n (allOf n) (bound n)) 0 (count_le _ _) hSlt
    (fun i hi => by
      by_cases hin : i ≤ n
      · exact ((hSprime i hin).mp hi).one_lt.le
      · rw [high_bit n _ i (sieve_le n (bound n)) (by omega)] at hi; exact absurd hi (by simp))
    k (by omega) hk
  rw [cdiv_primes n _ k hSprime (by omega) hk] at hPk
  simp only [Nat.zero_testBit, Bool.false_xor] at hPk
  rw [hPk]
  by_cases hsq : Squarefree k
  · have hQk : (sqfree n (allOf n) (bound n)).testBit k = true := hQ.mpr ⟨by omega, hsq⟩
    rw [hQk, ArithmeticFunction.moebius_apply_of_squarefree hsq]
    have hcard : ArithmeticFunction.cardFactors k = k.primeFactorsList.dedup.length := by
      rw [← ArithmeticFunction.cardDistinctFactors_apply,
        (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hk0).mpr hsq]
    rw [hcard]
    unfold odd
    rcases Nat.even_or_odd k.primeFactorsList.dedup.length with he | ho
    · rw [he.neg_one_pow, show k.primeFactorsList.dedup.length % 2 = 0 from Nat.even_iff.mp he]
      simp
    · rw [ho.neg_one_pow, show k.primeFactorsList.dedup.length % 2 = 1 from Nat.odd_iff.mp ho]
      simp
  · have hQk : (sqfree n (allOf n) (bound n)).testBit k = false := by
      cases h : (sqfree n (allOf n) (bound n)).testBit k
      · rfl
      · exact absurd (hQ.mp h).2 hsq
    rw [hQk, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp

theorem impl_correct : ∀ n, impl n = mertensSpec n := by
  intro n
  unfold impl
  rw [forceI_eq, forceI_eq, forceI_eq, forceI_eq]
  simp only [land_eq, xor_eq, show Nat.add n 1 = n + 1 from rfl]
  have hQlt : sqfree n (allOf n) (bound n) < 2 ^ (n + 1) :=
    Nat.lt_of_le_of_lt (sqfree_le n (bound n)) (allOf_lt n)
  rw [pop_bits n _ (Nat.lt_of_le_of_lt Nat.and_le_left hQlt),
    pop_bits n _ (Nat.lt_of_le_of_lt Nat.and_le_left hQlt)]
  show ((count _ (n + 1) : Int) - (count _ (n + 1) : Int)) = _
  rw [count_diff _ _ _ (fun k => (ArithmeticFunction.moebius k : Int)) (n + 1)
    (fun k hk => moebius_bits n k (by omega))]
  rfl

end Submission
