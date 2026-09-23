import Spec

/-!
# The Mertens function with packed fields and a handful of primes

Every number `k ≤ n` owns a field of `w` bits (`n < 2 ^ (w - 1)`), and three packed
vectors are kept while the primes `p` with `p * p ≤ n` are processed:

* `F`: field `k` is the product of the processed primes dividing `k`;
* `P`: field `k` is the parity of how many processed primes divide `k`;
* `Q`: field `k` is `1` while no processed `p²` divides `k`.

Processing `p` is a few big-number operations on the pattern `M` of the fields
`p, 2p, …` (one closed form `(2^{wpq} - 1) / (2^{wp} - 1) << wp`):
`F += (p - 1) * (F & M·(2^w - 1))`, `P ^= M`, and `Q` loses the multiples of `p²`.
Candidates are `2, 3, 6j ± 1`; a candidate is prime exactly when its own `F` field
is still `1`, which also skips composites such as `25`.

Afterwards a squarefree `k ≤ n` has at most one prime factor `≥ √n`, and has one
exactly when `F_k < k`; that comparison is one subtraction against the packed
identity vector plus a guard bit. So `μ(k)` is `Q_k · (-1)^(P_k + [F_k < k])`, and
since `2^w ≡ 1 (mod 2^w - 1)` each of the two counts `#{μ = 1}` and `#{μ = -1}` is a
single `mod`.

Kernel-cost notes: loops are `Nat.rec`, branches `Bool.rec`, word operations call
`Nat.*` directly, and `Nat.log2` is only used for `n ≥ 512`.
-/

namespace Submission

/-! ## Implementation -/

/-- Process `d` if it is prime (its product field is still `1`), then continue with `k`. -/
def proc (w n m d F P Q : Nat) (k : Nat → Nat → Nat → Int) : Int :=
  Bool.rec (motive := fun _ => Int) (k F P Q)
    (k (Nat.add F (Nat.mul (Nat.sub d 1) (Nat.land F (Nat.mul (Nat.shiftLeft (Nat.div
          (Nat.sub (Nat.shiftLeft 1 (Nat.mul (Nat.mul w d) (Nat.div n d))) 1)
          (Nat.sub (Nat.shiftLeft 1 (Nat.mul w d)) 1)) (Nat.mul w d)) m))))
      (Nat.xor P (Nat.shiftLeft (Nat.div
          (Nat.sub (Nat.shiftLeft 1 (Nat.mul (Nat.mul w d) (Nat.div n d))) 1)
          (Nat.sub (Nat.shiftLeft 1 (Nat.mul w d)) 1)) (Nat.mul w d)))
      (Nat.xor Q (Nat.land Q (Nat.shiftLeft (Nat.div
          (Nat.sub (Nat.shiftLeft 1 (Nat.mul (Nat.mul w (Nat.mul d d)) (Nat.div n (Nat.mul d d)))) 1)
          (Nat.sub (Nat.shiftLeft 1 (Nat.mul w (Nat.mul d d))) 1)) (Nat.mul w (Nat.mul d d))))))
    (Nat.beq (Nat.land (Nat.shiftRight F (Nat.mul w d)) m) 1)

/-- `M(n)` from the three vectors, once every prime `p` with `p * p ≤ n` is processed. -/
def fin (w n m A F P Q : Nat) : Int :=
  (fun QO => Int.subNatNat (Nat.mod (Nat.xor Q QO) m) (Nat.mod QO m))
  (Nat.land Q (Nat.xor P (Nat.land (Nat.shiftRight (Nat.add (Nat.sub
    (Nat.div (Nat.sub (Nat.add (Nat.mul n (Nat.shiftLeft 1 (Nat.mul w (Nat.add n 2))))
        (Nat.shiftLeft 1 w)) (Nat.mul (Nat.add n 1) (Nat.shiftLeft 1 (Nat.mul w (Nat.add n 1)))))
      (Nat.mul m m)) F)
    (Nat.mul A (Nat.sub (Nat.shiftLeft 1 (Nat.sub w 1)) 1))) (Nat.sub w 1)) A)))

/-- Process `d` and `d + 2` for `d = 5, 11, 17, …` until `n < d * d`. -/
def loop (w n m A fuel : Nat) : Nat → Nat → Nat → Nat → Int :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Int) (fun _ F P Q => fin w n m A F P Q)
    (fun _ ih d F P Q => Bool.rec (motive := fun _ => Int)
      (proc w n m d F P Q fun F P Q => proc w n m (Nat.add d 2) F P Q fun F P Q =>
        ih (Nat.add d 6) F P Q)
      (fin w n m A F P Q) (Nat.blt n (Nat.mul d d))) fuel

/-- Field width: `n < 2 ^ (width n - 1)`. -/
def width (n : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.add (Nat.log2 n) 2) 10 (Nat.blt n 512)

def impl (n : Nat) : Int :=
  (fun w => (fun m => (fun A => (fun F0 =>
      proc w n m 2 F0 0 F0 fun F P Q => proc w n m 3 F P Q fun F P Q => loop w n m A n 5 F P Q)
    (Nat.sub A 1))
    (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul w (Nat.add n 1))) 1) m))
    (Nat.sub (Nat.shiftLeft 1 w) 1)) (width n)

/-! ## Packed vectors -/

/-- `pk X f L = f 0 + f 1 * X + … + f (L - 1) * X ^ (L - 1)`. -/
def pk (X : Nat) : (Nat → Nat) → Nat → Nat
  | _, 0 => 0
  | f, L + 1 => f 0 + X * pk X (fun i => f (i + 1)) L

/-- `f 0 + … + f (L - 1)`. -/
def sm : (Nat → Nat) → Nat → Nat
  | _, 0 => 0
  | f, L + 1 => f 0 + sm (fun i => f (i + 1)) L

theorem pk_congr (X : Nat) : ∀ (L : Nat) (f g : Nat → Nat),
    (∀ i, i < L → f i = g i) → pk X f L = pk X g L
  | 0, _, _, _ => rfl
  | L + 1, f, g, h => by
    simp only [pk]
    rw [h 0 (by omega), pk_congr X L (fun i => f (i + 1)) (fun i => g (i + 1))
      (fun i hi => h (i + 1) (by omega))]

theorem sm_congr : ∀ (L : Nat) (f g : Nat → Nat),
    (∀ i, i < L → f i = g i) → sm f L = sm g L
  | 0, _, _, _ => rfl
  | L + 1, f, g, h => by
    simp only [sm]
    rw [h 0 (by omega), sm_congr L (fun i => f (i + 1)) (fun i => g (i + 1))
      (fun i hi => h (i + 1) (by omega))]

theorem pk_zero_fun (X : Nat) : ∀ L, pk X (fun _ => 0) L = 0
  | 0 => rfl
  | L + 1 => by simp only [pk]; rw [pk_zero_fun X L]; simp

theorem pk_add (X : Nat) : ∀ (L : Nat) (f g : Nat → Nat),
    pk X (fun i => f i + g i) L = pk X f L + pk X g L
  | 0, _, _ => rfl
  | L + 1, f, g => by
    simp only [pk]
    rw [pk_add X L (fun i => f (i + 1)) (fun i => g (i + 1)), Nat.mul_add]
    omega

theorem pk_mul (X c : Nat) : ∀ (L : Nat) (f : Nat → Nat),
    c * pk X f L = pk X (fun i => c * f i) L
  | 0, _ => by simp [pk]
  | L + 1, f => by
    simp only [pk]
    rw [← pk_mul X c L (fun i => f (i + 1)), Nat.mul_add, Nat.mul_left_comm]

theorem pk_lt (X : Nat) : ∀ (L : Nat) (f : Nat → Nat),
    (∀ i, i < L → f i < X) → pk X f L < X ^ L
  | 0, _, _ => by simp [pk]
  | L + 1, f, h => by
    simp only [pk]
    have ih := pk_lt X L (fun i => f (i + 1)) (fun i hi => h (i + 1) (by omega))
    have h0 := h 0 (by omega)
    have : X * (pk X (fun i => f (i + 1)) L + 1) ≤ X * X ^ L :=
      Nat.mul_le_mul_left X ih
    rw [Nat.pow_succ, Nat.mul_comm (X ^ L) X, Nat.mul_add, Nat.mul_one] at *
    omega

theorem pk_digit (X : Nat) : ∀ (m L : Nat) (f : Nat → Nat),
    (∀ i, i < L → f i < X) → m < L → pk X f L / X ^ m % X = f m
  | m, 0, _, _, hm => absurd hm (by omega)
  | 0, L + 1, f, h, _ => by
    simp only [pk, Nat.pow_zero, Nat.div_one]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 0 (by omega))]
  | m + 1, L + 1, f, h, hm => by
    have h0 := h 0 (by omega)
    have hX : 0 < X := by omega
    simp only [pk]
    rw [Nat.pow_succ, Nat.mul_comm (X ^ m) X, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ hX, Nat.div_eq_of_lt h0, Nat.zero_add]
    exact pk_digit X m L (fun i => f (i + 1)) (fun i hi => h (i + 1) (by omega)) (by omega)

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

theorem pk_and (W : Nat) (hW : 0 < W) (L : Nat) (f g : Nat → Nat)
    (hf : ∀ u, u < L → f u < 2 ^ W) (hg : ∀ u, u < L → g u < 2 ^ W) :
    pk (2 ^ W) f L &&& pk (2 ^ W) g L = pk (2 ^ W) (fun u => f u &&& g u) L := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_pk W hW L f hf, testBit_pk W hW L g hg,
    testBit_pk W hW L _ (fun u hu => Nat.and_lt_two_pow _ (hg u hu)), Nat.testBit_and]
  cases decide (i < W * L) <;> simp

theorem pk_xor (W : Nat) (hW : 0 < W) (L : Nat) (f g : Nat → Nat)
    (hf : ∀ u, u < L → f u < 2 ^ W) (hg : ∀ u, u < L → g u < 2 ^ W) :
    pk (2 ^ W) f L ^^^ pk (2 ^ W) g L = pk (2 ^ W) (fun u => f u ^^^ g u) L := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_pk W hW L f hf, testBit_pk W hW L g hg,
    testBit_pk W hW L _ (fun u hu => Nat.xor_lt_two_pow (hf u hu) (hg u hu)), Nat.testBit_xor]
  cases decide (i < W * L) <;> simp

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

/-- A packed vector is congruent to its digit sum modulo `X - 1`. -/
theorem pk_mod (m : Nat) : ∀ L f, pk (m + 1) f L % m = sm f L % m
  | 0, _ => rfl
  | L + 1, f => by
    show (f 0 + (m + 1) * pk (m + 1) _ L) % m = (f 0 + sm _ L) % m
    have ih := pk_mod m L (fun i => f (i + 1))
    rw [Nat.succ_mul, show f 0 + (m * pk (m + 1) (fun i => f (i + 1)) L +
      pk (m + 1) (fun i => f (i + 1)) L) = (f 0 + pk (m + 1) (fun i => f (i + 1)) L) +
      m * pk (m + 1) (fun i => f (i + 1)) L by omega, Nat.add_mul_mod_self_left,
      Nat.add_mod, ih, ← Nat.add_mod]

theorem sm_le : ∀ L (f : Nat → Nat), (∀ i, f i ≤ 1) → sm f L ≤ L
  | 0, _, _ => Nat.le_refl 0
  | L + 1, f, hf => by
    show f 0 + sm _ L ≤ L + 1
    have := sm_le L (fun i => f (i + 1)) (fun i => hf (i + 1))
    have := hf 0
    omega

theorem sm_sum : ∀ L (f : Nat → Nat), (sm f L : Int) = ∑ k ∈ Finset.range L, (f k : Int)
  | 0, _ => by simp [sm]
  | L + 1, f => by
    rw [Finset.sum_range_succ']
    show ((f 0 + sm _ L : Nat) : Int) = _
    rw [Nat.cast_add, sm_sum L (fun i => f (i + 1))]
    ring

/-- `(X - 1)² (0 + 1 X + … + n X^n) + (n + 1) X^(n+1) = n X^(n+2) + X`. -/
theorem pk_id (Y : Nat) : ∀ M, Y ^ 2 * pk (Y + 1) (fun k => k) (M + 1) + (M + 1) * (Y + 1) ^ (M + 1)
    = M * (Y + 1) ^ (M + 2) + (Y + 1)
  | 0 => by simp [pk]
  | M + 1 => by
    have ih := pk_id Y M
    have hs : pk (Y + 1) (fun k => k) (M + 1 + 1) =
        pk (Y + 1) (fun k => k) (M + 1) + (Y + 1) ^ (M + 1) * (M + 1) := by
      clear ih
      suffices h : ∀ (L s : Nat), pk (Y + 1) (fun k => k + s) (L + 1) =
          pk (Y + 1) (fun k => k + s) L + (Y + 1) ^ L * (L + s) by
        simpa using h (M + 1) 0
      intro L
      induction L with
      | zero => intro s; simp [pk]
      | succ L ihL =>
        intro s
        show (0 + s) + (Y + 1) * pk (Y + 1) (fun i => (i + 1) + s) (L + 1) =
          ((0 + s) + (Y + 1) * pk (Y + 1) (fun i => (i + 1) + s) L) + _
        have e : (fun i => i + 1 + s) = (fun i => i + (s + 1)) := by funext i; omega
        rw [e, ihL (s + 1), Nat.pow_succ]
        ring
    rw [hs]
    zify at ih ⊢
    have e1 : ((Y : Int) + 1) ^ (M + 1 + 1) = (Y + 1) ^ (M + 1) * (Y + 1) := pow_succ _ _
    have e2 : ((Y : Int) + 1) ^ (M + 2) = (Y + 1) ^ (M + 1) * (Y + 1) := pow_succ _ _
    have e3 : ((Y : Int) + 1) ^ (M + 1 + 2) = (Y + 1) ^ (M + 1) * (Y + 1) ^ 2 := by
      rw [pow_add]
    rw [e1, e3]
    rw [e2] at ih
    ring_nf at ih ⊢
    linarith

/-! ## Multiples patterns -/

/-- `((2^(a q) - 1) / den) <<< s`: the pattern computed inline in `proc`. -/
def pat (a q den s : Nat) : Nat :=
  Nat.shiftLeft (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul a q)) 1) den) s

theorem testBit_one_iff : ∀ r, (1 : Nat).testBit r = true ↔ r = 0
  | 0 => by simp
  | r + 1 => by simp [Nat.testBit_succ]

theorem testBit_pat (a q s i : Nat) (ha : 0 < a) :
    (pat a q (Nat.sub (Nat.shiftLeft 1 a) 1) s).testBit i = true ↔
      (s ≤ i ∧ i - s < a * q ∧ (i - s) % a = 0) := by
  have hsub : 0 < 2 ^ a - 1 := by
    have := Nat.one_lt_two_pow (show a ≠ 0 by omega)
    omega
  have hG : Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul a q)) 1) (Nat.sub (Nat.shiftLeft 1 a) 1)
      = pk (2 ^ a) (fun _ => 1) q := by
    show (1 <<< (a * q) - 1) / (1 <<< a - 1) = _
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul, ← geom a q,
      Nat.mul_div_cancel_left _ hsub]
  have hone : ∀ u, u < q → (fun _ => 1) u < 2 ^ a :=
    fun _ _ => Nat.one_lt_two_pow (by omega)
  show (Nat.shiftLeft _ s).testBit i = true ↔ _
  rw [hG]
  show (pk (2 ^ a) (fun _ => 1) q <<< s).testBit i = true ↔ _
  rw [Nat.testBit_shiftLeft, testBit_pk a ha _ _ hone]
  simp only [Bool.and_eq_true, decide_eq_true_eq, testBit_one_iff]

/-- A number whose set bits are the bases `w k` of the fields `k ≤ n` with `R k`. -/
theorem pk_of_bits (w n : Nat) (hw : 0 < w) (R : Nat → Prop) [DecidablePred R] (S : Nat)
    (h : ∀ i, S.testBit i = true ↔ (i % w = 0 ∧ i / w ≤ n ∧ R (i / w))) :
    S = pk (2 ^ w) (fun k => if R k then 1 else 0) (n + 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hf : ∀ u, u < n + 1 → (fun k => if R k then 1 else 0) u < 2 ^ w := by
    intro u _
    have := Nat.one_lt_two_pow (show w ≠ 0 by omega)
    dsimp only; split <;> omega
  rw [testBit_pk w hw (n + 1) _ hf i, Bool.eq_iff_iff, h i]
  have hlt : i < w * (n + 1) ↔ i / w ≤ n := by
    rw [Nat.mul_comm, ← Nat.div_lt_iff_lt_mul hw]; omega
  by_cases hp : R (i / w)
  · simp only [hp, if_true, Bool.and_eq_true, decide_eq_true_eq, testBit_one_iff, hlt, and_true]
    exact and_comm
  · simp [hp]

/-- Fields `e, 2e, …` (up to `n`). -/
theorem mults_pk (w n e : Nat) (hw : 0 < w) (he : 0 < e) :
    pat (w * e) (n / e) (Nat.sub (Nat.shiftLeft 1 (w * e)) 1) (w * e) =
      pk (2 ^ w) (fun k => if 0 < k ∧ e ∣ k then 1 else 0) (n + 1) := by
  have ha : 0 < w * e := Nat.mul_pos hw he
  apply pk_of_bits w n hw
  intro i
  rw [testBit_pat _ _ _ _ ha]
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero h3
    have ht2 : w * e * t < w * e * (n / e) := ht ▸ h2
    have ht3 : t < n / e := Nat.lt_of_mul_lt_mul_left ht2
    have hi : i = w * (e * (t + 1)) := by
      have : i = w * e * t + w * e := by omega
      rw [this]; ring
    subst hi
    rw [Nat.mul_mod_right, Nat.mul_div_cancel_left _ hw]
    have hle : e * (t + 1) ≤ e * (n / e) := Nat.mul_le_mul_left e ht3
    have := Nat.mul_div_le n e
    exact ⟨rfl, by omega, Nat.mul_pos he (by omega), Dvd.intro _ rfl⟩
  · rintro ⟨h1, h2, h3, t, ht⟩
    have hi : i = w * e * t := by
      rw [Nat.mul_assoc, ← ht]; exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h1)).symm
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · rw [h, Nat.mul_zero] at ht; omega
      · exact h
    have htq : t ≤ n / e := by
      rw [Nat.le_div_iff_mul_le he, Nat.mul_comm]; omega
    subst hi
    have e1 : w * e * t - w * e = w * e * (t - 1) := by rw [Nat.mul_sub_one]
    refine ⟨Nat.le_mul_of_pos_right _ ht1, ?_, ?_⟩
    · rw [e1]; exact Nat.mul_lt_mul_of_pos_left (by omega) ha
    · rw [e1, Nat.mul_mod_right]

/-! ## The invariant -/

/-- Primes below `d` dividing `k`. -/
def Af (d k : Nat) : Finset Nat := k.primeFactors.filter (· < d)

/-- Product of the primes below `d` dividing `k` (`0` for `k = 0`). -/
def Fv (d k : Nat) : Nat := if k = 0 then 0 else ∏ p ∈ Af d k, p

/-- Parity of the number of primes below `d` dividing `k`. -/
def Pv (d k : Nat) : Nat := (Af d k).card % 2

/-- `1` if `k > 0` and no `p * p` with `p` a prime below `d` divides `k`. -/
def Qv (d k : Nat) : Nat := if 0 < k ∧ ∀ p, p < d → p.Prime → ¬ p * p ∣ k then 1 else 0

def Inv (w n d F P Q : Nat) : Prop :=
  F = pk (2 ^ w) (Fv d) (n + 1) ∧ P = pk (2 ^ w) (Pv d) (n + 1) ∧ Q = pk (2 ^ w) (Qv d) (n + 1)

theorem Af_succ (d k : Nat) :
    Af (d + 1) k = if d ∈ k.primeFactors then insert d (Af d k) else Af d k := by
  ext p
  unfold Af
  split
  · rename_i h
    simp only [Finset.mem_insert, Finset.mem_filter]
    constructor
    · rintro ⟨hp, hlt⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h' | h'
      · exact Or.inr ⟨hp, h'⟩
      · exact Or.inl h'
    · rintro (rfl | ⟨hp, hlt⟩)
      · exact ⟨h, by omega⟩
      · exact ⟨hp, by omega⟩
  · rename_i h
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hlt⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h' | h'
      · exact ⟨hp, h'⟩
      · subst h'; exact absurd hp h
    · rintro ⟨hp, hlt⟩; exact ⟨hp, by omega⟩

theorem d_not_mem (d k : Nat) : d ∉ Af d k := by
  unfold Af; simp

theorem Fv_le (d k : Nat) : Fv d k ≤ k := by
  unfold Fv
  split
  · omega
  · rename_i hk
    apply Nat.le_of_dvd (by omega)
    exact Nat.dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))
      (Nat.prod_primeFactors_dvd k)

theorem Fv_succ (d k : Nat) :
    Fv (d + 1) k = if d.Prime ∧ d ∣ k then d * Fv d k else Fv d k := by
  unfold Fv
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk, if_neg hk, Af_succ]
    by_cases h : d.Prime ∧ d ∣ k
    · rw [if_pos (Nat.mem_primeFactors.mpr ⟨h.1, h.2, hk⟩), if_pos h,
        Finset.prod_insert (d_not_mem d k)]
    · rw [if_neg (fun hm => h ⟨(Nat.mem_primeFactors.mp hm).1, (Nat.mem_primeFactors.mp hm).2.1⟩),
        if_neg h]

theorem Pv_succ (d k : Nat) :
    Pv (d + 1) k = Pv d k ^^^ (if d.Prime ∧ d ∣ k ∧ k ≠ 0 then 1 else 0) := by
  unfold Pv
  rw [Af_succ]
  by_cases h : d.Prime ∧ d ∣ k ∧ k ≠ 0
  · rw [if_pos (Nat.mem_primeFactors.mpr h), if_pos h, Finset.card_insert_of_notMem (d_not_mem d k)]
    rcases Nat.mod_two_eq_zero_or_one (Af d k).card with h2 | h2
    · rw [h2, show ((Af d k).card + 1) % 2 = 1 by omega]; rfl
    · rw [h2, show ((Af d k).card + 1) % 2 = 0 by omega]; rfl
  · rw [if_neg (fun hm => h (Nat.mem_primeFactors.mp hm)), if_neg h, Nat.xor_zero]

theorem Qv_succ (d k : Nat) :
    Qv (d + 1) k = if d.Prime ∧ d * d ∣ k then 0 else Qv d k := by
  unfold Qv
  by_cases h : d.Prime ∧ d * d ∣ k
  · rw [if_pos h, if_neg]
    rintro ⟨_, hall⟩
    exact hall d (by omega) h.1 h.2
  · rw [if_neg h]
    congr 1
    apply propext
    constructor
    · rintro ⟨hk, hall⟩; exact ⟨hk, fun p hp => hall p (by omega)⟩
    · rintro ⟨hk, hall⟩
      refine ⟨hk, fun p hp hpp => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hp with h' | h'
      · exact hall p h' hpp
      · subst h'; exact fun hd => h ⟨hpp, hd⟩

theorem Fv_self (d : Nat) (hd : 2 ≤ d) : Fv d d = 1 ↔ d.Prime := by
  unfold Fv
  rw [if_neg (by omega)]
  constructor
  · intro h
    by_contra hnp
    have hlt := (Nat.not_prime_iff_minFac_lt hd).mp hnp
    have hmem : d.minFac ∈ Af d d := by
      unfold Af
      rw [Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨Nat.minFac_prime (by omega), Nat.minFac_dvd d, by omega⟩, hlt⟩
    have := Finset.dvd_prod_of_mem (fun p => p) hmem
    rw [h] at this
    have := (Nat.minFac_prime (show d ≠ 1 by omega)).two_le
    have := Nat.le_of_dvd (by omega) ‹d.minFac ∣ 1›
    omega
  · intro hp
    have : Af d d = ∅ := by
      unfold Af
      rw [Nat.Prime.primeFactors hp]
      simp
    rw [this, Finset.prod_empty]

/-! ## One sieve round -/

theorem land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

theorem Pv_le (d k : Nat) : Pv d k ≤ 1 := by
  unfold Pv; have := Nat.mod_lt (Af d k).card (show 2 > 0 by omega); omega

theorem Qv_le (d k : Nat) : Qv d k ≤ 1 := by
  unfold Qv; split <;> omega

theorem bit_cases (a : Nat) (h : a ≤ 1) : a = 0 ∨ a = 1 := by omega

theorem guard_eq (w n d F m : Nat) (hm : m = 2 ^ w - 1) (hF : F = pk (2 ^ w) (Fv d) (n + 1))
    (hb : ∀ u, u < n + 1 → Fv d u < 2 ^ w) :
    Nat.land (Nat.shiftRight F (Nat.mul w d)) m = if d ≤ n then Fv d d else 0 := by
  show F >>> (w * d) &&& m = _
  rw [hm, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.pow_mul, hF]
  split
  · exact pk_digit _ d (n + 1) _ hb (by omega)
  · have hlt := pk_lt _ (n + 1) _ hb
    have : (2 ^ w) ^ (n + 1) ≤ (2 ^ w) ^ d :=
      Nat.pow_le_pow_right (Nat.two_pow_pos w) (by omega)
    rw [Nat.div_eq_of_lt (by omega)]
    rfl

theorem Inv_skip (w n e F P Q : Nat) (he : ¬ e.Prime) (h : Inv w n e F P Q) :
    Inv w n (e + 1) F P Q := by
  obtain ⟨hF, hP, hQ⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [hF]; apply pk_congr; intro u _; rw [Fv_succ, if_neg (fun h => he h.1)]
  · rw [hP]; apply pk_congr; intro u _; rw [Pv_succ, if_neg (fun h => he h.1), Nat.xor_zero]
  · rw [hQ]; apply pk_congr; intro u _; rw [Qv_succ, if_neg (fun h => he h.1)]

theorem not_prime_of_dvd (e q : Nat) (hq : 2 ≤ q) (hqe : q < e) (hd : e % q = 0) : ¬ e.Prime :=
  fun hp => by
    rcases hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero hd) with h | h <;> omega

theorem proc_spec (w n m d F P Q : Nat) (hw : 0 < w) (hn : n < 2 ^ w) (hm : m = 2 ^ w - 1)
    (hd : 2 ≤ d) (hI : Inv w n d F P Q) (k : Nat → Nat → Nat → Int) (R : Int)
    (hk : ∀ F' P' Q', Inv w n (d + 1) F' P' Q' → k F' P' Q' = R) :
    proc w n m d F P Q k = R := by
  obtain ⟨hF, hP, hQ⟩ := hI
  have h2w : 2 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show 1 ≤ w by omega); simpa using this
  have hbF : ∀ u, u < n + 1 → Fv d u < 2 ^ w :=
    fun u hu => Nat.lt_of_le_of_lt (Fv_le d u) (by omega)
  have hbP : ∀ u, u < n + 1 → Pv d u < 2 ^ w := fun u _ => by have := Pv_le d u; omega
  have hbQ : ∀ u, u < n + 1 → Qv d u < 2 ^ w := fun u _ => by have := Qv_le d u; omega
  have hg := guard_eq w n d F m hm hF hbF
  unfold proc
  by_cases hc : d ≤ n ∧ d.Prime
  · have hb : Nat.beq (Nat.land (Nat.shiftRight F (Nat.mul w d)) m) 1 = true := by
      rw [hg, if_pos hc.1, (Fv_self d hd).mpr hc.2]; rfl
    rw [hb]
    apply hk
    have hdp := hc.2
    refine ⟨?_, ?_, ?_⟩
    · show F + (d - 1) * (F &&& (pat (w * d) (n / d) (Nat.sub (Nat.shiftLeft 1 (w * d)) 1)
        (w * d) * m)) = _
      rw [mults_pk w n d hw (by omega), Nat.mul_comm _ m, pk_mul, hF,
        pk_and w hw _ _ _ hbF (fun u _ => by
          split <;> simp only [Nat.mul_one, Nat.mul_zero] <;> omega),
        pk_mul, ← pk_add]
      apply pk_congr
      intro u _
      rw [Fv_succ, hm]
      by_cases hu : 0 < u ∧ d ∣ u
      · rw [if_pos hu, if_pos ⟨hdp, hu.2⟩, Nat.mul_one, Nat.and_two_pow_sub_one_eq_mod,
          Nat.mod_eq_of_lt (hbF u (by omega))]
        have : Fv d u ≤ d * Fv d u := Nat.le_mul_of_pos_left _ (by omega)
        rw [Nat.sub_one_mul]
        omega
      · rw [if_neg hu, Nat.mul_zero, Nat.and_zero, Nat.mul_zero, Nat.add_zero]
        split
        · rename_i h'
          have hu0 : u = 0 := by
            rcases Nat.eq_zero_or_pos u with h0 | h0
            · exact h0
            · exact absurd ⟨h0, h'.2⟩ hu
          subst hu0; simp [Fv]
        · rfl
    · show P ^^^ pat (w * d) (n / d) (Nat.sub (Nat.shiftLeft 1 (w * d)) 1) (w * d) = _
      rw [mults_pk w n d hw (by omega), hP, pk_xor w hw _ _ _ hbP (fun u _ => by split <;> omega)]
      apply pk_congr
      intro u _
      rw [Pv_succ]
      congr 1
      by_cases hu : 0 < u ∧ d ∣ u
      · rw [if_pos hu, if_pos ⟨hdp, hu.2, by omega⟩]
      · rw [if_neg hu, if_neg (fun h => hu ⟨by omega, h.2.1⟩)]
    · show Q ^^^ (Q &&& pat (w * (d * d)) (n / (d * d))
        (Nat.sub (Nat.shiftLeft 1 (w * (d * d))) 1) (w * (d * d))) = _
      rw [mults_pk w n (d * d) hw (Nat.mul_pos (by omega) (by omega)), hQ,
        pk_and w hw _ _ _ hbQ (fun u _ => by split <;> omega),
        pk_xor w hw _ _ _ hbQ (fun u _ => Nat.and_lt_two_pow _ (by split <;> omega))]
      apply pk_congr
      intro u _
      rw [Qv_succ]
      rcases bit_cases _ (Qv_le d u) with hq | hq
      · by_cases hu : 0 < u ∧ d * d ∣ u
        · rw [if_pos hu, if_pos ⟨hdp, hu.2⟩, hq]; rfl
        · rw [if_neg hu, hq]; split <;> rfl
      · by_cases hu : 0 < u ∧ d * d ∣ u
        · rw [if_pos hu, if_pos ⟨hdp, hu.2⟩, hq]; rfl
        · rw [if_neg hu, hq]
          split
          · rename_i h'
            exfalso
            have hu0 : u = 0 := by
              rcases Nat.eq_zero_or_pos u with h0 | h0
              · exact h0
              · exact absurd ⟨h0, h'.2⟩ hu
            subst hu0
            unfold Qv at hq; simp at hq
          · rfl
  · have hb : Nat.beq (Nat.land (Nat.shiftRight F (Nat.mul w d)) m) 1 = false := by
      rw [Bool.eq_false_iff]
      intro h
      rw [Nat.beq_eq, hg] at h
      split at h
      · exact hc ⟨by assumption, (Fv_self d hd).mp h⟩
      · omega
    rw [hb]
    apply hk
    refine ⟨?_, ?_, ?_⟩
    · rw [hF]; apply pk_congr; intro u hu
      rw [Fv_succ]
      split
      · rename_i h'
        have hu0 : u = 0 := by
          rcases Nat.eq_zero_or_pos u with h0 | h0
          · exact h0
          · exact absurd ⟨Nat.le_trans (Nat.le_of_dvd h0 h'.2) (by omega), h'.1⟩ hc
        subst hu0; simp [Fv]
      · rfl
    · rw [hP]; apply pk_congr; intro u hu
      rw [Pv_succ, if_neg, Nat.xor_zero]
      rintro ⟨h1, h2, h3⟩
      exact hc ⟨Nat.le_trans (Nat.le_of_dvd (by omega) h2) (by omega), h1⟩
    · rw [hQ]; apply pk_congr; intro u hu
      rw [Qv_succ]
      split
      · rename_i h'
        rcases Nat.eq_zero_or_pos u with h0 | h0
        · subst h0; simp [Qv]
        · exfalso
          have := Nat.le_of_dvd h0 h'.2
          have : d ≤ d * d := Nat.le_mul_self d
          exact hc ⟨by omega, h'.1⟩
      · rfl

/-! ## The Möbius value of one field -/

theorem omega_card (k : Nat) : ArithmeticFunction.cardDistinctFactors k = k.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

theorem neg_one_pow_eq (c : Nat) : (-1 : Int) ^ c = if c % 2 = 0 then 1 else -1 := by
  split
  · exact Even.neg_one_pow (Nat.even_iff.mpr (by assumption))
  · exact Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))

/-- Once every prime `p < d` is processed and `n < d * d`, a squarefree `k ≤ n` has exactly one
more prime factor exactly when the product of its small prime factors is below `k`. -/
theorem card_split (d k n : Nat) (hk0 : 0 < k) (hkn : k ≤ n) (hd : n < d * d)
    (hsq : Squarefree k) :
    k.primeFactors.card = (Af d k).card + (if Fv d k < k then 1 else 0) := by
  set B := k.primeFactors.filter (fun p => ¬ p < d) with hB
  have hcard := Finset.card_filter_add_card_filter_not (s := k.primeFactors) (fun p => p < d)
  have hprod := Finset.prod_filter_mul_prod_filter_not k.primeFactors (fun p => p < d)
    (f := fun p => p)
  rw [Nat.prod_primeFactors_of_squarefree hsq] at hprod
  have hFv : Fv d k = ∏ p ∈ Af d k, p := by unfold Fv; rw [if_neg (by omega)]
  have hB1 : B.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hne
    rw [hB, Finset.mem_filter, Nat.mem_primeFactors] at ha hb
    have hab : a * b ∣ k := Nat.Coprime.mul_dvd_of_dvd_of_dvd
      ((Nat.coprime_primes ha.1.1 hb.1.1).mpr hne) ha.1.2.1 hb.1.2.1
    have := Nat.le_of_dvd hk0 hab
    have : d * d ≤ a * b := Nat.mul_le_mul (by omega) (by omega)
    omega
  unfold Af
  rcases Nat.lt_or_ge B.card 1 with h0 | h1
  · have hBe : B = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hB] at hBe
    rw [hBe, Finset.prod_empty, Nat.mul_one] at hprod
    unfold Af at hFv
    rw [if_neg (by omega)]
    rw [hBe, Finset.card_empty] at hcard
    omega
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp (show B.card = 1 by omega)
    have hpm : p ∈ B := by rw [hp]; exact Finset.mem_singleton_self p
    rw [hB, Finset.mem_filter, Nat.mem_primeFactors] at hpm
    rw [hB] at hp
    rw [hp, Finset.prod_singleton] at hprod
    rw [hp, Finset.card_singleton] at hcard
    unfold Af at hFv
    have hp2 := hpm.1.1.two_le
    have hpos : 0 < ∏ p ∈ Finset.filter (fun p => p < d) k.primeFactors, p := by
      rcases Nat.eq_zero_or_pos (∏ p ∈ Finset.filter (fun p => p < d) k.primeFactors, p) with
        h | h
      · rw [h, Nat.zero_mul] at hprod; omega
      · exact h
    have : ∏ p ∈ Finset.filter (fun p => p < d) k.primeFactors, p < k := by
      have := Nat.mul_le_mul_left (∏ p ∈ Finset.filter (fun p => p < d) k.primeFactors, p) hp2
      omega
    rw [if_pos (by omega)]
    omega

theorem mu_field (d n k : Nat) (hkn : k ≤ n) (hd : n < d * d) :
    ((Qv d k ^^^ (Qv d k &&& (Pv d k ^^^ (if Fv d k < k then 1 else 0))) : Nat) : Int) -
      ((Qv d k &&& (Pv d k ^^^ (if Fv d k < k then 1 else 0)) : Nat) : Int) =
      ArithmeticFunction.moebius k := by
  unfold Qv
  split
  · rename_i hq
    obtain ⟨hk0, hall⟩ := hq
    have hsq : Squarefree k := by
      rw [Nat.squarefree_iff_prime_squarefree]
      intro p hp hpp
      have := Nat.le_of_dvd hk0 hpp
      exact hall p (Nat.mul_self_lt_mul_self_iff.mp (by omega)) hp hpp
    rw [ArithmeticFunction.moebius_apply_of_squarefree hsq,
      ← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree
        (by omega)).mpr hsq,
      omega_card, card_split d k n hk0 hkn hd hsq, neg_one_pow_eq]
    unfold Pv
    rcases Nat.mod_two_eq_zero_or_one (Af d k).card with h | h <;>
      by_cases hb : Fv d k < k <;> simp [h, hb] <;> omega
  · rename_i hq
    have : ArithmeticFunction.moebius k = 0 := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; simp
      · apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
        intro hsq
        apply hq
        refine ⟨h0, fun p _ hp hpp => ?_⟩
        exact (Nat.squarefree_iff_prime_squarefree.mp hsq) p hp hpp
    rw [this]
    simp

/-! ## The final count -/

theorem top_bit (q c : Nat) (hq : 0 < q) (hc : c < q) (i : Nat) (hi : q = 2 ^ i) :
    (c + (q - 1)).testBit i = decide (1 ≤ c) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, ← hi]
  by_cases h : 1 ≤ c
  · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]; simp [h]
  · rw [Nat.div_eq_of_lt (by omega)]; simp [h]

theorem fin_spec (w n m A F P Q d : Nat) (hw : 0 < w) (hn : n < 2 ^ (w - 1))
    (hn2 : n + 2 < 2 ^ w) (hm : m = 2 ^ w - 1) (hA : A = pk (2 ^ w) (fun _ => 1) (n + 1))
    (hd : n < d * d) (hI : Inv w n d F P Q) : fin w n m A F P Q = mertensSpec n := by
  obtain ⟨hF, hP, hQ⟩ := hI
  have hX : 2 ^ w = 2 ^ (w - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have hFk : ∀ u, u < n + 1 → Fv d u < 2 ^ w :=
    fun u hu => Nat.lt_of_le_of_lt (Fv_le d u) (by omega)
  have hmX : m + 1 = 2 ^ w := by rw [hm]; omega
  -- the identity vector
  have hK : Nat.div (Nat.sub (Nat.add (Nat.mul n (Nat.shiftLeft 1 (Nat.mul w (Nat.add n 2))))
        (Nat.shiftLeft 1 w)) (Nat.mul (Nat.add n 1) (Nat.shiftLeft 1 (Nat.mul w (Nat.add n 1)))))
      (Nat.mul m m) = pk (2 ^ w) (fun k => k) (n + 1) := by
    show (n * (1 <<< (w * (n + 2))) + (1 <<< w) - (n + 1) * (1 <<< (w * (n + 1)))) / (m * m) = _
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul,
      Nat.one_mul, Nat.pow_mul, Nat.pow_mul, ← hmX]
    have := pk_id m n
    rw [Nat.pow_two] at this
    rw [show n * (m + 1) ^ (n + 2) + (m + 1) - (n + 1) * (m + 1) ^ (n + 1) =
      m * m * pk (m + 1) (fun k => k) (n + 1) by omega]
    exact Nat.mul_div_cancel_left _ (Nat.mul_pos (by omega) (by omega))
  -- `K - F + H`, digit by digit
  have hKF : pk (2 ^ w) (fun k => k) (n + 1) - F = pk (2 ^ w) (fun k => k - Fv d k) (n + 1) := by
    have := pk_add (2 ^ w) (n + 1) (fun k => k - Fv d k) (Fv d)
    rw [pk_congr (2 ^ w) (n + 1) (fun i => i - Fv d i + Fv d i) (fun k => k)
      (fun i _ => Nat.sub_add_cancel (Fv_le d i))] at this
    rw [hF, this]; omega
  have hH : Nat.mul A (Nat.sub (Nat.shiftLeft 1 (Nat.sub w 1)) 1) =
      pk (2 ^ w) (fun _ => 2 ^ (w - 1) - 1) (n + 1) := by
    show A * (1 <<< (w - 1) - 1) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul, hA, Nat.mul_comm, pk_mul]
    simp
  have hbig : Nat.land (Nat.shiftRight (Nat.add (Nat.sub (pk (2 ^ w) (fun k => k) (n + 1)) F)
      (Nat.mul A (Nat.sub (Nat.shiftLeft 1 (Nat.sub w 1)) 1))) (Nat.sub w 1)) A =
      pk (2 ^ w) (fun k => if Fv d k < k then 1 else 0) (n + 1) := by
    show ((pk (2 ^ w) (fun k => k) (n + 1) - F) + Nat.mul A (Nat.sub (Nat.shiftLeft 1 (Nat.sub w 1)) 1))
      >>> (w - 1) &&& A = _
    rw [hKF, hH, ← pk_add]
    apply pk_of_bits w n hw
    intro i
    have hv : ∀ u, u < n + 1 → u - Fv d u + (2 ^ (w - 1) - 1) < 2 ^ w := by
      intro u hu; have := Nat.two_pow_pos (w - 1); omega
    have h1 : ∀ u, u < n + 1 → (fun _ => 1) u < 2 ^ w := fun _ _ => Nat.one_lt_two_pow (by omega)
    rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_pk w hw _ _ hv, hA,
      testBit_pk w hw _ _ h1]
    simp only [Bool.and_eq_true, decide_eq_true_eq, testBit_one_iff]
    have hlt : i < w * (n + 1) ↔ i / w ≤ n := by
      rw [Nat.mul_comm, ← Nat.div_lt_iff_lt_mul hw]; omega
    rw [hlt]
    by_cases h3 : i % w = 0
    · obtain ⟨k, rfl⟩ : ∃ k, i = w * k :=
        ⟨i / w, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h3)).symm⟩
      rw [Nat.mul_div_cancel_left k hw]
      have e1 : (w - 1 + w * k) / w = k := by
        apply Nat.div_eq_of_lt_le
        · rw [Nat.mul_comm]; omega
        · rw [Nat.succ_mul, Nat.mul_comm]; omega
      have e2 : (w - 1 + w * k) % w = w - 1 := by
        have := Nat.mod_add_div (w - 1 + w * k) w
        rw [e1] at this
        omega
      rw [e1, e2]
      by_cases hkn : k ≤ n
      · rw [top_bit (2 ^ (w - 1)) _ (Nat.two_pow_pos _)
          (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by omega)) (w - 1) rfl]
        have hwk : w * k ≤ w * n := Nat.mul_le_mul_left w hkn
        have : w - 1 + w * k < w * (n + 1) := by rw [Nat.mul_succ]; omega
        simp only [this, hkn, h3, decide_eq_true_eq, true_and, and_true]
        omega
      · simp [hkn]
    · simp [h3]
  have hb1 : ∀ x, x ≤ 1 → x < 2 ^ w := fun x hx => by omega
  have xor01 : ∀ a b : Nat, a ≤ 1 → b ≤ 1 → a ^^^ b ≤ 1 := by
    intro a b ha hb
    rcases bit_cases a ha with rfl | rfl <;> rcases bit_cases b hb with rfl | rfl <;> decide
  have and01 : ∀ a b : Nat, a ≤ 1 → a &&& b ≤ 1 := by
    intro a b ha
    exact Nat.le_trans Nat.and_le_left ha
  have hbb : ∀ k, (if Fv d k < k then 1 else 0) ≤ 1 := fun k => by split <;> omega
  unfold fin
  rw [hK, hbig, hP, hQ]
  simp only [land_eq, xor_eq]
  rw [pk_xor w hw _ _ _ (fun u _ => hb1 _ (Pv_le d u)) (fun u _ => hb1 _ (hbb u)),
    pk_and w hw _ _ _ (fun u _ => hb1 _ (Qv_le d u))
      (fun u _ => hb1 _ (xor01 _ _ (Pv_le d u) (hbb u))),
    pk_xor w hw _ _ _ (fun u _ => hb1 _ (Qv_le d u))
      (fun u _ => hb1 _ (and01 _ _ (Qv_le d u)))]
  rw [← hmX]
  show Int.subNatNat (pk (m + 1) _ (n + 1) % m) (pk (m + 1) _ (n + 1) % m) = _
  rw [pk_mod, pk_mod, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Int.subNatNat_eq_coe, sm_sum, sm_sum,
    ← Finset.sum_sub_distrib]
  · unfold mertensSpec
    apply Finset.sum_congr rfl
    intro k hk
    exact mu_field d n k (by rw [Finset.mem_range] at hk; omega) hd
  all_goals
    refine Nat.lt_of_le_of_lt (sm_le _ _ (fun i => ?_)) (by omega)
    first
    | exact xor01 _ _ (Qv_le d i) (and01 _ _ (Qv_le d i))
    | exact and01 _ _ (Qv_le d i)

/-! ## The loop and the entry point -/

theorem blt_iff (a b : Nat) : Nat.blt a b = true ↔ a < b := by
  simp [Nat.blt_eq]

theorem loop_spec (w n m A : Nat) (hw : 0 < w) (hn : n < 2 ^ (w - 1)) (hn2 : n + 2 < 2 ^ w)
    (hm : m = 2 ^ w - 1) (hA : A = pk (2 ^ w) (fun _ => 1) (n + 1)) :
    ∀ fuel d F P Q, d % 6 = 5 → 5 ≤ d → Inv w n d F P Q →
      n < (d + 6 * fuel) * (d + 6 * fuel) → loop w n m A fuel d F P Q = mertensSpec n
  | 0, d, F, P, Q, _, _, hI, hd => fin_spec w n m A F P Q d hw hn hn2 hm hA (by simpa using hd) hI
  | fuel + 1, d, F, P, Q, h6, h5, hI, hd => by
    have hnw : n < 2 ^ w := by omega
    show Bool.rec (motive := fun _ => Int)
      (proc w n m d F P Q fun F P Q => proc w n m (Nat.add d 2) F P Q fun F P Q =>
        loop w n m A fuel (Nat.add d 6) F P Q)
      (fin w n m A F P Q) (Nat.blt n (Nat.mul d d)) = _
    cases hb : Nat.blt n (Nat.mul d d)
    · show proc w n m d F P Q (fun F P Q => proc w n m (d + 2) F P Q fun F P Q =>
        loop w n m A fuel (d + 6) F P Q) = _
      apply proc_spec w n m d F P Q hw hnw hm (by omega) hI
      intro F1 P1 Q1 h1
      have h1' := Inv_skip w n (d + 1) F1 P1 Q1 (not_prime_of_dvd _ 2 (by omega) (by omega)
        (by omega)) h1
      apply proc_spec w n m (d + 2) F1 P1 Q1 hw hnw hm (by omega) h1'
      intro F2 P2 Q2 h2
      have h3 := Inv_skip w n (d + 3) F2 P2 Q2 (not_prime_of_dvd _ 2 (by omega) (by omega)
        (by omega)) h2
      have h4 := Inv_skip w n (d + 4) F2 P2 Q2 (not_prime_of_dvd _ 3 (by omega) (by omega)
        (by omega)) h3
      have h5' := Inv_skip w n (d + 5) F2 P2 Q2 (not_prime_of_dvd _ 2 (by omega) (by omega)
        (by omega)) h4
      exact loop_spec w n m A hw hn hn2 hm hA fuel (d + 6) F2 P2 Q2 (by omega) (by omega) h5'
        (by rw [show d + 6 + 6 * fuel = d + 6 * (fuel + 1) by omega]; exact hd)
    · exact fin_spec w n m A F P Q d hw hn hn2 hm hA ((blt_iff _ _).mp hb) hI

theorem width_spec (n : Nat) : 0 < width n ∧ n < 2 ^ (width n - 1) ∧ n + 2 < 2 ^ width n := by
  unfold width
  cases h : Nat.blt n 512
  · show 0 < Nat.log2 n + 2 ∧ n < 2 ^ (Nat.log2 n + 2 - 1) ∧ n + 2 < 2 ^ (Nat.log2 n + 2)
    have hge : ¬ n < 512 := fun h' => by rw [(blt_iff _ _).mpr h'] at h; contradiction
    have := Nat.lt_log2_self (n := n)
    rw [show Nat.log2 n + 2 - 1 = Nat.log2 n + 1 by omega, Nat.pow_succ 2 (Nat.log2 n + 1)]
    omega
  · show 0 < 10 ∧ n < 2 ^ (10 - 1) ∧ n + 2 < 2 ^ 10
    have := (blt_iff _ _).mp h
    have h9 : (2 : Nat) ^ (10 - 1) = 512 := rfl
    have h10 : (2 : Nat) ^ 10 = 1024 := rfl
    omega

theorem impl_correct : ∀ n, impl n = mertensSpec n := by
  intro n
  obtain ⟨hw, hn, hn2⟩ := width_spec n
  show proc (width n) n (Nat.sub (Nat.shiftLeft 1 (width n)) 1) 2
    (Nat.sub (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul (width n) (Nat.add n 1))) 1)
      (Nat.sub (Nat.shiftLeft 1 (width n)) 1)) 1) 0
    (Nat.sub (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul (width n) (Nat.add n 1))) 1)
      (Nat.sub (Nat.shiftLeft 1 (width n)) 1)) 1)
    (fun F P Q => proc (width n) n (Nat.sub (Nat.shiftLeft 1 (width n)) 1) 3 F P Q
      fun F P Q => loop (width n) n (Nat.sub (Nat.shiftLeft 1 (width n)) 1)
        (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul (width n) (Nat.add n 1))) 1)
          (Nat.sub (Nat.shiftLeft 1 (width n)) 1)) n 5 F P Q) = _
  generalize width n = w at hw hn hn2
  have hm : Nat.sub (Nat.shiftLeft 1 w) 1 = 2 ^ w - 1 := by
    show 1 <<< w - 1 = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hA : Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul w (Nat.add n 1))) 1)
      (Nat.sub (Nat.shiftLeft 1 w) 1) = pk (2 ^ w) (fun _ => 1) (n + 1) := by
    rw [hm]
    show (1 <<< (w * (n + 1)) - 1) / (2 ^ w - 1) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul, ← geom w (n + 1),
      Nat.mul_div_cancel_left _ (by omega)]
  generalize Nat.sub (Nat.shiftLeft 1 w) 1 = m at hm hA
  generalize Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul w (Nat.add n 1))) 1) m = A at hA
  have hnw : n < 2 ^ w := by omega
  have h0 : Inv w n 2 (A - 1) 0 (A - 1) := by
    have hA1 : A - 1 = pk (2 ^ w) (fun k => if k = 0 then 0 else 1) (n + 1) := by
      rw [hA]
      show 1 + 2 ^ w * pk (2 ^ w) (fun _ => 1) n - 1 = 0 + 2 ^ w * pk (2 ^ w) _ n
      rw [pk_congr (2 ^ w) n (fun i => if i + 1 = 0 then 0 else 1) (fun _ => 1)
        (fun i _ => by simp)]
      omega
    have hAf : ∀ k, Af 2 k = ∅ := by
      intro k; unfold Af
      apply Finset.filter_false_of_mem
      intro p hp
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      omega
    refine ⟨?_, ?_, ?_⟩
    · rw [hA1]; apply pk_congr; intro u _; unfold Fv; rw [hAf]; simp
    · rw [← pk_zero_fun (2 ^ w) (n + 1)]; apply pk_congr; intro u _; unfold Pv; rw [hAf]; simp
    · rw [hA1]; apply pk_congr; intro u _; unfold Qv
      by_cases hu : u = 0
      · simp [hu]
      · rw [if_neg hu, if_pos ⟨by omega, fun p hp hpp => absurd hpp.two_le (by omega)⟩]
  apply proc_spec w n m 2 _ _ _ hw hnw hm (by omega) h0
  intro F1 P1 Q1 h1
  apply proc_spec w n m 3 F1 P1 Q1 hw hnw hm (by omega) h1
  intro F2 P2 Q2 h2
  have h5 := Inv_skip w n 4 F2 P2 Q2 (not_prime_of_dvd 4 2 (by omega) (by omega) (by omega)) h2
  apply loop_spec w n m A hw hn hn2 hm hA n 5 F2 P2 Q2 (by omega) (by omega) h5
  have := Nat.le_mul_self (5 + 6 * n)
  omega

end Submission
