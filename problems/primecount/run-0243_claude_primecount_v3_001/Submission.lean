import Spec

/-!
# Prime counting with a spread-out sieve counted by one `mod`

Every number `k ≤ n` gets its own field of `w` bits (`2 ^ w > n + 2`): the sieve
`S` has bit `w * k` set exactly when `k` is still a candidate, and every other bit
clear. Viewed in base `B = 2 ^ w`, `S` is a number whose digits are `0` or `1`, so
since `B ≡ 1 (mod B - 1)` the digit sum, which is the number of candidates, is
simply `S % (B - 1)`. That replaces a set-bit-counting loop (one kernel step per
prime) by a single big-number operation.

Sieving: start from the fields `2 … n`, then for `d = 2`, `3` and then
`d = 6j + 5`, `6j + 7` (every prime is `2`, `3`, or `≡ ±1 (mod 6)`) clear the
fields `d², d² + d, …`, stopping as soon as `d * d > n`. The pattern of those
fields is one closed form, `((2^{aq} - 1) / (2^a - 1)) <<< (a d)` with `a = w d`,
`q = n / d`.

Kernel-cost notes: loops are `Nat.rec`, branches are `Bool.rec` (cheaper than
`cond`), word operations call `Nat.*` directly, and `Nat.log2` (not
GMP-accelerated) is only used when `n ≥ 1022`.
-/

namespace Submission

/-! ## Implementation -/

/-- `((2^(a q) - 1) / den) <<< s`; with `den = 2^a - 1` its set bits are
`s, s + a, …, s + a (q - 1)`. (Written out inline in `step` and `impl`, where it is
cheaper for the kernel; the proofs use this name.) -/
def pat (a q den s : Nat) : Nat :=
  Nat.shiftLeft (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul a q)) 1) den) s

/-- Clear the fields `d², d² + d, …` (at most `n`) of `S`. -/
def step (w n d S : Nat) : Nat :=
  (fun a => Nat.xor S (Nat.land S (Nat.shiftLeft
    (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul a (Nat.div n d))) 1) (Nat.sub (Nat.shiftLeft 1 a) 1))
    (Nat.mul a d)))) (Nat.mul w d)

/-- Sieve with `d, d + 2, d + 6, d + 8, …` until `n < d * d`; `fuel` only bounds it. -/
def loop (w n fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih d S => Bool.rec (motive := fun _ => Nat)
      (ih (Nat.add d 6) (step w n (Nat.add d 2) (step w n d S))) S (Nat.blt n (Nat.mul d d)))
    fuel

/-- Field width: `2 ^ width n > n + 2`. -/
def width (n : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.add (Nat.log2 n) 2) 10 (Nat.blt n 1022)

def impl (n : Nat) : Nat :=
  (fun w => (fun m => Nat.mod
    (loop w n n 5 (step w n 3 (step w n 2
      (Nat.shiftLeft (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul w (Nat.sub n 1))) 1) m)
        (Nat.mul 2 w))))) m)
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

/-- A packed vector is congruent to its digit sum modulo `X - 1`. -/
theorem pk_modEq (X : Nat) (hX : 1 ≤ X) : ∀ L f, pk X f L ≡ sm f L [MOD X - 1]
  | 0, _ => rfl
  | L + 1, f => by
    show f 0 + X * pk X _ L ≡ f 0 + sm _ L [MOD X - 1]
    have h := (Nat.modEq_sub hX).mul (pk_modEq X hX L (fun i => f (i + 1)))
    rw [Nat.one_mul] at h
    exact Nat.ModEq.add_left _ h

theorem sm_le : ∀ L (f : Nat → Nat), (∀ i, f i ≤ 1) → sm f L ≤ L
  | 0, _, _ => Nat.le_refl 0
  | L + 1, f, hf => by
    show f 0 + sm _ L ≤ L + 1
    have := sm_le L (fun i => f (i + 1)) (fun i => hf (i + 1))
    have := hf 0
    omega

theorem sm_count : ∀ L (p : Nat → Prop) [DecidablePred p],
    sm (fun k => if p k then 1 else 0) L = Nat.count p L
  | 0, _, _ => by simp [sm]
  | L + 1, p, _ => by
    rw [Nat.count_succ']
    show (if p 0 then 1 else 0) + sm (fun k => if p (k + 1) then 1 else 0) L = _
    rw [sm_count L (fun k => p (k + 1))]
    omega

/-! ## Bit patterns -/

theorem land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

theorem testBit_one_iff : ∀ r, (1 : Nat).testBit r = true ↔ r = 0
  | 0 => by simp
  | r + 1 => by simp [Nat.testBit_succ]

theorem blt_iff (a b : Nat) : Nat.blt a b = true ↔ a < b := by
  simp [Nat.blt_eq]

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

/-! ## The sieve invariant -/

/-- `S` has exactly the bits `w * k` with `k ≤ n` and `P k`. -/
def fld (w n : Nat) (P : Nat → Prop) (S : Nat) : Prop :=
  ∀ i, S.testBit i = true ↔ (i % w = 0 ∧ i / w ≤ n ∧ P (i / w))

theorem fld_congr {w n : Nat} {P Q : Nat → Prop} {S : Nat}
    (h : ∀ k, k ≤ n → (P k ↔ Q k)) (hS : fld w n P S) : fld w n Q S := by
  intro i
  rw [hS i]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (h _ h2).mp h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (h _ h2).mpr h3⟩

/-- Field `k ≤ n` is hit by the pattern of `step` exactly when `d * d ≤ k` and `d ∣ k`. -/
theorem hit_iff (w d k n : Nat) (hw : 0 < w) (hd : 2 ≤ d) (hk : k ≤ n) :
    (w * d * d ≤ w * k ∧ w * k - w * d * d < w * d * (n / d) ∧
      (w * k - w * d * d) % (w * d) = 0) ↔ (d * d ≤ k ∧ d ∣ k) := by
  rw [Nat.mul_assoc w d d, Nat.mul_assoc w d (n / d), ← Nat.mul_sub, Nat.mul_mod_mul_left,
    Nat.mul_le_mul_left_iff hw, Nat.mul_lt_mul_left hw, Nat.mul_eq_zero]
  have h2d : 2 * d ≤ d * d := Nat.mul_le_mul_right d hd
  have hq : n < d * (n / d + 1) := Nat.lt_mul_div_succ n (by omega)
  rw [Nat.mul_add, Nat.mul_one] at hq
  constructor
  · rintro ⟨h1, _, h3⟩
    refine ⟨h1, ?_⟩
    have h3' : (k - d * d) % d = 0 := by omega
    have := Nat.dvd_add (Nat.dvd_of_mod_eq_zero h3') (Dvd.intro d rfl)
    rwa [Nat.sub_add_cancel h1] at this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, by omega, Or.inr ?_⟩
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_sub h2 (Dvd.intro d rfl))

theorem step_fld (w n d S : Nat) (P : Nat → Prop) (hw : 0 < w) (hd : 2 ≤ d)
    (hS : fld w n P S) : fld w n (fun k => P k ∧ ¬ (d * d ≤ k ∧ d ∣ k)) (step w n d S) := by
  intro i
  have ha : 0 < w * d := Nat.mul_pos hw (by omega)
  show (Nat.xor S (Nat.land S (pat (w * d) (n / d) (Nat.sub (Nat.shiftLeft 1 (w * d)) 1)
    (w * d * d)))).testBit i = true ↔ _
  rw [xor_eq, land_eq, Nat.testBit_xor, Nat.testBit_and]
  cases hb : S.testBit i
  · have h := hS i
    rw [hb] at h
    simp only [Bool.false_and, Bool.false_xor, Bool.false_eq_true, false_iff]
    rintro ⟨h1, h2, h3, _⟩
    exact absurd (h.mpr ⟨h1, h2, h3⟩) (by simp)
  · obtain ⟨h1, h2, h3⟩ := (hS i).mp hb
    obtain ⟨k, rfl⟩ : ∃ k, i = w * k := ⟨i / w, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h1)).symm⟩
    rw [Nat.mul_div_cancel_left k hw] at h2 h3 ⊢
    simp only [Bool.true_and, Bool.true_xor, Bool.not_eq_true', Nat.mul_mod_right, h2, h3,
      true_and]
    rw [Bool.eq_false_iff, ne_eq, testBit_pat _ _ _ _ ha, hit_iff w d k n hw hd h2]

/-! ## The wheel -/

/-- The divisors used before reaching `d`: `2`, `3`, and `5 ≤ e < d` with `e ≡ ±1 (mod 6)`. -/
def Cov (d e : Nat) : Prop := e = 2 ∨ e = 3 ∨ (5 ≤ e ∧ e < d ∧ (e % 6 = 5 ∨ e % 6 = 1))

/-- `k` survives sieving by the divisors covered before `d`. -/
def Q (d k : Nat) : Prop := 2 ≤ k ∧ ∀ e, Cov d e → ¬ (e * e ≤ k ∧ e ∣ k)

theorem Q_prime (n d k : Nat) (hk : k ≤ n) (hn : n < d * d) : Q d k ↔ k.Prime := by
  constructor
  · rintro ⟨h2, hall⟩
    by_contra hnp
    have hk1 : k ≠ 1 := by omega
    have hp := Nat.minFac_prime hk1
    have hsq := Nat.minFac_sq_le_self (by omega) hnp
    have hpd := Nat.minFac_dvd k
    have hp2 := hp.two_le
    rw [Nat.pow_two] at hsq
    have hlt : k.minFac < d := Nat.mul_self_lt_mul_self_iff.mp (by omega)
    have hodd : k.minFac % 2 = 1 ∨ k.minFac = 2 := by
      by_cases h : k.minFac % 2 = 0
      · rcases hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h) with h' | h' <;> omega
      · omega
    have h3 : k.minFac % 3 ≠ 0 ∨ k.minFac = 3 := by
      by_cases h : k.minFac % 3 = 0
      · rcases hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h) with h' | h' <;> omega
      · omega
    exact hall k.minFac (by unfold Cov; omega) ⟨hsq, hpd⟩
  · intro hp
    refine ⟨hp.two_le, fun e he ⟨hee, hdvd⟩ => ?_⟩
    have he2 : 2 ≤ e := by unfold Cov at he; omega
    rcases hp.eq_one_or_self_of_dvd e hdvd with h | h
    · omega
    · subst h
      have := Nat.mul_le_mul_right e he2
      omega

theorem loop_fld (w n : Nat) (hw : 0 < w) : ∀ fuel d S, d % 6 = 5 → 5 ≤ d →
    fld w n (Q d) S → n < (d + 6 * fuel) * (d + 6 * fuel) →
    fld w n Nat.Prime (loop w n fuel d S)
  | 0, d, S, _, _, hS, hn => by
    show fld w n Nat.Prime S
    exact fld_congr (fun k hk => Q_prime n d k hk (by simpa using hn)) hS
  | fuel + 1, d, S, h6, h5, hS, hn => by
    show fld w n Nat.Prime (Bool.rec (motive := fun _ => Nat)
      (loop w n fuel (Nat.add d 6) (step w n (Nat.add d 2) (step w n d S))) S
      (Nat.blt n (Nat.mul d d)))
    cases hb : Nat.blt n (Nat.mul d d)
    · show fld w n Nat.Prime (loop w n fuel (d + 6) (step w n (d + 2) (step w n d S)))
      refine loop_fld w n hw fuel (d + 6) _ (by omega) (by omega) ?_
        (by rw [show d + 6 + 6 * fuel = d + 6 * (fuel + 1) by omega]; exact hn)
      have h1 := step_fld w n d S _ hw (by omega) hS
      have h2 := step_fld w n (d + 2) _ _ hw (by omega) h1
      refine fld_congr (fun k _ => ?_) h2
      unfold Q
      constructor
      · rintro ⟨⟨⟨h2k, hall⟩, hd1⟩, hd2⟩
        refine ⟨h2k, fun e he => ?_⟩
        have : Cov d e ∨ e = d ∨ e = d + 2 := by unfold Cov at *; omega
        rcases this with h | rfl | rfl
        · exact hall e h
        · exact hd1
        · exact hd2
      · rintro ⟨h2k, hall⟩
        exact ⟨⟨⟨h2k, fun e he => hall e (by unfold Cov at *; omega)⟩,
          hall d (by unfold Cov; omega)⟩, hall (d + 2) (by unfold Cov; omega)⟩
    · show fld w n Nat.Prime S
      exact fld_congr (fun k hk => Q_prime n d k hk ((blt_iff _ _).mp hb)) hS

/-! ## Assembling -/

theorem init_fld (w n : Nat) (hw : 0 < w) :
    fld w n (fun k => 2 ≤ k) (pat w (n - 1) (Nat.sub (Nat.shiftLeft 1 w) 1) (2 * w)) := by
  intro i
  rw [testBit_pat _ _ _ _ hw]
  by_cases h0 : i % w = 0
  · obtain ⟨k, rfl⟩ : ∃ k, i = w * k := ⟨i / w, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h0)).symm⟩
    rw [Nat.mul_div_cancel_left k hw, Nat.mul_comm 2 w, ← Nat.mul_sub, Nat.mul_mod_right,
      Nat.mul_le_mul_left_iff hw, Nat.mul_lt_mul_left hw]
    omega
  · constructor
    · rintro ⟨h1, _, h3⟩
      exfalso; apply h0
      have := Nat.sub_mul_mod (x := i) (k := 2) (n := w) (by rw [Nat.mul_comm]; exact h1)
      rw [Nat.mul_comm w 2] at this
      omega
    · rintro ⟨h, _⟩; exact absurd h h0

theorem fld_pk (w n S : Nat) (hw : 0 < w) (hS : fld w n Nat.Prime S) :
    S = pk (2 ^ w) (fun k => if k.Prime then 1 else 0) (n + 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hf : ∀ u, u < n + 1 → (fun k => if k.Prime then 1 else 0) u < 2 ^ w := by
    intro u _
    have := Nat.one_lt_two_pow (show w ≠ 0 by omega)
    dsimp only; split <;> omega
  rw [testBit_pk w hw (n + 1) _ hf i, Bool.eq_iff_iff, hS i]
  have hlt : i < w * (n + 1) ↔ i / w ≤ n := by
    rw [Nat.mul_comm, ← Nat.div_lt_iff_lt_mul hw]; omega
  by_cases hp : (i / w).Prime
  · simp only [hp, if_true, Bool.and_eq_true, decide_eq_true_eq, testBit_one_iff, hlt, and_true]
    exact and_comm
  · simp [hp]

theorem width_spec (n : Nat) : 0 < width n ∧ n + 2 < 2 ^ width n := by
  unfold width
  cases h : Nat.blt n 1022
  · show 0 < Nat.log2 n + 2 ∧ n + 2 < 2 ^ (Nat.log2 n + 2)
    have hge : ¬ n < 1022 := fun h' => by rw [(blt_iff _ _).mpr h'] at h; contradiction
    have := Nat.lt_log2_self (n := n)
    rw [Nat.pow_succ]
    omega
  · show 0 < 10 ∧ n + 2 < 2 ^ 10
    have := (blt_iff _ _).mp h
    have h10 : (2 : Nat) ^ 10 = 1024 := rfl
    omega

theorem impl_correct : ∀ n, impl n = primeCountSpec n := by
  intro n
  obtain ⟨hw, hwn⟩ := width_spec n
  show Nat.mod (loop (width n) n n 5 (step (width n) n 3 (step (width n) n 2
    (pat (width n) (n - 1) (Nat.sub (Nat.shiftLeft 1 (width n)) 1) (2 * width n)))))
    (Nat.sub (Nat.shiftLeft 1 (width n)) 1) = _
  generalize width n = w at hw hwn
  have h0 := init_fld w n hw
  have h2 := step_fld w n 2 _ _ hw (by omega) h0
  have h3 := step_fld w n 3 _ _ hw (by omega) h2
  have hS := loop_fld w n hw n 5 _ (by omega) (by omega) (fld_congr (fun k _ => by
    unfold Q Cov
    constructor
    · rintro ⟨⟨h2k, hd2⟩, hd3⟩
      refine ⟨h2k, fun e he => ?_⟩
      rcases he with rfl | rfl | he
      · exact hd2
      · exact hd3
      · omega
    · rintro ⟨h2k, hall⟩
      exact ⟨⟨h2k, hall 2 (Or.inl rfl)⟩, hall 3 (Or.inr (Or.inl rfl))⟩) h3)
    (by
      have := Nat.le_mul_self (5 + 6 * n)
      omega)
  have hm : Nat.sub (Nat.shiftLeft 1 w) 1 = 2 ^ w - 1 := by
    show 1 <<< w - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [fld_pk w n _ hw hS, hm, show ∀ a b : Nat, Nat.mod a b = a % b from fun _ _ => rfl]
  have hmod := pk_modEq (2 ^ w) Nat.one_le_two_pow (n + 1) (fun k => if k.Prime then 1 else 0)
  have hle := sm_le (n + 1) (fun k => if k.Prime then 1 else 0) (fun i => by show (if Nat.Prime i then 1 else 0) ≤ 1; split <;> omega)
  unfold Nat.ModEq at hmod
  rw [hmod, Nat.mod_eq_of_lt (by omega), sm_count]
  rfl

end Submission
