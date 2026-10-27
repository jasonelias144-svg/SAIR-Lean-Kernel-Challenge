import Spec

/-!
# Permanent by a packed subset DP

Let `d` be the dimension. For `i ≤ d` and a set `u` of already-used columns
(a `d`-bit mask), let `G_i[u] = permanentRows d (rows i … d-1) u`, the count the
spec's depth-first search returns. Then `G_d[u] = 1` and

  `G_i[u] = Σ_{j allowed in row i, j ∉ u} G_{i+1}[u + 2^j]`,

and the answer is `G_0[∅]`.

A whole vector `G_i` is stored as one natural number with `2^d` fields of `W`
bits (field `u` holds `G_i[u]`). `2^W` exceeds every entry, so fields never
overflow into each other. One DP row is then a few big-number operations per
allowed column `j`: shift the vector down by `2^j` fields, keep only the fields
whose mask has bit `j` clear (an AND with the selector `zm W j d`), and add.

Row `i`'s allowed columns are computed once per row (`i` and the two seeded
columns, or every column below dimension 3). Values used more than once
(the vector, the columns, the selectors) are forced to literals with
`forceN` / `forceL`, so the kernel evaluates them once. Loops are `Nat.rec`,
and word operations call `Nat.*` directly.
-/

namespace Submission

/-! ## Implementation -/

/-- Evaluate `x` before continuing (so it is computed once, not per use). -/
def forceN (x : Nat) (k : Nat → Nat) : Nat :=
  Nat.casesOn (motive := fun _ => Nat) x (k 0) (fun m => k (Nat.succ m))

def forceL (x : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.casesOn (motive := fun _ => List Nat) x (k 0) (fun m => k (Nat.succ m))

/-- Field width: `2 ^ fieldW d` exceeds `(d + 1) ^ d`, a bound on every entry. -/
def fieldW (d : Nat) : Nat := Nat.add (Nat.mul d (Nat.add (Nat.log2 d) 1)) 1

/-- Selector over `2^k` fields: field `u` is all ones iff bit `j` of `u` is clear. -/
def zm (W j k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.sub (Nat.shiftLeft 1 W) 1)
    (fun i acc => Nat.add acc
      (cond (Nat.beq i j) 0 (Nat.shiftLeft acc (Nat.mul W (Nat.shiftLeft 1 i))))) k

/-- `2^k` fields, each equal to 1. -/
def ones (W k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1
    (fun i acc => Nat.add acc (Nat.shiftLeft acc (Nat.mul W (Nat.shiftLeft 1 i)))) k

/-- The selectors `zm W (d - k) d, …, zm W (d - 1) d`, each forced once. -/
def zlistRec (W d k : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) []
    (fun m acc => forceL (zm W (Nat.sub (Nat.sub d 1) m) d) fun z => z :: acc) k

/-- The permanent mixer, word operations called directly. -/
def mix (x : Nat) : Nat :=
  let g1 (x : Nat) : Nat :=
    Nat.land (Nat.mul (Nat.xor x (Nat.shiftRight x 16)) 2146121005) 4294967295
  let g2 (x : Nat) : Nat :=
    Nat.land (Nat.mul (Nat.xor x (Nat.shiftRight x 15)) 2221713035) 4294967295
  let g3 (x : Nat) : Nat := Nat.land (Nat.xor x (Nat.shiftRight x 16)) 4294967295
  g3 (g2 (g1 x))

/-- The spec's `permanentColumnOne`. -/
def col1 (d s i : Nat) : Nat :=
  permanentSkipOne i
    (Nat.mod (mix (Nat.xor (Nat.xor s (Nat.mul i 2654435769)) 2246822507)) (Nat.sub d 1))

/-- The spec's `permanentColumnTwo`, given the first column `c1`. -/
def col2 (d s i c1 : Nat) : Nat :=
  permanentSkipTwo i c1
    (Nat.mod (mix (Nat.xor (Nat.xor s (Nat.mul i 2654435769)) 3266489909)) (Nat.sub d 2))

/-- One DP row: `Σ_{j < d, ok j} (V >>> W·2^j) &&& zs[j]`. -/
def rowStep (W : Nat) (zs : List Nat) (ok : Nat → Bool) (V d : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => cond (ok j)
      (Nat.add acc (Nat.land (Nat.shiftRight V (Nat.mul W (Nat.shiftLeft 1 j))) (zs.getD j 0)))
      acc) d

/-- Whether entry `(i, j)` is one, given row `i`'s two seeded columns. -/
def okAt (d i c1 c2 j : Nat) : Bool :=
  Nat.blt d 3 || Nat.beq j i || Nat.beq j c1 || Nat.beq j c2

/-- The vector after processing the last `k` rows, starting from `V`. -/
def rowsFrom (d s W : Nat) (zs : List Nat) (V k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) V
    (fun m acc => forceN acc fun acc =>
      forceN (col1 d s (Nat.sub (Nat.sub d 1) m)) fun c1 =>
      forceN (col2 d s (Nat.sub (Nat.sub d 1) m) c1) fun c2 =>
      rowStep W zs (okAt d (Nat.sub (Nat.sub d 1) m) c1 c2) acc d) k

def perm (d s : Nat) : Nat :=
  forceN (fieldW d) fun W =>
  (fun zs => Nat.land (rowsFrom d s W zs (ones W d) d) (Nat.sub (Nat.shiftLeft 1 W) 1))
    (zlistRec W d d)

def impl (n : Nat) : Nat := perm (Nat.shiftRight n 32) (Nat.land n 4294967295)

/-! ## Packed vectors -/

/-- `pk X f L = f 0 + f 1 * X + … + f (L - 1) * X ^ (L - 1)`. -/
def pk (X : Nat) : (Nat → Nat) → Nat → Nat
  | _, 0 => 0
  | f, L + 1 => f 0 + X * pk X (fun i => f (i + 1)) L

theorem pk_congr (X : Nat) : ∀ (L : Nat) (f g : Nat → Nat),
    (∀ i, i < L → f i = g i) → pk X f L = pk X g L
  | 0, _, _, _ => rfl
  | L + 1, f, g, h => by
    simp only [pk]
    rw [h 0 (by omega), pk_congr X L (fun i => f (i + 1)) (fun i => g (i + 1))
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

theorem pk_split (X : Nat) : ∀ (a b : Nat) (f : Nat → Nat),
    pk X f (a + b) = pk X f a + X ^ a * pk X (fun i => f (i + a)) b
  | 0, b, f => by simp [pk]
  | a + 1, b, f => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [pk]
    rw [pk_split X a b (fun i => f (i + 1))]
    have e : (fun i => f (i + a + 1)) = (fun i => f (i + (a + 1))) := by
      funext i; rw [Nat.add_assoc]
    rw [e, Nat.pow_succ, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm X (X ^ a)]
    omega

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

/-- Dividing by `X ^ s` drops the lowest `s` fields. -/
theorem pk_div (X : Nat) (hX : 0 < X) (s L : Nat) (hs : s ≤ L) (f : Nat → Nat)
    (hf : ∀ u, u < s → f u < X) :
    pk X f L / X ^ s = pk X (fun u => f (u + s)) (L - s) := by
  have h := pk_split X s (L - s) f
  rw [Nat.add_sub_cancel' hs] at h
  rw [h, Nat.add_mul_div_left _ _ (Nat.pow_pos hX),
    Nat.div_eq_of_lt (pk_lt X s f hf), Nat.zero_add]

/-- Extending with zero fields does not change the number. -/
theorem pk_pad (X : Nat) (g : Nat → Nat) (a b : Nat) :
    pk X g a = pk X (fun u => if u < a then g u else 0) (a + b) := by
  rw [pk_split, pk_congr X a (fun u => if u < a then g u else 0) g (fun u hu => by simp [hu])]
  rw [pk_congr X b (fun i => if i + a < a then g (i + a) else 0) (fun _ => 0)
    (fun i _ => by rw [if_neg (by omega)]), pk_zero_fun]
  simp

theorem pk_digit0 (X : Nat) (L : Nat) (f : Nat → Nat) (hL : 0 < L) (h0 : f 0 < X) :
    pk X f L % X = f 0 := by
  cases L with
  | zero => omega
  | succ L =>
    simp only [pk]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]

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

/-- AND with a selector keeps exactly the selected fields. -/
theorem pk_and_sel (W : Nat) (hW : 0 < W) (L : Nat) (f : Nat → Nat) (z : Nat → Bool)
    (hf : ∀ u, u < L → f u < 2 ^ W) :
    pk (2 ^ W) f L &&& pk (2 ^ W) (fun u => if z u then 2 ^ W - 1 else 0) L =
      pk (2 ^ W) (fun u => if z u then f u else 0) L := by
  have hpos : 0 < 2 ^ W := Nat.two_pow_pos W
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_pk W hW L f hf,
    testBit_pk W hW L _ (fun u _ => by split <;> omega),
    testBit_pk W hW L _ (fun u hu => by have := hf u hu; split <;> omega)]
  by_cases hi : i < W * L
  · have hr : i % W < W := Nat.mod_lt _ hW
    simp only [hi, decide_true, Bool.true_and]
    cases z (i / W)
    · simp
    · simp [Nat.testBit_two_pow_sub_one, hr]
  · simp [hi]

theorem land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl

/-! ## Selectors and the all-ones vector -/

theorem testBit_add_two_pow (u j k : Nat) (hu : u < 2 ^ k) :
    (u + 2 ^ k).testBit j = (decide (j = k) || u.testBit j) := by
  rw [Nat.add_comm]
  rcases Nat.lt_trichotomy j k with h | h | h
  · rw [Nat.testBit_two_pow_add_gt h]; simp [Nat.ne_of_lt h]
  · subst h; rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hu]; simp
  · have h1 : 2 ^ k + u < 2 ^ j := by
      have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show k + 1 ≤ j by omega)
      rw [Nat.pow_succ] at this
      omega
    have h2 : u < 2 ^ j :=
      Nat.lt_of_lt_of_le hu (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
    simp [Nat.ne_of_gt h]

theorem shiftLeft_fields (W V k : Nat) :
    Nat.shiftLeft V (Nat.mul W (Nat.shiftLeft 1 k)) = (2 ^ W) ^ (2 ^ k) * V := by
  show V <<< (W * (1 <<< k)) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, ← Nat.pow_mul, Nat.mul_comm]

theorem zm_eq (W j : Nat) : ∀ k,
    zm W j k = pk (2 ^ W) (fun u => if !u.testBit j then 2 ^ W - 1 else 0) (2 ^ k)
  | 0 => by
    show 1 <<< W - 1 = _
    simp [pk, Nat.shiftLeft_eq]
  | k + 1 => by
    show zm W j k + cond (Nat.beq k j) 0 (Nat.shiftLeft (zm W j k) (Nat.mul W (Nat.shiftLeft 1 k)))
      = _
    rw [shiftLeft_fields, zm_eq W j k, show 2 ^ (k + 1) = 2 ^ k + 2 ^ k by rw [Nat.pow_succ]; omega,
      pk_split]
    congr 1
    by_cases hkj : k = j
    · subst hkj
      rw [show Nat.beq k k = true by simp, cond_true,
        pk_congr _ _ _ (fun _ => 0) (fun u hu => by
          rw [testBit_add_two_pow u k k hu]; simp),
        pk_zero_fun, Nat.mul_zero]
    · rw [show Nat.beq k j = false by
        rw [Bool.eq_false_iff]; intro h; rw [Nat.beq_eq] at h; exact hkj h, cond_false]
      congr 1
      apply pk_congr
      intro u hu
      rw [testBit_add_two_pow u j k hu]
      simp [Ne.symm hkj]

theorem ones_eq (W : Nat) : ∀ k, ones W k = pk (2 ^ W) (fun _ => 1) (2 ^ k)
  | 0 => by show 1 = _; simp [pk]
  | k + 1 => by
    show ones W k + Nat.shiftLeft (ones W k) (Nat.mul W (Nat.shiftLeft 1 k)) = _
    rw [shiftLeft_fields, ones_eq W k,
      show 2 ^ (k + 1) = 2 ^ k + 2 ^ k by rw [Nat.pow_succ]; omega, pk_split]

theorem zlistRec_getD (W d : Nat) : ∀ k j, k ≤ d → j < k →
    (zlistRec W d k).getD j 0 = zm W (d - k + j) d
  | 0, _, _, hj => absurd hj (by omega)
  | k + 1, j, hk, hj => by
    show (forceL (zm W (d - 1 - k) d) fun z => z :: zlistRec W d k).getD j 0 = _
    have hf : ∀ (x : Nat) (g : Nat → List Nat), forceL x g = g x := by
      intro x g; cases x <;> rfl
    rw [hf]
    cases j with
    | zero => simp; congr 1; omega
    | succ j =>
      rw [List.getD_cons_succ, zlistRec_getD W d k j (by omega) (by omega)]
      congr 1; omega

/-! ## One DP row -/

theorem forceN_eq (x : Nat) (k : Nat → Nat) : forceN x k = k x := by
  cases x <;> rfl

/-- `Σ_{j < n} F j`. -/
def sumTo (F : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo F n + F n

theorem sumTo_congr (F G : Nat → Nat) : ∀ n, (∀ j, j < n → F j = G j) → sumTo F n = sumTo G n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [sumTo]
    rw [sumTo_congr F G n (fun j hj => h j (by omega)), h n (by omega)]

theorem sumTo_le (F : Nat → Nat) (B : Nat) : ∀ n, (∀ j, j < n → F j ≤ B) → sumTo F n ≤ n * B
  | 0, _ => by simp [sumTo]
  | n + 1, h => by
    simp only [sumTo]
    have := sumTo_le F B n (fun j hj => h j (by omega))
    have := h n (by omega)
    rw [Nat.succ_mul]
    omega

theorem pk_sumTo (X L : Nat) (F : Nat → Nat → Nat) : ∀ n,
    pk X (fun u => sumTo (F u) n) L = sumTo (fun j => pk X (fun u => F u j) L) n
  | 0 => by simp only [sumTo]; exact pk_zero_fun X L
  | n + 1 => by
    simp only [sumTo]
    rw [pk_add, pk_sumTo X L F n]

/-- If bit `j` of `u < 2^d` is clear then `u + 2^j < 2^d`. -/
theorem add_two_pow_lt (u j d : Nat) (hu : u < 2 ^ d) (hj : j < d) (hb : u.testBit j = false) :
    u + 2 ^ j < 2 ^ d := by
  have hlow : u % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
  have hsplit := Nat.div_add_mod u (2 ^ j)
  have hq : (u / 2 ^ j) % 2 = 0 := by
    have := Nat.testBit_div_two_pow (n := j) u 0
    rw [Nat.zero_add, hb, Nat.testBit_zero] at this
    simpa using this
  have hup : u / 2 ^ j < 2 ^ (d - j) := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    exact hu
  -- `u / 2^j` is even and below `2^(d-j)`, so `u / 2^j + 1 < 2^(d-j)`.
  have hev : u / 2 ^ j + 1 < 2 ^ (d - j) := by
    have h2 : 2 ∣ 2 ^ (d - j) := by
      exact Nat.dvd_of_mod_eq_zero (by
        rw [show d - j = (d - j - 1) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left])
    rcases h2 with ⟨c, hc⟩
    omega
  have : 2 ^ j * (u / 2 ^ j + 1) ≤ 2 ^ j * (2 ^ (d - j) - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' (by omega), Nat.mul_add,
    Nat.mul_one] at this
  omega

/-- One selected, shifted copy of the vector. -/
theorem sel_eq (W : Nat) (hW : 0 < W) (d j : Nat) (hj : j < d) (f : Nat → Nat)
    (hf : ∀ u, f u < 2 ^ W) :
    Nat.land (Nat.shiftRight (pk (2 ^ W) f (2 ^ d)) (Nat.mul W (Nat.shiftLeft 1 j))) (zm W j d) =
      pk (2 ^ W) (fun u => if !u.testBit j then f (u + 2 ^ j) else 0) (2 ^ d) := by
  have hXpos : 0 < 2 ^ W := Nat.two_pow_pos W
  have hjd : 2 ^ j ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) (by omega)
  have hsh : Nat.shiftRight (pk (2 ^ W) f (2 ^ d)) (Nat.mul W (Nat.shiftLeft 1 j)) =
      pk (2 ^ W) f (2 ^ d) / (2 ^ W) ^ (2 ^ j) := by
    show _ >>> (W * (1 <<< j)) = _
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_mul]
  rw [hsh, pk_div _ hXpos (2 ^ j) (2 ^ d) hjd f (fun u _ => hf u),
    pk_pad _ _ (2 ^ d - 2 ^ j) (2 ^ j), Nat.sub_add_cancel hjd, zm_eq]
  rw [land_eq, pk_and_sel W hW (2 ^ d) _ (fun u => !u.testBit j)
    (fun u _ => by split; exact hf _; exact Nat.two_pow_pos W)]
  apply pk_congr
  intro u hu
  cases hb : u.testBit j
  · have := add_two_pow_lt u j d hu hj hb
    simp [show u < 2 ^ d - 2 ^ j by omega]
  · simp

theorem rowStep_eq (W : Nat) (hW : 0 < W) (zs : List Nat) (ok : Nat → Bool) (d : Nat)
    (hzs : ∀ j, j < d → zs.getD j 0 = zm W j d) (f : Nat → Nat) (hf : ∀ u, f u < 2 ^ W) :
    rowStep W zs ok (pk (2 ^ W) f (2 ^ d)) d =
      pk (2 ^ W) (fun u => sumTo (fun j => if ok j && !u.testBit j then f (u + 2 ^ j) else 0) d)
        (2 ^ d) := by
  rw [pk_sumTo]
  -- partial sums over the first `m` columns
  have key : ∀ m, m ≤ d →
      Nat.rec (motive := fun _ => Nat) 0
        (fun j acc => cond (ok j)
          (Nat.add acc (Nat.land (Nat.shiftRight (pk (2 ^ W) f (2 ^ d))
            (Nat.mul W (Nat.shiftLeft 1 j))) (zs.getD j 0))) acc) m =
      sumTo (fun j => pk (2 ^ W) (fun u => if ok j && !u.testBit j then f (u + 2 ^ j) else 0)
        (2 ^ d)) m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      show cond (ok m) (Nat.add _ _) _ = sumTo _ m + _
      rw [ih (by omega)]
      cases hok : ok m
      · simp only [cond_false]
        rw [pk_congr _ _ _ (fun _ => 0) (fun u _ => by simp [hok]), pk_zero_fun, Nat.add_zero]
      · simp only [cond_true]
        rw [hzs m (by omega), sel_eq W hW d m (by omega) f hf]
        rw [show ∀ a b : Nat, Nat.add a b = a + b from fun _ _ => rfl]
        congr 1
        apply pk_congr
        intro u _
        simp [hok]
  exact key d (Nat.le_refl d)

/-! ## The spec as a sum -/

theorem foldl_range_sum (c : Nat → Bool) (t : Nat → Nat) : ∀ (w a : Nat),
    (List.range w).foldl (fun total j => if c j = true then total else total + t j) a =
      a + sumTo (fun j => if c j = true then 0 else t j) w
  | 0, a => by simp [sumTo]
  | w + 1, a => by
    rw [List.range_succ, List.foldl_append, foldl_range_sum c t w a]
    simp only [List.foldl_cons, List.foldl_nil, sumTo]
    split <;> omega

theorem permanentRows_cons (w : Nat) (row : List Nat) (rows : List (List Nat)) (u : Nat) :
    permanentRows w (row :: rows) u =
      sumTo (fun j => if (decide (row.getD j 0 = 0) || u.testBit j) = true then 0
        else row.getD j 0 * permanentRows w rows (u ||| 1 <<< j)) w := by
  simp only [permanentRows]
  rw [foldl_range_sum (fun j => (decide (row.getD j 0 = 0) || u.testBit j))
    (fun j => row.getD j 0 * permanentRows w rows (u ||| 1 <<< j)) w 0, Nat.zero_add]

theorem getD_row (d s i j : Nat) :
    (genPermanentRow d s i).getD j 0 = if j < d then permanentEntry d s i j else 0 := by
  unfold genPermanentRow
  rw [List.getD_eq_getElem?_getD]
  by_cases h : j < d
  · simp [h]
  · simp [h]

theorem entry_eq (d s i j : Nat) :
    permanentEntry d s i j =
      if okAt d i (permanentColumnOne d s i) (permanentColumnTwo d s i) j then 1 else 0 := by
  unfold permanentEntry okAt
  by_cases h : d < 3
  · simp [h, Nat.blt_eq]
  · have : Nat.blt d 3 = false := by
      rw [Bool.eq_false_iff]; intro hb; rw [Nat.blt_eq] at hb; exact h hb
    simp only [h, if_false, this, Bool.false_or]
    by_cases h1 : j = i
    · subst h1; simp
    · by_cases h2 : j = permanentColumnOne d s i
      · simp [h2]
      · by_cases h3 : j = permanentColumnTwo d s i
        · simp [h3]
        · simp [h1, h2, h3, Ne.symm h1]

theorem getD_row_le (d s i j : Nat) : (genPermanentRow d s i).getD j 0 ≤ 1 := by
  rw [getD_row, entry_eq]
  split <;> (try split) <;> omega

theorem permanentRows_le (w : Nat) : ∀ (rows : List (List Nat)) (u : Nat),
    (∀ row, row ∈ rows → ∀ j, row.getD j 0 ≤ 1) → permanentRows w rows u ≤ w ^ rows.length
  | [], _, _ => by simp [permanentRows]
  | row :: rows, u, h => by
    rw [permanentRows_cons, List.length_cons, Nat.pow_succ, Nat.mul_comm]
    apply sumTo_le
    intro j _
    split
    · exact Nat.zero_le _
    · have h1 := h row (by simp) j
      have h2 := permanentRows_le w rows (u ||| 1 <<< j)
        (fun r hr => h r (List.mem_cons_of_mem _ hr))
      calc row.getD j 0 * permanentRows w rows (u ||| 1 <<< j)
          ≤ 1 * w ^ rows.length := Nat.mul_le_mul h1 h2
        _ = w ^ rows.length := Nat.one_mul _

/-- Setting a clear bit is adding its power of two. -/
theorem or_two_pow_of_clear (u j : Nat) (hb : u.testBit j = false) : u ||| 1 <<< j = u + 2 ^ j := by
  have hpos : 0 < 2 ^ (j + 1) := Nat.two_pow_pos _
  have hsplit := Nat.div_add_mod u (2 ^ (j + 1))
  generalize hq : u / 2 ^ (j + 1) = q at hsplit
  generalize hr : u % 2 ^ (j + 1) = r at hsplit
  have hr1 : r < 2 ^ (j + 1) := hr ▸ Nat.mod_lt _ hpos
  have hrb : r.testBit j = false := by
    rw [← hr, Nat.testBit_mod_two_pow]; simp [hb]
  have hr2 : r < 2 ^ j := by
    rcases Nat.lt_or_ge r (2 ^ j) with hcon | hcon
    · exact hcon
    exfalso
    have : r = 2 ^ j + (r - 2 ^ j) := by omega
    have hlt : r - 2 ^ j < 2 ^ j := by rw [Nat.pow_succ] at hr1; omega
    rw [this, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt] at hrb
    simp at hrb
  have hlt' : 2 ^ j + r < 2 ^ (j + 1) := by rw [Nat.pow_succ]; omega
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, ← hsplit,
    show 2 ^ (j + 1) * q + r + 2 ^ j = 2 ^ (j + 1) * q + (2 ^ j + r) by omega,
    Nat.testBit_two_pow_mul_add _ hr1, Nat.testBit_two_pow_mul_add _ hlt']
  by_cases ht : t < j + 1
  · rw [if_pos ht, if_pos ht]
    by_cases htj : t = j
    · subst htj; rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr2]; simp
    · rw [Nat.testBit_two_pow_add_gt (by omega)]; simp [Ne.symm htj]
  · rw [if_neg ht, if_neg ht]; simp; omega

/-! ## The rows, from the end -/

/-- Rows `i, i + 1, …, d - 1` of the matrix. -/
def rowsFromI (d s i : Nat) : List (List Nat) :=
  (List.range' i (d - i)).map (genPermanentRow d s)

theorem rowsFromI_succ (d s i : Nat) (hi : i < d) :
    rowsFromI d s i = genPermanentRow d s i :: rowsFromI d s (i + 1) := by
  unfold rowsFromI
  rw [show d - i = (d - (i + 1)) + 1 by omega, List.range'_succ]
  rfl

theorem rowsFromI_length (d s i : Nat) : (rowsFromI d s i).length = d - i := by
  simp [rowsFromI]

theorem rowsFromI_le (d s i u : Nat) :
    permanentRows d (rowsFromI d s i) u < 2 ^ fieldW d := by
  have h := permanentRows_le d (rowsFromI d s i) u (by
    intro row hrow j
    simp only [rowsFromI, List.mem_map] at hrow
    obtain ⟨k, _, rfl⟩ := hrow
    exact getD_row_le d s k j)
  rw [rowsFromI_length] at h
  have h1 : d ^ (d - i) ≤ (d + 1) ^ d :=
    Nat.le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_right (by omega) (by omega))
  have h2 : (d + 1) ^ d ≤ (2 ^ (Nat.log2 d + 1)) ^ d :=
    Nat.pow_le_pow_left (Nat.lt_log2_self) _
  have h3 : (2 ^ (Nat.log2 d + 1)) ^ d < 2 ^ fieldW d := by
    rw [← Nat.pow_mul]
    apply Nat.pow_lt_pow_right (by omega)
    show (Nat.log2 d + 1) * d < d * (Nat.log2 d + 1) + 1
    rw [Nat.mul_comm]; omega
  omega

theorem rowsFrom_eq (d s W : Nat) (hW : W = fieldW d) (zs : List Nat)
    (hzs : ∀ j, j < d → zs.getD j 0 = zm W j d) : ∀ k, k ≤ d →
    rowsFrom d s W zs (ones W d) k =
      pk (2 ^ W) (fun u => permanentRows d (rowsFromI d s (d - k)) u) (2 ^ d)
  | 0, _ => by
    show ones W d = _
    rw [ones_eq]
    apply pk_congr
    intro u _
    simp [rowsFromI, permanentRows]
  | k + 1, hk => by
    have hWpos : 0 < W := by rw [hW]; unfold fieldW; show 0 < _ + 1; omega
    show forceN (rowsFrom d s W zs (ones W d) k) (fun acc =>
      forceN (col1 d s (d - 1 - k)) fun c1 =>
      forceN (col2 d s (d - 1 - k) c1) fun c2 =>
      rowStep W zs (okAt d (d - 1 - k) c1 c2) acc d) = _
    rw [forceN_eq, forceN_eq, forceN_eq, rowsFrom_eq d s W hW zs hzs k (by omega),
      rowStep_eq W hWpos zs _ d hzs _ (fun u => hW ▸ rowsFromI_le d s (d - k) u)]
    apply pk_congr
    intro u _
    rw [show d - (k + 1) = d - 1 - k by omega, rowsFromI_succ d s (d - 1 - k) (by omega),
      permanentRows_cons, show d - 1 - k + 1 = d - k by omega]
    apply sumTo_congr
    intro j hj
    rw [getD_row, if_pos hj, entry_eq]
    have hc1 : col1 d s (d - 1 - k) = permanentColumnOne d s (d - 1 - k) := rfl
    have hc2 : col2 d s (d - 1 - k) (permanentColumnOne d s (d - 1 - k)) =
        permanentColumnTwo d s (d - 1 - k) := rfl
    rw [hc1, hc2]
    cases hok : okAt d (d - 1 - k) (permanentColumnOne d s (d - 1 - k))
        (permanentColumnTwo d s (d - 1 - k)) j
    · simp
    · cases hb : u.testBit j
      · simp [or_two_pow_of_clear u j hb]
      · simp

/-! ## Correctness -/

theorem perm_correct (d s : Nat) :
    perm d s = permanentRows d (genPermanentMatrix d s) 0 := by
  unfold perm
  rw [forceN_eq]
  show Nat.land (rowsFrom d s (fieldW d) (zlistRec (fieldW d) d d) (ones (fieldW d) d) d)
    (Nat.sub (Nat.shiftLeft 1 (fieldW d)) 1) = _
  have hzs : ∀ j, j < d → (zlistRec (fieldW d) d d).getD j 0 = zm (fieldW d) j d := by
    intro j hj
    rw [zlistRec_getD (fieldW d) d d j (Nat.le_refl d) hj, Nat.sub_self, Nat.zero_add]
  rw [rowsFrom_eq d s (fieldW d) rfl _ hzs d (Nat.le_refl d), Nat.sub_self, land_eq,
    show Nat.sub (Nat.shiftLeft 1 (fieldW d)) 1 = 2 ^ fieldW d - 1 by
      show 1 <<< fieldW d - 1 = _
      rw [Nat.shiftLeft_eq, Nat.one_mul],
    Nat.and_two_pow_sub_one_eq_mod,
    pk_digit0 _ _ _ (Nat.two_pow_pos d) (rowsFromI_le d s 0 0)]
  unfold rowsFromI genPermanentMatrix
  rw [List.range_eq_range', Nat.sub_zero]

theorem impl_correct : ∀ n, impl n = permanentSpecN n := by
  intro n
  show perm (n >>> 32) (n &&& 4294967295) = _
  rw [perm_correct]
  unfold permanentSpecN permanentSpec permanentDimension permanentSeed
  simp [genPermanentMatrix]

end Submission
