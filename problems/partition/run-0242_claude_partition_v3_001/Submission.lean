import Spec

/-!
# Partitions by packed generating-function rows

A DP row `partAux k 0, …, partAux k n` is stored as one natural number: the
row's values are its digits in base `X = (n + 1) ^ n + 1`, which exceeds every
entry. Adding part size `p = k + 1` multiplies the row by `1 / (1 - X ^ p)`.
That is the truncated geometric sum `1 + X ^ p + … + X ^ (p * ⌊n / p⌋)`, taken
modulo `X ^ (n + 1)`. Each step is a few big-number multiplications and
reductions, which the kernel performs with GMP. The answer is digit `n`.
-/

namespace Submission

/-- `geo a J = a ^ 0 + a ^ 1 + … + a ^ J`. -/
def geo (a : Nat) : Nat → Nat
  | 0 => 1
  | J + 1 => geo a J + a ^ (J + 1)

/-- Digit base: larger than every `partAux k m` with `k, m ≤ n`. -/
def base (n : Nat) : Nat := (n + 1) ^ n + 1

/-- Packed row after allowing parts `1, …, k` (digits in base `X`, modulo `M`). -/
def rowv (n X M : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => (rowv n X M k * geo (X ^ (k + 1)) (n / (k + 1))) % M

/-! The computation itself uses `Nat.add`, `Nat.mul`, … directly (cheaper for the
kernel than going through the arithmetic type classes) and a Horner-form
geometric sum, with the loops written as `Nat.rec` (much cheaper for the kernel
than structural recursion). `hgeo_eq`, `rowF_eq` and `impl_eq` connect it to `geo` / `rowv`,
which the proofs use. -/

/-- Horner form of `geo`. -/
def hgeo (a J : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1 (fun _ acc => Nat.add 1 (Nat.mul a acc)) J

def rowF (n X M k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1
    (fun k acc => Nat.mod (Nat.mul acc
      (hgeo (Nat.pow X (Nat.add k 1)) (Nat.div n (Nat.add k 1)))) M) k

def baseF (n : Nat) : Nat := Nat.add (Nat.pow (Nat.add n 1) n) 1

def impl (n : Nat) : Nat :=
  Nat.mod (Nat.div (rowF n (baseF n) (Nat.pow (baseF n) (Nat.add n 1)) n)
    (Nat.pow (baseF n) n)) (baseF n)

theorem geo_succ' (a : Nat) : ∀ J, 1 + a * geo a J = geo a (J + 1)
  | 0 => by simp [geo]
  | J + 1 => by
    have ih := geo_succ' a J
    show 1 + a * (geo a J + a ^ (J + 1)) = geo a (J + 1) + a ^ (J + 1 + 1)
    rw [Nat.mul_add, ← Nat.add_assoc, ih, Nat.pow_succ a (J + 1), Nat.mul_comm a]

theorem hgeo_eq (a : Nat) : ∀ J, hgeo a J = geo a J
  | 0 => rfl
  | J + 1 => by
    show 1 + a * hgeo a J = _
    rw [hgeo_eq a J, geo_succ']

theorem rowF_eq (n X M : Nat) : ∀ k, rowF n X M k = rowv n X M k
  | 0 => rfl
  | k + 1 => by
    show (rowF n X M k * hgeo (X ^ (k + 1)) (n / (k + 1))) % M =
      (rowv n X M k * geo (X ^ (k + 1)) (n / (k + 1))) % M
    rw [rowF_eq n X M k, hgeo_eq]

theorem impl_eq (n : Nat) :
    impl n = rowv n (base n) (base n ^ (n + 1)) n / base n ^ n % base n := by
  show rowF n (base n) (base n ^ (n + 1)) n / base n ^ n % base n = _
  rw [rowF_eq]

/-! ## Packed digit strings -/

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

/-- Split off the first `a` digits. -/
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

/-- Shifting digits up by `p` places multiplies by `X ^ p`. -/
theorem pk_shift (X : Nat) (h : Nat → Nat) : ∀ (p L : Nat),
    pk X (fun i => if p ≤ i then h (i - p) else 0) (L + p) = X ^ p * pk X h L
  | 0, L => by simp
  | p + 1, L => by
    rw [show L + (p + 1) = (L + p) + 1 by omega]
    simp only [pk]
    have e : (fun i => if p + 1 ≤ i + 1 then h (i + 1 - (p + 1)) else 0) =
        (fun i => if p ≤ i then h (i - p) else 0) := by
      funext i
      by_cases hi : p ≤ i
      · rw [if_pos (by omega), if_pos hi, show i + 1 - (p + 1) = i - p by omega]
      · rw [if_neg (by omega), if_neg hi]
    rw [if_neg (by omega), e, pk_shift X h p L, Nat.pow_succ]
    rw [Nat.zero_add, ← Nat.mul_assoc, Nat.mul_comm X (X ^ p)]

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

/-! ## The DP recurrence for the specification -/

theorem foldl_add (l : List Nat) (a : Nat) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, List.sum_cons]; omega

theorem partAux_zero_succ (m : Nat) : partAux 0 (m + 1) = 0 := rfl

theorem partAux_succ (k i : Nat) :
    partAux (k + 1) i =
      partAux k i + (if k + 1 ≤ i then partAux (k + 1) (i - (k + 1)) else 0) := by
  have unfold_ : ∀ m, partAux (k + 1) m =
      ((List.range (m / (k + 1) + 1)).map (fun j => partAux k (m - j * (k + 1)))).sum := by
    intro m
    show ((List.range (m / (k + 1) + 1)).map
      (fun j => partAux k (m - j * (k + 1)))).foldl (· + ·) 0 = _
    rw [foldl_add, Nat.zero_add]
  by_cases hi : k + 1 ≤ i
  · rw [if_pos hi, unfold_ i, unfold_ (i - (k + 1)),
      Nat.div_eq_sub_div (Nat.succ_pos k) hi, List.range_succ_eq_map, List.map_cons,
      List.sum_cons, List.map_map, Nat.zero_mul, Nat.sub_zero]
    congr 2
    apply List.map_congr_left
    intro j _
    simp only [Function.comp, Nat.succ_mul]
    congr 1
    omega
  · rw [if_neg hi, unfold_ i, Nat.div_eq_of_lt (by omega)]
    simp

theorem partAux_le : ∀ k m, partAux k m ≤ (m + 1) ^ k
  | 0, 0 => by simp [partAux]
  | 0, m + 1 => by rw [partAux_zero_succ]; exact Nat.zero_le _
  | k + 1, m => by
    rw [partAux_succ]
    have hk := partAux_le k m
    have hpow : (m + 1) ^ (k + 1) = (m + 1) ^ k * m + (m + 1) ^ k := by
      rw [Nat.pow_succ, Nat.mul_add, Nat.mul_one]
    by_cases hi : k + 1 ≤ m
    · rw [if_pos hi]
      have hr := partAux_le (k + 1) (m - (k + 1))
      have h1 : (m - (k + 1) + 1) ^ (k + 1) ≤ m ^ (k + 1) :=
        Nat.pow_le_pow_left (by omega) _
      have h2 : m ^ k ≤ (m + 1) ^ k := Nat.pow_le_pow_left (by omega) _
      have h3 : m ^ k * m ≤ (m + 1) ^ k * m := Nat.mul_le_mul_right m h2
      have h4 : m ^ (k + 1) = m ^ k * m := Nat.pow_succ m k
      omega
    · rw [if_neg hi]
      have : (m + 1) ^ k ≤ (m + 1) ^ k * m + (m + 1) ^ k := by omega
      omega
termination_by k m => (k, m)
decreasing_by all_goals (first | omega | (apply Prod.Lex.left; omega) |
  (apply Prod.Lex.right; omega))

theorem partAux_lt_base (n k m : Nat) (hk : k ≤ n) (hm : m ≤ n) :
    partAux k m < base n := by
  have h1 := partAux_le k m
  have h2 : (m + 1) ^ k ≤ (n + 1) ^ k := Nat.pow_le_pow_left (by omega) _
  have h3 : (n + 1) ^ k ≤ (n + 1) ^ n := Nat.pow_le_pow_right (by omega) hk
  unfold base
  omega

/-! ## One DP step on packed rows -/

section Step

variable (X L p : Nat) (f g : Nat → Nat)

/-- If `g i = f i + g (i - p)` (the second term only when `p ≤ i`), then the
packed row of `g` is a fixed point of `G ↦ (P + X ^ p * G) mod X ^ L`. -/
theorem fixpoint (hp : p ≤ L) (hg : ∀ i, i < L → g i < X)
    (hrec : ∀ i, i < L → g i = f i + (if p ≤ i then g (i - p) else 0)) :
    (pk X f L + X ^ p * pk X g L) % X ^ L = pk X g L := by
  have hG : pk X g L = pk X f L + X ^ p * pk X g (L - p) := by
    rw [pk_congr X L g _ hrec, pk_add]
    congr 1
    have := pk_shift X g p (L - p)
    rwa [Nat.sub_add_cancel hp] at this
  have hsplit := pk_split X (L - p) p g
  rw [Nat.sub_add_cancel hp] at hsplit
  have hmul : X ^ p * pk X g L =
      X ^ p * pk X g (L - p) + X ^ L * pk X (fun i => g (i + (L - p))) p := by
    rw [hsplit, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' hp]
  rw [hmul, ← Nat.add_assoc, ← hG, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (pk_lt X L g hg)]

/-- Unrolling the fixed point `j + 1` times. -/
theorem unroll (P G M a : Nat) (hfix : (P + a * G) % M = G) :
    ∀ j, (P * geo a j + a ^ (j + 1) * G) % M = G
  | 0 => by simp [geo, hfix]
  | j + 1 => by
    have ih := unroll P G M a hfix j
    have hq : P + a * G = G + M * ((P + a * G) / M) := by
      have := Nat.div_add_mod (P + a * G) M
      rw [hfix] at this
      omega
    have e : a ^ (j + 1) * (P + a * G) = a ^ (j + 1) * (G + M * ((P + a * G) / M)) := by
      rw [← hq]
    have : P * geo a (j + 1) + a ^ (j + 1 + 1) * G =
        (P * geo a j + a ^ (j + 1) * G) + M * (a ^ (j + 1) * ((P + a * G) / M)) := by
      simp only [geo, Nat.pow_succ] at e ⊢
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] at e ⊢
      omega
    rw [this, Nat.add_mul_mod_self_left, ih]

theorem step (n k : Nat) (hk : k < n) (hg : ∀ i, i < n + 1 → g i < X)
    (hrec : ∀ i, i < n + 1 → g i = f i + (if k + 1 ≤ i then g (i - (k + 1)) else 0)) :
    (pk X f (n + 1) * geo (X ^ (k + 1)) (n / (k + 1))) % X ^ (n + 1) = pk X g (n + 1) := by
  have hfix := fixpoint X (n + 1) (k + 1) f g (by omega) hg hrec
  have hu := unroll (pk X f (n + 1)) (pk X g (n + 1)) (X ^ (n + 1)) (X ^ (k + 1)) hfix
    (n / (k + 1))
  -- `(X ^ (k + 1)) ^ (n / (k + 1) + 1)` is a multiple of `X ^ (n + 1)`.
  have hge : n + 1 ≤ (k + 1) * (n / (k + 1) + 1) := by
    have := Nat.lt_div_mul_add (a := n) (b := k + 1) (by omega)
    rw [Nat.mul_comm, Nat.add_mul, Nat.one_mul]
    omega
  have hpow : (X ^ (k + 1)) ^ (n / (k + 1) + 1) =
      X ^ (n + 1) * X ^ ((k + 1) * (n / (k + 1) + 1) - (n + 1)) := by
    rw [← Nat.pow_mul, ← Nat.pow_add, Nat.add_sub_cancel' hge]
  rw [hpow, Nat.mul_assoc, Nat.add_mul_mod_self_left] at hu
  exact hu

end Step

/-! ## Correctness -/

theorem rowv_eq (n : Nat) :
    ∀ k, k ≤ n → rowv n (base n) (base n ^ (n + 1)) k = pk (base n) (partAux k) (n + 1)
  | 0, _ => by
    simp only [rowv, pk]
    have : pk (base n) (fun i => partAux 0 (i + 1)) n = 0 := by
      rw [pk_congr (base n) n _ (fun _ => 0) (fun i _ => partAux_zero_succ i)]
      exact pk_zero_fun _ _
    rw [this]; rfl
  | k + 1, hk => by
    simp only [rowv]
    rw [rowv_eq n k (by omega)]
    exact step (base n) (partAux k) (partAux (k + 1)) n k (by omega)
      (fun i hi => partAux_lt_base n (k + 1) i hk (by omega))
      (fun i _ => partAux_succ k i)

theorem impl_correct : ∀ n, impl n = partitionSpec n := by
  intro n
  rw [impl_eq]
  unfold partitionSpec
  rw [rowv_eq n n (Nat.le_refl n)]
  exact pk_digit (base n) n (n + 1) (partAux n)
    (fun i hi => partAux_lt_base n n i (Nat.le_refl n) (by omega)) (by omega)

end Submission
